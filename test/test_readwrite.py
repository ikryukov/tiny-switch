"""Read/Write passthrough test for tiny-switch.

Tests the CMD_READ and CMD_WRITE commands which:
- READ: Read from a specific node's memory, return data to requester
- WRITE: Write to a specific node's memory, return ACK to requester
"""

import cocotb
from cocotb.triggers import RisingEdge

from .helpers import (
    setup, send_command,
    run_and_expect_data, run_and_expect_ack, log_test_header,
    float_to_bf16, format_bf16, bf16_approx_equal,
    SwitchMetrics, logger,
    CMD_READ, CMD_WRITE, NUM_NODES,
)


@cocotb.test()
async def test_read(dut):
    """Test simple read from a node."""
    
    log_test_header("Simple READ command")
    
    # Initialize each node with different data
    test_values = [
        float_to_bf16(1.0),   # Node 0
        float_to_bf16(2.0),   # Node 1
        float_to_bf16(3.0),   # Node 2
        float_to_bf16(4.0),   # Node 3
    ]
    node_data = [[val] for val in test_values]
    
    # Use a non-multicast address for passthrough
    test_addr = 0x00001000
    
    # Setup
    mem_ctrl = await setup(dut, node_data=node_data, base_addr=test_addr)
    
    logger.info("Initial memory state:")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: addr={test_addr:#x} value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Test reading from Node 0
    logger.info(f"Node 0: Sending READ to address {test_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_READ, addr=test_addr, metrics=metrics)
    
    cycles, resp_data = await run_and_expect_data(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify response (bit-exact for passthrough, no arithmetic involved)
    expected_value = test_values[0]
    logger.info(f"Expected: {format_bf16(expected_value)}, Got: {format_bf16(resp_data)}")
    
    assert resp_data == expected_value, \
        f"Data mismatch: expected {format_bf16(expected_value)}, got {format_bf16(resp_data)}"
    
    logger.info("TEST PASSED: READ command successful!")


@cocotb.test()
async def test_write(dut):
    """Test simple write to a node."""
    
    log_test_header("Simple WRITE command")
    
    # Initialize with zeros
    initial_data = [[float_to_bf16(0.0)] for _ in range(NUM_NODES)]
    
    # Use a non-multicast address for passthrough
    test_addr = 0x00001000
    
    # Value to write
    write_value = float_to_bf16(99.5)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=test_addr)
    
    logger.info("Initial memory state (all zeros):")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Send WRITE command from Node 0
    logger.info(f"Node 0: Sending WRITE to address {test_addr:#x} with value {format_bf16(write_value)}")
    await send_command(dut, port=0, cmd=CMD_WRITE, addr=test_addr, data=write_value, metrics=metrics)
    
    cycles = await run_and_expect_ack(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify memory was written (only Node 0 should have the value)
    logger.info("Final memory state:")
    zero_bf16 = float_to_bf16(0.0)
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
        
        if i == 0:
            # Node 0 should have the written value
            assert bf16_approx_equal(val, write_value), \
                f"Node 0 has wrong value: expected {format_bf16(write_value)}, got {format_bf16(val)}"
        else:
            # Other nodes should still be zero
            assert bf16_approx_equal(val, zero_bf16), \
                f"Node {i} should be zero, got {format_bf16(val)}"
    
    logger.info("TEST PASSED: WRITE command successful!")


@cocotb.test()
async def test_read_after_write(dut):
    """Test reading back a value after writing it."""
    
    log_test_header("Read after Write")
    
    # Initialize with zeros
    initial_data = [[float_to_bf16(0.0)] for _ in range(NUM_NODES)]
    
    test_addr = 0x00002000
    write_value = float_to_bf16(123.0)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=test_addr)
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Step 1: Write value
    logger.info(f"Step 1: Writing {format_bf16(write_value)} to Node 0 at {test_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_WRITE, addr=test_addr, data=write_value, metrics=metrics)
    
    cycles = await run_and_expect_ack(dut, mem_ctrl, metrics, port=0)
    logger.info(f"Write completed in {cycles} cycles with ACK")
    
    # Wait a few cycles before next command
    for _ in range(5):
        await RisingEdge(dut.clk)
    
    # Step 2: Read it back
    logger.info(f"Step 2: Reading back from Node 0 at {test_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_READ, addr=test_addr, metrics=metrics)
    
    cycles, resp_data = await run_and_expect_data(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Read back: {format_bf16(resp_data)} (expected {format_bf16(write_value)})")
    
    assert bf16_approx_equal(resp_data, write_value), \
        f"Read value mismatch: expected {format_bf16(write_value)}, got {format_bf16(resp_data)}"
    
    metrics.log_report()
    logger.info("TEST PASSED: Read after Write successful!")


@cocotb.test()
async def test_multiple_ports_read(dut):
    """Test reads from different ports."""
    
    log_test_header("Multiple ports READ")
    
    # Each node has unique data
    test_values = [
        float_to_bf16(10.0),  # Node 0
        float_to_bf16(20.0),  # Node 1
        float_to_bf16(30.0),  # Node 2
        float_to_bf16(40.0),  # Node 3
    ]
    node_data = [[val] for val in test_values]
    test_addr = 0x00003000
    
    # Setup
    mem_ctrl = await setup(dut, node_data=node_data, base_addr=test_addr)
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    logger.info("Memory contents:")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: {format_bf16(val)}")
    
    # Test read from each port sequentially
    for port in range(NUM_NODES):
        logger.info(f"--- Testing READ from port {port} ---")
        await send_command(dut, port=port, cmd=CMD_READ, addr=test_addr, metrics=metrics)
        
        cycles, resp_data = await run_and_expect_data(dut, mem_ctrl, metrics, port=port)
        
        # Bit-exact for passthrough (no arithmetic involved)
        expected = test_values[port]
        logger.info(f"Port {port}: Got {format_bf16(resp_data)}, expected {format_bf16(expected)}")
        
        assert resp_data == expected, \
            f"Port {port}: Data mismatch - expected {format_bf16(expected)}, got {format_bf16(resp_data)}"
        
        # Wait between commands
        for _ in range(5):
            await RisingEdge(dut.clk)
    
    metrics.log_report()
    logger.info("TEST PASSED: All ports read correctly!")
