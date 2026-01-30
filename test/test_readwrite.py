"""Read/Write passthrough test for tiny-switch.

Tests the CMD_READ and CMD_WRITE commands which:
- READ: Read from a specific node's memory, return data to requester
- WRITE: Write to a specific node's memory, return ACK to requester
"""

import cocotb
from cocotb.triggers import RisingEdge

from .helpers.setup import setup, send_command, wait_response, get_signal_slice, DATA_WIDTH, RESP_TYPE_WIDTH
from .helpers.node_memory import NodeMemoryController
from .helpers.bf16 import float_to_bf16, bf16_to_float, format_bf16
from .helpers.format import format_cycle
from .helpers.logger import logger
from .helpers.metrics import SwitchMetrics
from .helpers.config import config


# Command types
CMD_READ = 3
CMD_WRITE = 4

# Response types
RESP_DATA = 0
RESP_ACK = 1


async def run_until_response(dut, mem_ctrl, metrics, port, max_cycles=None):
    """Run simulation until response is received on the given port.
    
    Args:
        dut: Device under test
        mem_ctrl: Memory controller
        metrics: Metrics tracker
        port: Port to watch for response
        max_cycles: Maximum cycles to wait (uses config default if None)
        
    Returns:
        Tuple of (cycles, response) where response is (type, data) or None
    """
    if max_cycles is None:
        max_cycles = config.max_cycles
    
    cycles = 0
    response = None
    
    while cycles < max_cycles:
        await mem_ctrl.run()
        await cocotb.triggers.ReadOnly()
        metrics.update()
        format_cycle(dut, cycles)
        
        try:
            # Use flattened array access for response signals
            resp_valid = dut.node_resp_valid.value.to_unsigned()
            if (resp_valid >> port) & 1:
                resp_type = get_signal_slice(dut.node_resp_type, port, RESP_TYPE_WIDTH)
                resp_data = get_signal_slice(dut.node_resp_data, port, DATA_WIDTH)
                response = (resp_type, resp_data)
                break
        except ValueError:
            pass
            
        await RisingEdge(dut.clk)
        cycles += 1
    
    return cycles, response


@cocotb.test()
async def test_read(dut):
    """Test simple read from a node."""
    
    logger.info("=" * 60)
    logger.info("TEST: Simple READ command")
    logger.info("=" * 60)
    
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
    for i in range(4):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: addr={test_addr:#x} value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=4)
    
    # Test reading from Node 0
    logger.info(f"Node 0: Sending READ to address {test_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_READ, addr=test_addr, metrics=metrics)
    
    cycles, response = await run_until_response(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify response
    assert response is not None, f"No response received within timeout"
    resp_type, resp_data = response
    
    assert resp_type == RESP_DATA, f"Expected DATA response (0), got {resp_type}"
    
    expected_value = test_values[0]
    logger.info(f"Expected: {format_bf16(expected_value)}, Got: {format_bf16(resp_data)}")
    
    assert resp_data == expected_value, \
        f"Data mismatch: expected {expected_value:#x}, got {resp_data:#x}"
    
    logger.info("TEST PASSED: READ command successful!")


@cocotb.test()
async def test_write(dut):
    """Test simple write to a node."""
    
    logger.info("=" * 60)
    logger.info("TEST: Simple WRITE command")
    logger.info("=" * 60)
    
    # Initialize with zeros
    initial_data = [[float_to_bf16(0.0)] for _ in range(4)]
    
    # Use a non-multicast address for passthrough
    test_addr = 0x00001000
    
    # Value to write
    write_value = float_to_bf16(99.5)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=test_addr)
    
    logger.info("Initial memory state (all zeros):")
    for i in range(4):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=4)
    
    # Send WRITE command from Node 0
    logger.info(f"Node 0: Sending WRITE to address {test_addr:#x} with value {format_bf16(write_value)}")
    await send_command(dut, port=0, cmd=CMD_WRITE, addr=test_addr, data=write_value, metrics=metrics)
    
    cycles, response = await run_until_response(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify ACK received
    assert response is not None, f"No response received within timeout"
    resp_type, _ = response
    
    assert resp_type == RESP_ACK, f"Expected ACK response (1), got {resp_type}"
    
    # Verify memory was written (only Node 0 should have the value)
    logger.info("Final memory state:")
    for i in range(4):
        val = mem_ctrl.read(i, test_addr)
        val_float = bf16_to_float(val)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
        
        if i == 0:
            # Node 0 should have the written value
            assert abs(val_float - 99.5) < 0.1, \
                f"Node 0 has wrong value: expected 99.5, got {val_float}"
        else:
            # Other nodes should still be zero
            assert abs(val_float - 0.0) < 0.1, \
                f"Node {i} should be 0.0, got {val_float}"
    
    logger.info("TEST PASSED: WRITE command successful!")


@cocotb.test()
async def test_read_after_write(dut):
    """Test reading back a value after writing it."""
    
    logger.info("=" * 60)
    logger.info("TEST: Read after Write")
    logger.info("=" * 60)
    
    # Initialize with zeros
    initial_data = [[float_to_bf16(0.0)] for _ in range(4)]
    
    test_addr = 0x00002000
    write_value = float_to_bf16(123.0)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=test_addr)
    metrics = SwitchMetrics(dut, num_ports=4)
    
    # Step 1: Write value
    logger.info(f"Step 1: Writing {bf16_to_float(write_value)} to Node 0 at {test_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_WRITE, addr=test_addr, data=write_value, metrics=metrics)
    
    cycles, response = await run_until_response(dut, mem_ctrl, metrics, port=0)
    assert response is not None and response[0] == RESP_ACK, "Write failed"
    logger.info(f"Write completed in {cycles} cycles with ACK")
    
    # Wait a few cycles before next command
    for _ in range(5):
        await RisingEdge(dut.clk)
    
    # Step 2: Read it back
    logger.info(f"Step 2: Reading back from Node 0 at {test_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_READ, addr=test_addr, metrics=metrics)
    
    cycles, response = await run_until_response(dut, mem_ctrl, metrics, port=0)
    
    assert response is not None, "No read response"
    resp_type, resp_data = response
    
    assert resp_type == RESP_DATA, f"Expected DATA response, got {resp_type}"
    
    read_value = bf16_to_float(resp_data)
    expected_value = bf16_to_float(write_value)
    
    logger.info(f"Read back: {read_value} (expected {expected_value})")
    
    assert abs(read_value - expected_value) < 0.1, \
        f"Read value mismatch: expected {expected_value}, got {read_value}"
    
    metrics.log_report()
    logger.info("TEST PASSED: Read after Write successful!")


@cocotb.test()
async def test_multiple_ports_read(dut):
    """Test reads from different ports."""
    
    logger.info("=" * 60)
    logger.info("TEST: Multiple ports READ")
    logger.info("=" * 60)
    
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
    metrics = SwitchMetrics(dut, num_ports=4)
    
    logger.info("Memory contents:")
    for i in range(4):
        val = mem_ctrl.read(i, test_addr)
        logger.info(f"  Node {i}: {format_bf16(val)}")
    
    # Test read from each port sequentially
    for port in range(4):
        logger.info(f"--- Testing READ from port {port} ---")
        await send_command(dut, port=port, cmd=CMD_READ, addr=test_addr, metrics=metrics)
        
        cycles, response = await run_until_response(dut, mem_ctrl, metrics, port=port)
        
        assert response is not None, f"Port {port}: No response"
        resp_type, resp_data = response
        
        assert resp_type == RESP_DATA, f"Port {port}: Expected DATA, got {resp_type}"
        
        expected = test_values[port]
        logger.info(f"Port {port}: Got {format_bf16(resp_data)}, expected {format_bf16(expected)}")
        
        assert resp_data == expected, \
            f"Port {port}: Data mismatch - expected {expected:#x}, got {resp_data:#x}"
        
        # Wait between commands
        for _ in range(5):
            await RisingEdge(dut.clk)
    
    metrics.log_report()
    logger.info("TEST PASSED: All ports read correctly!")
