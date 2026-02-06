"""Multicast test for tiny-switch.

Tests the STORE_MC command which:
1. Node sends STORE_MC command with data to a multicast address
2. Switch writes the data to all nodes in the multicast group
3. Switch returns ACK to the requesting node
"""

import cocotb

from .helpers import (
    setup, send_command,
    run_and_expect_ack, log_test_header,
    float_to_bf16, format_bf16, bf16_approx_equal,
    SwitchMetrics, logger,
    CMD_STORE_MC,
    ADDR_GROUP_ALL, ADDR_GROUP_23, NUM_NODES,
)


@cocotb.test()
async def test_multicast(dut):
    """Test multicast write to all 4 nodes."""
    
    log_test_header("Multicast write to all nodes")
    
    # Initial data (zeros in all nodes)
    initial_data = [[float_to_bf16(0.0)] for _ in range(NUM_NODES)]
    base_addr = ADDR_GROUP_ALL
    broadcast_value = float_to_bf16(42.0)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=base_addr)
    
    logger.info("Initial memory state (all zeros):")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, base_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Send STORE_MC command from Node 0
    logger.info(f"Node 0: Sending STORE_MC to address {base_addr:#x} with value {format_bf16(broadcast_value)}")
    await send_command(dut, port=0, cmd=CMD_STORE_MC, addr=base_addr, data=broadcast_value, metrics=metrics)
    
    cycles = await run_and_expect_ack(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify all nodes received the broadcast value
    logger.info("Final memory state (should all be 42.0):")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, base_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
        assert bf16_approx_equal(val, broadcast_value), \
            f"Node {i} has wrong value: expected {format_bf16(broadcast_value)}, got {format_bf16(val)}"
    
    logger.info("TEST PASSED: Multicast write to all nodes successful!")


@cocotb.test()
async def test_multicast_subset(dut):
    """Test multicast write to a subset of nodes (group 2: nodes 2,3 only)."""
    
    log_test_header("Multicast write to node subset (2,3)")
    
    # Initial data (different values to distinguish)
    initial_data = [
        [float_to_bf16(1.0)],   # Node 0
        [float_to_bf16(2.0)],   # Node 1
        [float_to_bf16(3.0)],   # Node 2
        [float_to_bf16(4.0)],   # Node 3
    ]
    
    base_addr = ADDR_GROUP_23
    broadcast_value = float_to_bf16(99.0)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=base_addr)
    
    logger.info("Initial memory state:")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, base_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Send STORE_MC from Node 0
    logger.info(f"Node 0: Sending STORE_MC to group 2 address {base_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_STORE_MC, addr=base_addr, data=broadcast_value, metrics=metrics)
    
    cycles = await run_and_expect_ack(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Check memory: nodes 0,1 should be unchanged, nodes 2,3 should have new value
    logger.info("Final memory state:")
    original_values = [float_to_bf16(float(i + 1)) for i in range(NUM_NODES)]
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, base_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
        
        if i < 2:
            # Nodes 0,1 should be unchanged
            assert bf16_approx_equal(val, original_values[i]), \
                f"Node {i} was modified but shouldn't be: expected {format_bf16(original_values[i])}, got {format_bf16(val)}"
        else:
            # Nodes 2,3 should have the broadcast value
            assert bf16_approx_equal(val, broadcast_value), \
                f"Node {i} should have {format_bf16(broadcast_value)}, got {format_bf16(val)}"
    
    logger.info("TEST PASSED: Subset multicast write successful!")


@cocotb.test()
async def test_multicast_from_different_port(dut):
    """Test multicast from a non-zero port."""
    
    log_test_header("Multicast from Port 2")
    
    initial_data = [[float_to_bf16(0.0)] for _ in range(NUM_NODES)]
    base_addr = ADDR_GROUP_ALL
    broadcast_value = float_to_bf16(77.0)
    
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=base_addr)
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Send from Port 2 instead of Port 0
    logger.info(f"Node 2: Sending STORE_MC")
    await send_command(dut, port=2, cmd=CMD_STORE_MC, addr=base_addr, data=broadcast_value, metrics=metrics)
    
    cycles = await run_and_expect_ack(dut, mem_ctrl, metrics, port=2)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # All nodes should have 77.0
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, base_addr)
        assert bf16_approx_equal(val, broadcast_value), \
            f"Node {i} has wrong value: expected {format_bf16(broadcast_value)}, got {format_bf16(val)}"
    
    logger.info("TEST PASSED: Multicast from Port 2 successful!")
