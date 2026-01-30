"""Multicast test for tiny-switch.

Tests the STORE_MC command which:
1. Node sends STORE_MC command with data to a multicast address
2. Switch writes the data to all nodes in the multicast group
3. Switch returns ACK to the requesting node
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
CMD_STORE_MC = 2

# Response types
RESP_ACK = 1


@cocotb.test()
async def test_multicast(dut):
    """Test multicast write to all 4 nodes."""
    
    logger.info("=" * 60)
    logger.info("TEST: Multicast write to all nodes")
    logger.info("=" * 60)
    
    # Initial data (zeros in all nodes)
    initial_data = [[float_to_bf16(0.0)] for _ in range(4)]
    
    # Multicast address (group 0: all nodes)
    base_addr = 0x10000000
    
    # Data to broadcast
    broadcast_value = float_to_bf16(42.0)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=base_addr)
    
    logger.info("Initial memory state (all zeros):")
    for i in range(4):
        val = mem_ctrl.read(i, base_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=4)
    
    # Send STORE_MC command from Node 0
    logger.info(f"Node 0: Sending STORE_MC to address {base_addr:#x} with value {format_bf16(broadcast_value)}")
    await send_command(dut, port=0, cmd=CMD_STORE_MC, addr=base_addr, data=broadcast_value, metrics=metrics)
    
    # Run simulation until ACK or timeout
    max_cycles = config.max_cycles
    cycles = 0
    response = None
    
    while cycles < max_cycles:
        await mem_ctrl.run()
        await cocotb.triggers.ReadOnly()
        metrics.update()
        format_cycle(dut, cycles)
        
        try:
            resp_valid = dut.node_resp_valid.value.to_unsigned()
            if resp_valid & 1:  # Check port 0
                resp_type = get_signal_slice(dut.node_resp_type, 0, RESP_TYPE_WIDTH)
                resp_data = get_signal_slice(dut.node_resp_data, 0, DATA_WIDTH)
                response = (resp_type, resp_data)
                logger.info(f"Node 0: Received response type={resp_type}")
                break
        except ValueError:
            pass
            
        await RisingEdge(dut.clk)
        cycles += 1
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify ACK received
    assert response is not None, f"No response received within {max_cycles} cycles"
    assert response[0] == RESP_ACK, f"Expected ACK response (1), got {response[0]}"
    
    # Verify all nodes received the broadcast value
    logger.info("Final memory state (should all be 42.0):")
    for i in range(4):
        val = mem_ctrl.read(i, base_addr)
        val_float = bf16_to_float(val)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
        assert abs(val_float - 42.0) < 0.1, \
            f"Node {i} has wrong value: expected 42.0, got {val_float}"
    
    logger.info("TEST PASSED: Multicast write to all nodes successful!")


@cocotb.test()
async def test_multicast_subset(dut):
    """Test multicast write to a subset of nodes (group 2: nodes 2,3 only)."""
    
    logger.info("=" * 60)
    logger.info("TEST: Multicast write to node subset (2,3)")
    logger.info("=" * 60)
    
    # Initial data (different values to distinguish)
    initial_data = [
        [float_to_bf16(1.0)],   # Node 0
        [float_to_bf16(2.0)],   # Node 1
        [float_to_bf16(3.0)],   # Node 2
        [float_to_bf16(4.0)],   # Node 3
    ]
    
    # Use group 2 address (nodes 2,3 only): 0x3000_0000
    base_addr = 0x30000000
    
    # Data to broadcast
    broadcast_value = float_to_bf16(99.0)
    
    # Setup
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=base_addr)
    
    logger.info("Initial memory state:")
    for i in range(4):
        val = mem_ctrl.read(i, base_addr)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
    
    metrics = SwitchMetrics(dut, num_ports=4)
    
    # Send STORE_MC from Node 0
    logger.info(f"Node 0: Sending STORE_MC to group 2 address {base_addr:#x}")
    await send_command(dut, port=0, cmd=CMD_STORE_MC, addr=base_addr, data=broadcast_value, metrics=metrics)
    
    # Run until ACK
    max_cycles = config.max_cycles
    cycles = 0
    response = None
    
    while cycles < max_cycles:
        await mem_ctrl.run()
        await cocotb.triggers.ReadOnly()
        metrics.update()
        
        try:
            resp_valid = dut.node_resp_valid.value.to_unsigned()
            if resp_valid & 1:  # Check port 0
                resp_type = get_signal_slice(dut.node_resp_type, 0, RESP_TYPE_WIDTH)
                response = (resp_type, 0)
                break
        except ValueError:
            pass
            
        await RisingEdge(dut.clk)
        cycles += 1
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    # Verify
    assert response is not None, "No response received"
    assert response[0] == RESP_ACK, f"Expected ACK, got {response[0]}"
    
    # Check memory: nodes 0,1 should be unchanged, nodes 2,3 should have new value
    logger.info("Final memory state:")
    for i in range(4):
        val = mem_ctrl.read(i, base_addr)
        val_float = bf16_to_float(val)
        logger.info(f"  Node {i}: value={format_bf16(val)}")
        
        if i < 2:
            # Nodes 0,1 should be unchanged
            expected = float(i + 1)
            assert abs(val_float - expected) < 0.1, \
                f"Node {i} was modified but shouldn't be: expected {expected}, got {val_float}"
        else:
            # Nodes 2,3 should have the broadcast value
            assert abs(val_float - 99.0) < 0.1, \
                f"Node {i} should have 99.0, got {val_float}"
    
    logger.info("TEST PASSED: Subset multicast write successful!")


@cocotb.test()
async def test_multicast_from_different_port(dut):
    """Test multicast from a non-zero port."""
    
    logger.info("=" * 60)
    logger.info("TEST: Multicast from Port 2")
    logger.info("=" * 60)
    
    initial_data = [[float_to_bf16(0.0)] for _ in range(4)]
    base_addr = 0x10000000
    broadcast_value = float_to_bf16(77.0)
    
    mem_ctrl = await setup(dut, node_data=initial_data, base_addr=base_addr)
    metrics = SwitchMetrics(dut, num_ports=4)
    
    # Send from Port 2 instead of Port 0
    logger.info(f"Node 2: Sending STORE_MC")
    await send_command(dut, port=2, cmd=CMD_STORE_MC, addr=base_addr, data=broadcast_value, metrics=metrics)
    
    # Run until ACK on port 2
    max_cycles = config.max_cycles
    cycles = 0
    response = None
    
    while cycles < max_cycles:
        await mem_ctrl.run()
        await cocotb.triggers.ReadOnly()
        metrics.update()
        
        try:
            resp_valid = dut.node_resp_valid.value.to_unsigned()
            if (resp_valid >> 2) & 1:  # Check port 2
                resp_type = get_signal_slice(dut.node_resp_type, 2, RESP_TYPE_WIDTH)
                response = (resp_type, 0)
                logger.info(f"Node 2: Received ACK")
                break
        except ValueError:
            pass
            
        await RisingEdge(dut.clk)
        cycles += 1
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    assert response is not None, "No response received"
    assert response[0] == RESP_ACK, f"Expected ACK, got {response[0]}"
    
    # All nodes should have 77.0
    for i in range(4):
        val = mem_ctrl.read(i, base_addr)
        val_float = bf16_to_float(val)
        assert abs(val_float - 77.0) < 0.1, \
            f"Node {i} has wrong value: expected 77.0, got {val_float}"
    
    logger.info("TEST PASSED: Multicast from Port 2 successful!")
