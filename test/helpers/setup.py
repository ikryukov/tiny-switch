"""Test setup utilities for tiny-switch."""

from typing import List, Optional
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

from .node_memory import NodeMemoryController
from .logger import logger
from .config import config


# Signal widths (must match tswitch_pkg.sv)
ADDR_WIDTH = 32
DATA_WIDTH = 16
CMD_WIDTH = 3
RESP_TYPE_WIDTH = 2


def _get_test_name() -> str:
    """Get the current test name from cocotb."""
    import os
    
    # Try COCOTB_TEST_MODULES env var (e.g., "test.test_allreduce")
    test_module = os.environ.get("COCOTB_TEST_MODULES", "")
    if test_module:
        # Extract last part: "test.test_allreduce" -> "test_allreduce"
        name = test_module.split(".")[-1]
        # Remove "test_" prefix if present
        if name.startswith("test_"):
            name = name[5:]
        return name
    
    # Fallback: try cocotb internal API
    try:
        test = cocotb._scheduler._test
        if test is not None:
            name = test.__name__
            if name.startswith('test_'):
                name = name[5:]
            return name
    except (AttributeError, TypeError):
        pass
    
    return "unknown"


def set_signal_slice(signal, port: int, width: int, value: int):
    """Set a slice of a flattened packed array signal.
    
    For a signal like node_cmd[(NUM_PORTS * 3) - 1:0], set bits for port i.
    sv2v flattens [N-1:0][W-1:0] to [(N*W)-1:0], so port i is at bits [i*W +: W].
    """
    current = signal.value.to_unsigned() if signal.value.is_resolvable else 0
    mask = ((1 << width) - 1) << (port * width)
    new_val = (current & ~mask) | ((value & ((1 << width) - 1)) << (port * width))
    signal.value = new_val


def get_signal_slice(signal, port: int, width: int) -> int:
    """Get a slice of a flattened packed array signal.
    
    For a signal like node_resp_data[(NUM_PORTS * 16) - 1:0], get bits for port i.
    """
    val = signal.value.to_unsigned()
    return (val >> (port * width)) & ((1 << width) - 1)


async def setup(
    dut,
    node_data: List[List[int]] = None,
    base_addr: int = 0x10000000,
    read_latency: Optional[int] = None,
    num_ports: int = 4
) -> NodeMemoryController:
    """Set up the test environment.
    
    Args:
        dut: Device under test
        node_data: List of data lists, one per node. If None, uses default test data.
        base_addr: Base address for data in each node's memory
        read_latency: Simulated read latency in cycles (uses config default if None)
        num_ports: Number of ports (default 4)
        
    Returns:
        NodeMemoryController for memory simulation
    """
    # Use config default if not specified
    if read_latency is None:
        read_latency = config.read_latency
    
    # Configure logger with test name
    test_name = _get_test_name()
    logger.configure(test_name)
    
    logger.info(f"Test mode: {config.mode} (read_latency={read_latency} cycles)")
    
    logger.info("Setting up tiny-switch test")
    
    # Create clock (10ns period = 100MHz)
    clock = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clock.start())
    
    # Initialize all inputs to known state
    dut.rst_n.value = 0
    
    # Initialize single-bit per port signals (can be indexed)
    dut.node_cmd_valid.value = 0
    dut.node_resp_ready.value = (1 << num_ports) - 1  # All ports ready
    dut.node_mem_read_data_valid.value = 0
    dut.node_mem_write_done.value = 0
    
    # Initialize flattened packed array signals to 0
    dut.node_cmd.value = 0
    dut.node_addr.value = 0
    dut.node_wdata.value = 0
    dut.node_mem_read_data.value = 0
    
    # Wait a few cycles in reset
    for _ in range(3):
        await RisingEdge(dut.clk)
    
    # Release reset
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    
    logger.info("Reset complete")
    
    # Create memory controller
    mem_ctrl = NodeMemoryController(dut, num_nodes=num_ports, read_latency=read_latency)
    
    # Load test data if provided
    if node_data is not None:
        mem_ctrl.load_different(node_data, base_addr)
        logger.info(f"Loaded data to nodes at base address {base_addr:#x}")
    
    return mem_ctrl


async def send_command(dut, port: int, cmd: int, addr: int, data: int = 0, metrics=None):
    """Send a command from a node to the switch.
    
    Args:
        dut: Device under test
        port: Node port (0-3)
        cmd: Command type (CMD_LOAD_REDUCE=1, CMD_STORE_MC=2, etc.)
        addr: Address for the operation
        data: Data for write operations
        metrics: Optional SwitchMetrics object to track the command
    """
    # Set command valid bit for this port
    current_valid = dut.node_cmd_valid.value.to_unsigned() if dut.node_cmd_valid.value.is_resolvable else 0
    dut.node_cmd_valid.value = current_valid | (1 << port)
    
    # Set command type for this port (flattened array)
    set_signal_slice(dut.node_cmd, port, CMD_WIDTH, cmd)
    
    # Set address for this port (flattened array)
    set_signal_slice(dut.node_addr, port, ADDR_WIDTH, addr)
    
    # Set write data for this port (flattened array)
    set_signal_slice(dut.node_wdata, port, DATA_WIDTH, data)
    
    # Wait for command to be accepted
    while True:
        await RisingEdge(dut.clk)
        ready = dut.node_cmd_ready.value.to_unsigned()
        if (ready >> port) & 1:
            break
            
    # Deassert valid for this port
    current_valid = dut.node_cmd_valid.value.to_unsigned()
    dut.node_cmd_valid.value = current_valid & ~(1 << port)
    
    # Track command in metrics if provided
    if metrics is not None:
        metrics.port_commands[port] = metrics.port_commands.get(port, 0) + 1
        if cmd == 1:  # LOAD_REDUCE
            metrics.reductions_started += 1
            metrics.reduction_start_cycle = metrics.total_cycles
        elif cmd == 2:  # STORE_MC
            metrics.multicasts_started += 1
            metrics.multicast_start_cycle = metrics.total_cycles
    
    logger.info(f"Node {port}: Sent command {cmd} to address {addr:#x}")


async def wait_response(dut, port: int, timeout: int = 100):
    """Wait for a response from the switch.
    
    Args:
        dut: Device under test
        port: Node port (0-3)
        timeout: Maximum cycles to wait
        
    Returns:
        Tuple of (response_type, response_data) or None if timeout
    """
    for _ in range(timeout):
        await RisingEdge(dut.clk)
        try:
            resp_valid = dut.node_resp_valid.value.integer
            if (resp_valid >> port) & 1:
                rtype = get_signal_slice(dut.node_resp_type, port, RESP_TYPE_WIDTH)
                rdata = get_signal_slice(dut.node_resp_data, port, DATA_WIDTH)
                logger.info(f"Node {port}: Received response type={rtype} data={rdata:#x}")
                return (rtype, rdata)
        except ValueError:
            pass
            
    logger.warning(f"Node {port}: Timeout waiting for response")
    return None
