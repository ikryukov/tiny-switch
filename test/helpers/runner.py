"""Unified simulation runner for tiny-switch tests.

Consolidates the common simulation loop patterns used across all tests.
"""

from typing import Optional, Tuple
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from .signals import get_signal_slice, DATA_WIDTH, RESP_TYPE_WIDTH
from .config import config
from .logger import logger
from .constants import RESP_DATA, RESP_ACK


async def run_until_response(
    dut,
    mem_ctrl,
    metrics,
    port: int,
    max_cycles: int = None,
    expect_data: bool = True,
) -> Tuple[int, Optional[Tuple[int, int]]]:
    """Run simulation until a response is received on the given port.
    
    This is the unified simulation loop used by all tests. It:
    1. Processes memory requests each cycle
    2. Updates metrics
    3. Checks for response on the specified port
    4. Returns when response received or timeout
    
    Args:
        dut: Device under test
        mem_ctrl: NodeMemoryController for simulating node memory
        metrics: SwitchMetrics for tracking performance
        port: Port number to monitor for response (0-3)
        max_cycles: Maximum cycles to wait (default: config.max_cycles)
        expect_data: If True, capture response data; if False, only capture type
        
    Returns:
        Tuple of (cycles_elapsed, response) where:
        - cycles_elapsed: Number of simulation cycles run
        - response: (resp_type, resp_data) tuple, or None if timeout
    """
    if max_cycles is None:
        max_cycles = config.max_cycles
    
    cycles = 0
    while cycles < max_cycles:
        # Process memory requests
        await mem_ctrl.run()
        
        # Sample signals in ReadOnly phase
        await ReadOnly()
        metrics.update()
        
        try:
            # Check for response valid on this port
            resp_valid = dut.node_resp_valid.value.to_unsigned()
            if (resp_valid >> port) & 1:
                resp_type = get_signal_slice(dut.node_resp_type, port, RESP_TYPE_WIDTH)
                resp_data = get_signal_slice(dut.node_resp_data, port, DATA_WIDTH) if expect_data else 0
                await RisingEdge(dut.clk)  # Exit ReadOnly phase
                return cycles, (resp_type, resp_data)
        except ValueError:
            pass  # Signals might be X
        
        await RisingEdge(dut.clk)
        cycles += 1
    
    return cycles, None


async def run_and_expect_data(
    dut,
    mem_ctrl, 
    metrics,
    port: int,
    max_cycles: int = None,
) -> Tuple[int, int]:
    """Run until DATA response and return the data.
    
    Convenience wrapper that asserts DATA response type.
    
    Args:
        dut: Device under test
        mem_ctrl: Memory controller
        metrics: Metrics tracker
        port: Port to monitor
        max_cycles: Maximum cycles to wait
        
    Returns:
        Tuple of (cycles_elapsed, data_value)
        
    Raises:
        AssertionError: If no response or wrong response type
    """
    cycles, response = await run_until_response(
        dut, mem_ctrl, metrics, port, max_cycles, expect_data=True
    )
    
    assert response is not None, f"Port {port}: No response within {max_cycles or config.max_cycles} cycles"
    resp_type, resp_data = response
    assert resp_type == RESP_DATA, f"Port {port}: Expected DATA response ({RESP_DATA}), got {resp_type}"
    
    return cycles, resp_data


async def run_and_expect_ack(
    dut,
    mem_ctrl,
    metrics,
    port: int,
    max_cycles: int = None,
) -> int:
    """Run until ACK response.
    
    Convenience wrapper that asserts ACK response type.
    
    Args:
        dut: Device under test
        mem_ctrl: Memory controller
        metrics: Metrics tracker  
        port: Port to monitor
        max_cycles: Maximum cycles to wait
        
    Returns:
        Number of cycles elapsed
        
    Raises:
        AssertionError: If no response or wrong response type
    """
    cycles, response = await run_until_response(
        dut, mem_ctrl, metrics, port, max_cycles, expect_data=False
    )
    
    assert response is not None, f"Port {port}: No ACK within {max_cycles or config.max_cycles} cycles"
    resp_type, _ = response
    assert resp_type == RESP_ACK, f"Port {port}: Expected ACK response ({RESP_ACK}), got {resp_type}"
    
    return cycles


def log_test_header(title: str):
    """Log a formatted test header banner."""
    logger.info("=" * 60)
    logger.info(f"TEST: {title}")
    logger.info("=" * 60)


def log_section(title: str, width: int = 40):
    """Log a section header within a test."""
    logger.info("")
    logger.info("=" * width)
    logger.info(title)
    logger.info("=" * width)


def log_divider(width: int = 60):
    """Log a horizontal divider line."""
    logger.info("-" * width)
