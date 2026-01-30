"""Debug formatting utilities for tiny-switch tests."""

from .bf16 import bf16_to_float, format_bf16
from .logger import logger


# Command names
CMD_NAMES = {
    0: 'NOP',
    1: 'LOAD_REDUCE',
    2: 'STORE_MC',
    3: 'READ',
    4: 'WRITE',
}

# Response type names
RESP_NAMES = {
    0: 'DATA',
    1: 'ACK',
    3: 'ERROR',
}

# Decoder state names
DEC_STATE_NAMES = {
    0: 'IDLE',
    1: 'DECODE',
    2: 'LOOKUP',
    3: 'DISPATCH',
    4: 'WAIT',
    5: 'RESPOND',
}

# Reduction state names
RED_STATE_NAMES = {
    0: 'IDLE',
    1: 'FIRST',
    2: 'REDUCING',
    3: 'DONE',
    4: 'RESPOND',
}


def format_cmd(cmd: int) -> str:
    """Format command type for display."""
    return CMD_NAMES.get(cmd, f'UNKNOWN({cmd})')


def format_resp(resp: int) -> str:
    """Format response type for display."""
    return RESP_NAMES.get(resp, f'UNKNOWN({resp})')


def format_node_mask(mask: int) -> str:
    """Format node mask as list of nodes."""
    nodes = []
    for i in range(4):
        if mask & (1 << i):
            nodes.append(str(i))
    return '{' + ','.join(nodes) + '}'


def format_addr(addr: int) -> str:
    """Format address for display."""
    return f"0x{addr:08X}"


def format_cycle(dut, cycle: int):
    """Format and log cycle-by-cycle state (simplified version)."""
    try:
        busy = int(dut.busy.value)
        
        # Only log when switch is busy or every 10 cycles
        if busy or cycle % 10 == 0:
            logger.debug(f"Cycle {cycle:4d}: busy={busy}")
    except Exception as e:
        logger.debug(f"Cycle {cycle:4d}: (unable to read state: {e})")


def format_reduction_result(data: int, src_port: int) -> str:
    """Format reduction result for display."""
    return f"Port {src_port} <- {format_bf16(data)}"


def format_memory_op(op_type: str, port: int, addr: int, data: int = None) -> str:
    """Format memory operation for display."""
    if data is not None:
        return f"{op_type} Port{port} {format_addr(addr)} = {format_bf16(data)}"
    return f"{op_type} Port{port} {format_addr(addr)}"
