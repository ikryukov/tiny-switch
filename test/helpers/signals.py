"""Signal access helpers for tiny-switch testing.

Centralized utilities for reading/writing slices of flattened packed array
signals. sv2v flattens [N-1:0][W-1:0] to [(N*W)-1:0], so port i is at
bits [i*W +: W].
"""

# Signal widths (must match tswitch_pkg.sv)
ADDR_WIDTH = 32
DATA_WIDTH = 16
CMD_WIDTH = 3
RESP_TYPE_WIDTH = 2


def get_signal_bit(signal, port: int) -> int:
    """Get a single bit from a multi-bit signal.

    Returns 0 if the signal value is unresolvable (e.g., X during reset).
    """
    try:
        val = signal.value.to_unsigned()
        return (val >> port) & 1
    except ValueError:
        return 0


def get_signal_slice(signal, port: int, width: int) -> int:
    """Get a slice of a flattened packed array signal.

    For a signal like node_resp_data[(NUM_PORTS * 16) - 1:0], get bits for port i.
    """
    val = signal.value.to_unsigned()
    return (val >> (port * width)) & ((1 << width) - 1)


def set_signal_slice(signal, port: int, width: int, value: int):
    """Set a slice of a flattened packed array signal.

    For a signal like node_cmd[(NUM_PORTS * 3) - 1:0], set bits for port i.
    """
    current = signal.value.to_unsigned() if signal.value.is_resolvable else 0
    mask = ((1 << width) - 1) << (port * width)
    new_val = (current & ~mask) | ((value & ((1 << width) - 1)) << (port * width))
    signal.value = new_val


def pack_signal_slice(current: int, port: int, width: int, value: int) -> int:
    """Pack a value into a specific port slice of an integer.

    Pure function version of set_signal_slice for building packed integers
    without touching signals directly.
    """
    mask = ((1 << width) - 1) << (port * width)
    return (current & ~mask) | ((value & ((1 << width) - 1)) << (port * width))
