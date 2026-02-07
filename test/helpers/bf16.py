"""BFloat16 utilities for tiny-switch testing."""

import struct


def float_to_bf16(value: float) -> int:
    """Convert a Python float to BFloat16 (16-bit integer representation).
    
    BFloat16 format:
    - Bit 15: Sign (1 bit)
    - Bits 14-7: Exponent (8 bits, bias 127)
    - Bits 6-0: Mantissa (7 bits, implicit leading 1)
    
    BFloat16 is the upper 16 bits of IEEE 754 float32.
    """
    # Convert to float32 bytes
    f32_bytes = struct.pack('>f', value)  # Big-endian
    # Take upper 16 bits (BF16)
    bf16 = (f32_bytes[0] << 8) | f32_bytes[1]
    return bf16


def bf16_to_float(bf16: int) -> float:
    """Convert a BFloat16 (16-bit integer) to Python float.
    
    Pads the lower 16 bits with zeros to create float32.
    """
    # Pad to float32 (upper 16 bits are BF16, lower 16 are zeros)
    f32_bytes = bytes([(bf16 >> 8) & 0xFF, bf16 & 0xFF, 0, 0])
    return struct.unpack('>f', f32_bytes)[0]


def bf16_add(a: int, b: int) -> int:
    """Add two BFloat16 values (for test verification)."""
    fa = bf16_to_float(a)
    fb = bf16_to_float(b)
    return float_to_bf16(fa + fb)


def bf16_sum(values: list) -> int:
    """Sum a list of BFloat16 values."""
    result = 0x0000  # BF16 zero
    for v in values:
        result = bf16_add(result, v)
    return result


# Common BF16 values for testing
BF16_ZERO = 0x0000       # 0.0
BF16_ONE = 0x3F80        # 1.0
BF16_TWO = 0x4000        # 2.0
BF16_HALF = 0x3F00       # 0.5
BF16_NEG_ONE = 0xBF80    # -1.0


def bf16_approx_equal(a: int, b: int, tolerance: float = 0.1) -> bool:
    """Check if two BF16 values are approximately equal.
    
    Args:
        a: First BF16 value (16-bit integer)
        b: Second BF16 value (16-bit integer)
        tolerance: Maximum allowed difference in float representation
        
    Returns:
        True if the float representations differ by less than tolerance
    """
    return abs(bf16_to_float(a) - bf16_to_float(b)) < tolerance


def format_bf16(bf16: int) -> str:
    """Format BF16 value for display."""
    f = bf16_to_float(bf16)
    return f"0x{bf16:04X} ({f:.4f})"


if __name__ == "__main__":
    # Test the utilities
    print("BFloat16 Utility Tests")
    print("=" * 40)
    
    test_values = [0.0, 1.0, 2.0, 0.5, -1.0, 3.14159, 100.0]
    
    for v in test_values:
        bf16 = float_to_bf16(v)
        back = bf16_to_float(bf16)
        print(f"{v:10.4f} -> 0x{bf16:04X} -> {back:10.4f}")
    
    print()
    print("Sum test:")
    values = [float_to_bf16(1.5), float_to_bf16(2.0), float_to_bf16(0.5), float_to_bf16(1.0)]
    result = bf16_sum(values)
    print(f"1.5 + 2.0 + 0.5 + 1.0 = {bf16_to_float(result):.4f} (expected: 5.0)")
