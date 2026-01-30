"""Test configuration for tiny-switch.

Supports two modes:
- Functional: Fast tests with minimal latency (default)
- Performance: Realistic latencies for performance analysis
"""

import os
from dataclasses import dataclass
from typing import Optional


@dataclass
class TestConfig:
    """Configuration for test execution."""
    
    # Memory latencies (cycles)
    read_latency: int
    write_latency: int
    
    # Timeouts
    max_cycles: int
    
    # Mode name for logging
    mode: str
    
    # Expected switch clock frequency (MHz) for time calculations
    clock_mhz: int


# Predefined configurations
FUNCTIONAL = TestConfig(
    read_latency=2,
    write_latency=1,
    max_cycles=200,
    mode="functional",
    clock_mhz=100,  # Arbitrary for functional tests
)

PERFORMANCE_PERFLINK = TestConfig(
    read_latency=150,      # Simulated high-speed interconnect
    write_latency=75,
    max_cycles=2000,
    mode="performance-perflink",
    clock_mhz=500,
)

PERFORMANCE_SLOW = TestConfig(
    read_latency=500,      # Simulated slower interconnect
    write_latency=250,
    max_cycles=5000,
    mode="performance-slow",
    clock_mhz=500,
)


def get_config() -> TestConfig:
    """Get test configuration based on environment variable.
    
    Set TEST_MODE environment variable:
    - "functional" (default): Fast functional tests
    - "perflink": High-speed interconnect latencies
    - "slow": Slower interconnect latencies
    
    Example:
        TEST_MODE=perflink make test_allreduce
    """
    mode = os.environ.get("TEST_MODE", "functional").lower()
    
    if mode == "perflink":
        return PERFORMANCE_PERFLINK
    elif mode == "slow":
        return PERFORMANCE_SLOW
    else:
        return FUNCTIONAL


# Convenience accessor
config = get_config()
