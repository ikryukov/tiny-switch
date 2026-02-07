"""Test helpers for tiny-switch.

This package provides:
- constants: Command/response type constants matching RTL
- signals: Signal access helpers for flattened packed arrays
- setup: DUT initialization and command helpers
- runner: Unified simulation loop functions  
- node_memory: Simulated node memory controller
- metrics: Performance tracking
- bf16: BFloat16 utilities
- logger: Test logging
- config: Test configuration
"""

# Re-export commonly used items for convenient imports
from .constants import (
    CMD_NOP, CMD_LOAD_REDUCE, CMD_STORE_MC, CMD_READ, CMD_WRITE,
    RESP_DATA, RESP_ACK, RESP_ERROR,
    ADDR_GROUP_ALL, ADDR_GROUP_01, ADDR_GROUP_23,
    NUM_NODES, DEFAULT_VECTOR_SIZE, BF16_TOLERANCE,
)

from .setup import setup, send_command

from .runner import (
    run_until_response,
    run_and_expect_data,
    run_and_expect_ack,
    log_test_header,
    log_section,
    log_divider,
)

from .node_memory import NodeMemoryController
from .metrics import SwitchMetrics
from .bf16 import float_to_bf16, bf16_to_float, bf16_sum, format_bf16, bf16_approx_equal
from .logger import logger
from .config import config
