"""Shared constants for tiny-switch tests.

These match the values defined in tswitch_pkg.sv.
"""

# ============================================================
# Command Types (Node → Switch)
# ============================================================
CMD_NOP = 0          # No operation
CMD_LOAD_REDUCE = 1  # Read from all nodes, reduce, return result
CMD_STORE_MC = 2     # Write to all nodes (multicast)
CMD_READ = 3         # Normal read (passthrough)
CMD_WRITE = 4        # Normal write (passthrough)

# ============================================================
# Response Types (Switch → Node)
# ============================================================
RESP_DATA = 0   # Read data response
RESP_ACK = 1    # Write acknowledgment
RESP_ERROR = 3  # Error response

# ============================================================
# Multicast Group Addresses (matches group_table.sv defaults)
# ============================================================
ADDR_GROUP_ALL = 0x10000000    # Group 0: all nodes (mask 0xF0000000)
ADDR_GROUP_01 = 0x20000000     # Group 1: nodes 0,1 only
ADDR_GROUP_23 = 0x30000000     # Group 2: nodes 2,3 only

# ============================================================
# Test Parameters
# ============================================================
NUM_NODES = 4
DEFAULT_VECTOR_SIZE = 8
BF16_TOLERANCE = 0.1  # Acceptable difference for BF16 comparisons
