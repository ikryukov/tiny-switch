"""AllReduce test for tiny-switch.

Tests the LOAD_REDUCE command which:
1. Node sends LOAD_REDUCE command to a multicast address
2. Switch reads BFloat16 values from all nodes in group
3. Switch sums the values
4. Switch returns the result to requesting node
"""

from typing import List, Dict, Tuple

import cocotb

from .helpers import (
    setup, send_command,
    run_and_expect_data, run_and_expect_ack, log_test_header,
    float_to_bf16, bf16_to_float, bf16_sum, format_bf16, bf16_approx_equal,
    SwitchMetrics, logger, config,
    CMD_LOAD_REDUCE, CMD_STORE_MC,
    ADDR_GROUP_ALL, ADDR_GROUP_01,
    NUM_NODES, DEFAULT_VECTOR_SIZE, BF16_TOLERANCE,
)


# =============================================================================
# Test Utilities
# =============================================================================

def generate_test_vector(num_nodes: int, vector_size: int) -> List[List[int]]:
    """Generate test data with unique values per node and offset.
    
    Formula: value = (node_id + 1) * 0.1 + offset * 0.5
    This ensures unique values and predictable sums.
    
    Returns:
        List of BF16 value lists, one per node.
    """
    node_data = []
    for node_id in range(num_nodes):
        node_values = [
            float_to_bf16((node_id + 1) * 0.1 + offset * 0.5)
            for offset in range(vector_size)
        ]
        node_data.append(node_values)
    return node_data


def compute_expected_sums(node_data: List[List[int]]) -> List[int]:
    """Compute expected reduction sums for each offset.
    
    Args:
        node_data: List of BF16 value lists, one per node.
        
    Returns:
        List of expected BF16 sums, one per offset.
    """
    num_nodes = len(node_data)
    vector_size = len(node_data[0]) if node_data else 0
    
    expected = []
    for offset in range(vector_size):
        values_at_offset = [node_data[node_id][offset] for node_id in range(num_nodes)]
        expected.append(bf16_sum(values_at_offset))
    return expected


def verify_results(
    actual: List[int],
    expected: List[int],
    label: str = "Result"
) -> bool:
    """Verify a list of BF16 results against expected values.
    
    Args:
        actual: List of actual BF16 values
        expected: List of expected BF16 values
        label: Label for logging
        
    Returns:
        True if all values match within tolerance
    """
    all_passed = True
    logger.info(f"{label} verification:")
    logger.info("-" * 60)
    
    for i, (act, exp) in enumerate(zip(actual, expected)):
        act_float = bf16_to_float(act)
        exp_float = bf16_to_float(exp)
        passed = bf16_approx_equal(act, exp)
        status = "OK" if passed else "FAIL"
        logger.info(f"  [{i}] Expected: {exp_float:8.4f}  Actual: {act_float:8.4f}  [{status}]")
        if not passed:
            all_passed = False
    
    logger.info("-" * 60)
    return all_passed


def log_memory_state(mem_ctrl, base_addr: int, vector_size: int = 1, 
                     num_nodes: int = NUM_NODES, node_offsets: Dict[int, Tuple[int, int]] = None):
    """Log memory state for all nodes.
    
    Args:
        mem_ctrl: Memory controller
        base_addr: Base address
        vector_size: Number of elements to display
        num_nodes: Number of nodes
        node_offsets: Optional dict mapping node_id -> (start, end) offset range to mark
    """
    logger.info("Initial memory state:")
    for node_id in range(num_nodes):
        if node_offsets and node_id in node_offsets:
            start, end = node_offsets[node_id]
            logger.info(f"  Node {node_id} (responsible for offsets [{start}:{end}]):")
        else:
            logger.info(f"  Node {node_id}:")
        
        for offset in range(vector_size):
            addr = base_addr + offset
            val = mem_ctrl.read(node_id, addr)
            marker = ""
            if node_offsets and node_id in node_offsets:
                start, end = node_offsets[node_id]
                marker = " <--" if start <= offset < end else ""
            logger.info(f"    [{offset}] addr={addr:#x} value={format_bf16(val)}{marker}")


# =============================================================================
# Tests
# =============================================================================

@cocotb.test()
async def test_allreduce_1_value(dut):
    """Test AllReduce operation: sum 1 value from each of 4 nodes."""
    
    log_test_header("AllReduce with 4 nodes (1 value each)")
    
    # Test data: Node 0: 1.5, Node 1: 2.0, Node 2: 0.5, Node 3: 1.0
    # Expected sum: 1.5 + 2.0 + 0.5 + 1.0 = 5.0
    test_values = [
        float_to_bf16(1.5),
        float_to_bf16(2.0),
        float_to_bf16(0.5),
        float_to_bf16(1.0),
    ]
    node_data = [[val] for val in test_values]
    
    mem_ctrl = await setup(dut, node_data=node_data, base_addr=ADDR_GROUP_ALL)
    log_memory_state(mem_ctrl, ADDR_GROUP_ALL, vector_size=1)
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    logger.info(f"Node 0: Sending LOAD_REDUCE to address {ADDR_GROUP_ALL:#x}")
    await send_command(dut, port=0, cmd=CMD_LOAD_REDUCE, addr=ADDR_GROUP_ALL, metrics=metrics)
    
    cycles, result = await run_and_expect_data(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    expected_bf16 = bf16_sum(test_values)
    
    logger.info("Result verification:")
    logger.info("-" * 40)
    for i, val in enumerate(test_values):
        logger.info(f"  Node {i}:      {bf16_to_float(val):8.4f}  {format_bf16(val)}")
    logger.info("-" * 40)
    logger.info(f"  Expected:    {bf16_to_float(expected_bf16):8.4f}  {format_bf16(expected_bf16)}")
    logger.info(f"  Actual:      {bf16_to_float(result):8.4f}  {format_bf16(result)}")
    
    assert bf16_approx_equal(result, expected_bf16), \
        f"Result mismatch: expected {format_bf16(expected_bf16)}, got {format_bf16(result)}"
    
    logger.info("TEST PASSED: AllReduce result is correct!")


@cocotb.test()
async def test_allreduce_subset(dut):
    """Test AllReduce with a subset of nodes (group 1: nodes 0,1 only)."""
    
    log_test_header("AllReduce with node subset (0,1)")
    
    test_values = [
        float_to_bf16(3.0),    # Node 0 - in group
        float_to_bf16(4.0),    # Node 1 - in group
        float_to_bf16(100.0),  # Node 2 - excluded
        float_to_bf16(100.0),  # Node 3 - excluded
    ]
    node_data = [[val] for val in test_values]
    
    mem_ctrl = await setup(dut, node_data=node_data, base_addr=ADDR_GROUP_01)
    
    logger.info("Initial memory state:")
    for i in range(NUM_NODES):
        val = mem_ctrl.read(i, ADDR_GROUP_01)
        in_group = "(in group)" if i < 2 else "(excluded)"
        logger.info(f"  Node {i}: value={format_bf16(val)} {in_group}")
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    await send_command(dut, port=0, cmd=CMD_LOAD_REDUCE, addr=ADDR_GROUP_01, metrics=metrics)
    
    cycles, result = await run_and_expect_data(dut, mem_ctrl, metrics, port=0)
    
    logger.info(f"Completed in {cycles} cycles")
    metrics.log_report()
    
    expected_bf16 = bf16_sum([test_values[0], test_values[1]])
    
    logger.info("Result verification (Group 1: Nodes 0,1 only):")
    logger.info("-" * 40)
    for i, val in enumerate(test_values):
        in_group = "(in group)" if i < 2 else "(excluded)"
        logger.info(f"  Node {i}:      {bf16_to_float(val):8.4f}  {in_group}")
    logger.info("-" * 40)
    logger.info(f"  Expected:    {bf16_to_float(expected_bf16):8.4f}")
    logger.info(f"  Actual:      {bf16_to_float(result):8.4f}")
    
    assert bf16_approx_equal(result, expected_bf16), \
        f"Result mismatch: expected {format_bf16(expected_bf16)}, got {format_bf16(result)}"
    
    logger.info("TEST PASSED: Subset AllReduce is correct!")


@cocotb.test()
async def test_allreduce_oneshot(dut, vector_size: int = DEFAULT_VECTOR_SIZE):
    """Test oneshot AllReduce: all nodes reduce all elements in parallel.
    
    Every GPU issues LOAD_REDUCE for all elements. All nodes participate
    and receive the reduced results. This is true AllReduce semantics
    where every participant gets the final result.
    
    For each element:
    - All N nodes issue LOAD_REDUCE to the same address
    - All N nodes receive the same reduced result
    
    Args:
        vector_size: Number of BF16 values per node (default: 8)
    """
    
    log_test_header(f"Oneshot AllReduce ({vector_size} elements, all nodes)")
    
    node_data = generate_test_vector(NUM_NODES, vector_size)
    mem_ctrl = await setup(dut, node_data=node_data, base_addr=ADDR_GROUP_ALL)
    log_memory_state(mem_ctrl, ADDR_GROUP_ALL, vector_size)
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # Results per node: results[node_id][offset] = bf16_value
    results = {node_id: [] for node_id in range(NUM_NODES)}
    total_cycles = 0
    
    # For each element, all nodes issue LOAD_REDUCE
    for offset in range(vector_size):
        addr = ADDR_GROUP_ALL + offset
        logger.info(f"Reducing element [{offset}] at address {addr:#x} (all nodes)")
        
        # Each node issues LOAD_REDUCE for this element
        for node_id in range(NUM_NODES):
            await send_command(dut, port=node_id, cmd=CMD_LOAD_REDUCE, addr=addr, metrics=metrics)
            
            cycles, data = await run_and_expect_data(dut, mem_ctrl, metrics, port=node_id)
            total_cycles += cycles
            results[node_id].append(data)
        
        # Log results for this element from all nodes
        node_results = [format_bf16(results[n][offset]) for n in range(NUM_NODES)]
        logger.info(f"  Element [{offset}] results: {', '.join(node_results)}")
    
    logger.info(f"All {vector_size * NUM_NODES} reductions completed in {total_cycles} total cycles")
    logger.info(f"  ({vector_size} elements × {NUM_NODES} nodes)")
    metrics.log_report()
    
    # Verify all nodes got correct results
    expected = compute_expected_sums(node_data)
    all_passed = True
    
    logger.info("Result verification (all nodes should have identical results):")
    logger.info("-" * 60)
    
    for offset in range(vector_size):
        expected_float = bf16_to_float(expected[offset])
        node_values = [results[n][offset] for n in range(NUM_NODES)]
        node_floats = [bf16_to_float(v) for v in node_values]
        
        # Check all nodes got the same result
        all_same = all(bf16_approx_equal(v, expected[offset]) for v in node_values)
        status = "OK" if all_same else "FAIL"
        
        logger.info(f"  [{offset}] Expected: {expected_float:8.4f}  "
                   f"Nodes: {' '.join(f'{v:8.4f}' for v in node_floats)}  [{status}]")
        
        if not all_same:
            all_passed = False
    
    logger.info("-" * 60)
    assert all_passed, "Some nodes have incorrect results"
    logger.info(f"TEST PASSED: Oneshot AllReduce with {vector_size} elements (all nodes) is correct!")


@cocotb.test()
async def test_allreduce_twoshot(dut, vector_size: int = DEFAULT_VECTOR_SIZE):
    """Test two-shot AllReduce: reduce-scatter followed by allgather.
    
    Phase 1 (Reduce-Scatter): Each GPU processes only its rank-assigned offsets.
    Phase 2 (Allgather): Each node multicasts its reduced results to all others.
    
    This pattern is more bandwidth-efficient for large vectors.
    
    Args:
        vector_size: Number of BF16 values per node (default: 8, must be divisible by NUM_NODES)
    """
    
    assert vector_size % NUM_NODES == 0, \
        f"vector_size ({vector_size}) must be divisible by NUM_NODES ({NUM_NODES})"
    
    elements_per_node = vector_size // NUM_NODES
    
    log_test_header(f"Two-shot AllReduce ({vector_size} elements, {elements_per_node} per node)")
    
    node_data = generate_test_vector(NUM_NODES, vector_size)
    mem_ctrl = await setup(dut, node_data=node_data, base_addr=ADDR_GROUP_ALL)
    
    # Build offset assignment map
    node_offsets = {
        node_id: (node_id * elements_per_node, (node_id + 1) * elements_per_node)
        for node_id in range(NUM_NODES)
    }
    log_memory_state(mem_ctrl, ADDR_GROUP_ALL, vector_size, node_offsets=node_offsets)
    
    metrics = SwitchMetrics(dut, num_ports=NUM_NODES)
    
    # ===== PHASE 1: Reduce-Scatter =====
    logger.info("")
    logger.info("=" * 40)
    logger.info("PHASE 1: Reduce-Scatter")
    logger.info("=" * 40)
    
    reduced_values = {}  # (node_id, offset) -> reduced_value
    
    for node_id in range(NUM_NODES):
        start_offset, end_offset = node_offsets[node_id]
        logger.info(f"Node {node_id}: Reducing offsets [{start_offset}:{end_offset}]")
        
        for offset in range(start_offset, end_offset):
            addr = ADDR_GROUP_ALL + offset
            await send_command(dut, port=node_id, cmd=CMD_LOAD_REDUCE, addr=addr, metrics=metrics)
            
            _, data = await run_and_expect_data(dut, mem_ctrl, metrics, port=node_id)
            
            logger.info(f"  Node {node_id} result [{offset}]: {format_bf16(data)}")
            reduced_values[(node_id, offset)] = data
    
    logger.info("Phase 1 complete: Each node has its partial reductions")
    
    # ===== PHASE 2: Allgather (Multicast) =====
    logger.info("")
    logger.info("=" * 40)
    logger.info("PHASE 2: Allgather (Multicast)")
    logger.info("=" * 40)
    
    for node_id in range(NUM_NODES):
        start_offset, end_offset = node_offsets[node_id]
        logger.info(f"Node {node_id}: Multicasting offsets [{start_offset}:{end_offset}]")
        
        for offset in range(start_offset, end_offset):
            addr = ADDR_GROUP_ALL + offset
            reduced_val = reduced_values[(node_id, offset)]
            
            await send_command(dut, port=node_id, cmd=CMD_STORE_MC, addr=addr, data=reduced_val, metrics=metrics)
            
            await run_and_expect_ack(dut, mem_ctrl, metrics, port=node_id)
            
            logger.info(f"  Node {node_id}: ACK for offset [{offset}]")
    
    logger.info("Phase 2 complete: All reduced values distributed to all nodes")
    
    # ===== Verification =====
    logger.info("")
    logger.info("=" * 40)
    logger.info("VERIFICATION")
    logger.info("=" * 40)
    
    expected_results = compute_expected_sums(node_data)
    
    all_passed = True
    for node_id in range(NUM_NODES):
        logger.info(f"Node {node_id} final state:")
        actual = [mem_ctrl.read(node_id, ADDR_GROUP_ALL + offset) for offset in range(vector_size)]
        
        for offset in range(vector_size):
            actual_float = bf16_to_float(actual[offset])
            expected_float = bf16_to_float(expected_results[offset])
            passed = bf16_approx_equal(actual[offset], expected_results[offset])
            status = "OK" if passed else "FAIL"
            logger.info(f"  [{offset}] Expected: {expected_float:8.4f}  Actual: {actual_float:8.4f}  [{status}]")
            if not passed:
                all_passed = False
    
    metrics.log_report()
    
    assert all_passed, "Some nodes have incorrect final values"
    logger.info(f"TEST PASSED: Two-shot AllReduce with {vector_size} elements is correct!")
