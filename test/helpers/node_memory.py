"""Simulated node memory for tiny-switch testing.

Each node has its own memory that the switch can read from and write to.
This simulates the GPU/accelerator memory that the switch accesses.
"""

from typing import Dict, List, Optional
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from .bf16 import bf16_to_float, format_bf16
from .logger import logger
from .signals import get_signal_slice, pack_signal_slice, ADDR_WIDTH, DATA_WIDTH


class NodeMemory:
    """Simulates memory for a single node."""
    
    def __init__(self, node_id: int, size: int = 256):
        self.node_id = node_id
        self.size = size
        self.memory: Dict[int, int] = {}  # address -> BF16 value
        
        # Pending read response
        self.pending_read_addr: Optional[int] = None
        self.read_latency = 2  # Cycles of read latency
        self.read_latency_counter = 0
        
        # Pending write
        self.pending_write_addr: Optional[int] = None
        self.pending_write_data: Optional[int] = None
        self.write_latency = 1
        self.write_latency_counter = 0
        
    def load(self, data: List[int], base_addr: int = 0):
        """Load BF16 values into memory starting at base_addr."""
        for i, value in enumerate(data):
            self.memory[base_addr + i] = value & 0xFFFF
            
    def read(self, addr: int) -> int:
        """Read a BF16 value from memory (instant, for Python-side checks)."""
        return self.memory.get(addr, 0x0000)
        
    def write(self, addr: int, value: int):
        """Write a BF16 value to memory (instant, for Python-side)."""
        self.memory[addr] = value & 0xFFFF
        
    def display(self, start: int = 0, count: int = 16):
        """Display memory contents."""
        logger.info(f"Node {self.node_id} Memory [{start}:{start+count}]:")
        for i in range(start, start + count, 4):
            values = []
            for j in range(4):
                addr = i + j
                if addr in self.memory:
                    val = self.memory[addr]
                    values.append(f"{format_bf16(val)}")
                else:
                    values.append("--------")
            logger.info(f"  [{i:3d}]: {' | '.join(values)}")


class NodeMemoryController:
    """Controls memory access for all nodes in the simulation."""
    
    def __init__(self, dut, num_nodes: int = 4, read_latency: int = 2):
        self.dut = dut
        self.num_nodes = num_nodes
        self.memories = [NodeMemory(i) for i in range(num_nodes)]
        self.read_latency = read_latency
        
        # Track pending operations per node
        self.pending_reads = [None] * num_nodes  # (addr, cycles_remaining)
        self.pending_writes = [None] * num_nodes  # (addr, data, cycles_remaining)
        
    def load(self, node_id: int, data: List[int], base_addr: int = 0):
        """Load data into a node's memory."""
        self.memories[node_id].load(data, base_addr)
        
    def load_all(self, data: List[int], base_addr: int = 0):
        """Load the same data into all nodes' memories."""
        for mem in self.memories:
            mem.load(data, base_addr)
            
    def load_different(self, data_per_node: List[List[int]], base_addr: int = 0):
        """Load different data into each node's memory."""
        for i, data in enumerate(data_per_node):
            self.memories[i].load(data, base_addr)
            
    def display(self, node_id: int = None, start: int = 0, count: int = 16):
        """Display memory contents."""
        if node_id is not None:
            self.memories[node_id].display(start, count)
        else:
            for mem in self.memories:
                mem.display(start, count)
                
    def read(self, node_id: int, addr: int) -> int:
        """Direct read for Python-side verification."""
        return self.memories[node_id].read(addr)
    
    async def run(self):
        """Process memory requests each cycle.
        
        Processes all nodes and sets all output signals atomically.
        """
        dut = self.dut
        
        # Read current signal values once
        try:
            read_valid_all = dut.node_mem_read_valid.value.to_unsigned()
        except ValueError:
            read_valid_all = 0
            
        try:
            write_valid_all = dut.node_mem_write_valid.value.to_unsigned()
        except ValueError:
            write_valid_all = 0
        
        # Accumulate output values
        read_data_valid_out = 0
        read_data_out = 0
        write_done_out = 0
        
        # Process each node
        for node_id in range(self.num_nodes):
            mem = self.memories[node_id]
            
            # Get input signals for this node
            read_valid = (read_valid_all >> node_id) & 1
            write_valid = (write_valid_all >> node_id) & 1
            
            # Handle pending read
            if self.pending_reads[node_id] is not None:
                addr, cycles = self.pending_reads[node_id]
                if cycles <= 1:
                    # Return data
                    data = mem.read(addr)
                    read_data_valid_out |= (1 << node_id)
                    read_data_out = pack_signal_slice(read_data_out, node_id, DATA_WIDTH, data)
                    self.pending_reads[node_id] = None
                    logger.debug(f"Node {node_id}: Read response addr={addr:08X} data={format_bf16(data)}")
                else:
                    self.pending_reads[node_id] = (addr, cycles - 1)
            
            # Check for new read request (only if not currently pending)
            if read_valid and self.pending_reads[node_id] is None:
                try:
                    addr = get_signal_slice(dut.node_mem_read_addr, node_id, ADDR_WIDTH)
                    self.pending_reads[node_id] = (addr, self.read_latency)
                    logger.debug(f"Node {node_id}: Read request addr={addr:08X}")
                except ValueError:
                    pass
                    
            # Handle pending write
            if self.pending_writes[node_id] is not None:
                addr, data, cycles = self.pending_writes[node_id]
                if cycles <= 1:
                    # Complete write
                    mem.write(addr, data)
                    write_done_out |= (1 << node_id)
                    self.pending_writes[node_id] = None
                    logger.debug(f"Node {node_id}: Write complete addr={addr:08X} data={format_bf16(data)}")
                else:
                    self.pending_writes[node_id] = (addr, data, cycles - 1)
            
            # Check for new write request (only if not currently pending)
            if write_valid and self.pending_writes[node_id] is None:
                try:
                    addr = get_signal_slice(dut.node_mem_write_addr, node_id, ADDR_WIDTH)
                    data = get_signal_slice(dut.node_mem_write_data, node_id, DATA_WIDTH)
                    self.pending_writes[node_id] = (addr, data, 1)  # 1 cycle write latency
                    logger.debug(f"Node {node_id}: Write request addr={addr:08X} data={format_bf16(data)}")
                except ValueError:
                    pass
        
        # Set all output signals at once
        dut.node_mem_read_data_valid.value = read_data_valid_out
        dut.node_mem_read_data.value = read_data_out
        dut.node_mem_write_done.value = write_done_out
