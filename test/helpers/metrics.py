"""Performance metrics for tiny-switch testing."""

from typing import Dict, List, Optional
from .logger import logger
from .bf16 import bf16_to_float
from .signals import get_signal_bit, get_signal_slice, CMD_WIDTH, RESP_TYPE_WIDTH


class SwitchMetrics:
    """Tracks and reports switch performance metrics during simulation."""
    
    # Decoder state values (from tswitch_pkg.sv)
    DEC_IDLE = 0
    DEC_DECODE = 1
    DEC_LOOKUP = 2
    DEC_DISPATCH = 3
    DEC_WAIT = 4
    DEC_RESPOND = 5
    
    def __init__(self, dut, num_ports: int = 4):
        self.dut = dut
        self.num_ports = num_ports
        
        # Cycle counters
        self.total_cycles = 0
        self.busy_cycles = 0
        
        # Cycle breakdown by phase
        self.decode_cycles = 0      # DECODE + LOOKUP + DISPATCH
        self.memory_wait_cycles = 0  # Waiting for memory responses
        self.compute_cycles = 0      # Actual reduction computation
        self.response_cycles = 0     # RESPOND state
        
        # Track when memory requests are outstanding
        self.pending_reads = [False] * num_ports
        self.pending_writes = [False] * num_ports
        
        # Operation counters
        self.reductions_started = 0
        self.reductions_completed = 0
        self.multicasts_started = 0
        self.multicasts_completed = 0
        self.values_reduced = 0  # Total BF16 values that went through adder
        
        # Memory operation counters
        self.memory_reads_issued = 0
        self.memory_reads_completed = 0
        self.memory_writes_issued = 0
        self.memory_writes_completed = 0
        
        # Latency tracking
        self.reduction_start_cycle: Optional[int] = None
        self.reduction_latencies: List[int] = []
        self.multicast_start_cycle: Optional[int] = None
        self.multicast_latencies: List[int] = []
        
        # Memory latency tracking
        self.read_start_cycles: List[Optional[int]] = [None] * num_ports
        self.memory_latencies: List[int] = []
        
        # Per-port metrics
        self.port_commands: Dict[int, int] = {i: 0 for i in range(num_ports)}
        self.port_responses: Dict[int, int] = {i: 0 for i in range(num_ports)}
        
        # Decoder state tracking
        self.cycles_per_dec_state: Dict[int, int] = {i: 0 for i in range(6)}
        
    def update(self):
        """Call this every clock cycle to update metrics."""
        self.total_cycles += 1
        
        try:
            # Track busy cycles
            busy = int(self.dut.busy.value)
            if busy:
                self.busy_cycles += 1
            
            # Try to read decoder state (hierarchical access)
            dec_state = self._get_decoder_state()
            if dec_state is not None:
                self.cycles_per_dec_state[dec_state] = self.cycles_per_dec_state.get(dec_state, 0) + 1
                
                # Categorize by phase
                if dec_state in [self.DEC_DECODE, self.DEC_LOOKUP, self.DEC_DISPATCH]:
                    self.decode_cycles += 1
                elif dec_state == self.DEC_RESPOND:
                    self.response_cycles += 1
            
            # Track memory operations and detect waiting
            any_read_pending = False
            any_write_pending = False
            
            for i in range(self.num_ports):
                # Read tracking - use flattened array access
                read_valid = get_signal_bit(self.dut.node_mem_read_valid, i)
                read_data_valid = get_signal_bit(self.dut.node_mem_read_data_valid, i)
                
                if read_valid == 1:
                    if not self.pending_reads[i]:
                        self.memory_reads_issued += 1
                        self.read_start_cycles[i] = self.total_cycles
                    self.pending_reads[i] = True
                    
                if read_data_valid == 1:
                    self.memory_reads_completed += 1
                    if self.read_start_cycles[i] is not None:
                        latency = self.total_cycles - self.read_start_cycles[i]
                        self.memory_latencies.append(latency)
                        self.read_start_cycles[i] = None
                    self.pending_reads[i] = False
                    self.values_reduced += 1  # Each read feeds reduction
                
                if self.pending_reads[i]:
                    any_read_pending = True
                    
                # Write tracking - use flattened array access
                write_valid = get_signal_bit(self.dut.node_mem_write_valid, i)
                write_done = get_signal_bit(self.dut.node_mem_write_done, i)
                
                if write_valid == 1:
                    if not self.pending_writes[i]:
                        self.memory_writes_issued += 1
                    self.pending_writes[i] = True
                    
                if write_done == 1:
                    self.memory_writes_completed += 1
                    self.pending_writes[i] = False
                    
                if self.pending_writes[i]:
                    any_write_pending = True
            
            # Count memory wait cycles
            if any_read_pending or any_write_pending:
                self.memory_wait_cycles += 1
            
            # Track command submissions - use flattened array access
            for i in range(self.num_ports):
                cmd_valid = get_signal_bit(self.dut.node_cmd_valid, i)
                cmd_ready = get_signal_bit(self.dut.node_cmd_ready, i)
                if cmd_valid == 1 and cmd_ready == 1:
                    self.port_commands[i] += 1
                    cmd = get_signal_slice(self.dut.node_cmd, i, CMD_WIDTH)
                    if cmd == 1:  # LOAD_REDUCE
                        self.reductions_started += 1
                        self.reduction_start_cycle = self.total_cycles
                    elif cmd == 2:  # STORE_MC
                        self.multicasts_started += 1
                        self.multicast_start_cycle = self.total_cycles
                        
            # Track responses - use flattened array access
            for i in range(self.num_ports):
                resp_valid = get_signal_bit(self.dut.node_resp_valid, i)
                resp_ready = get_signal_bit(self.dut.node_resp_ready, i)
                if resp_valid == 1 and resp_ready == 1:
                    self.port_responses[i] += 1
                    resp_type = get_signal_slice(self.dut.node_resp_type, i, RESP_TYPE_WIDTH)
                    if resp_type == 0:  # DATA (reduction result)
                        self.reductions_completed += 1
                        if self.reduction_start_cycle is not None:
                            latency = self.total_cycles - self.reduction_start_cycle
                            self.reduction_latencies.append(latency)
                            self.reduction_start_cycle = None
                    elif resp_type == 1:  # ACK (multicast done)
                        self.multicasts_completed += 1
                        if self.multicast_start_cycle is not None:
                            latency = self.total_cycles - self.multicast_start_cycle
                            self.multicast_latencies.append(latency)
                            self.multicast_start_cycle = None
                            
        except ValueError:
            pass  # Signals are X during reset
    
    def _get_decoder_state(self) -> Optional[int]:
        """Try to read decoder state via hierarchical access."""
        try:
            # Try hierarchical access to decoder state
            state = self.dut.u_cmd_decoder.state.value
            return int(state)
        except (AttributeError, ValueError):
            return None
            
    def report(self) -> str:
        """Generate a formatted performance report."""
        lines = []
        lines.append("")
        lines.append("=" * 60)
        lines.append("              SWITCH PERFORMANCE METRICS")
        lines.append("=" * 60)
        
        # Basic metrics
        lines.append(f"Total Cycles:                    {self.total_cycles:,}")
        
        # Cycle breakdown
        lines.append("")
        lines.append("-" * 60)
        lines.append("CYCLE BREAKDOWN")
        lines.append("-" * 60)
        
        if self.total_cycles > 0:
            # Calculate compute cycles (values received - time to reduce them)
            # Each reduction takes N-1 additions for N values
            compute_estimate = max(0, self.values_reduced - 1) if self.reductions_completed > 0 else 0
            overhead_cycles = self.total_cycles - self.memory_wait_cycles - compute_estimate
            
            lines.append(f"  Command processing:      {self.decode_cycles:5d} cycles ({100*self.decode_cycles/self.total_cycles:5.1f}%)")
            lines.append(f"  Waiting for memory:      {self.memory_wait_cycles:5d} cycles ({100*self.memory_wait_cycles/self.total_cycles:5.1f}%)")
            lines.append(f"  Reduction compute:       {compute_estimate:5d} cycles ({100*compute_estimate/self.total_cycles:5.1f}%)")
            lines.append(f"  Response/other:          {self.response_cycles:5d} cycles ({100*self.response_cycles/self.total_cycles:5.1f}%)")
        
        # Efficiency metrics
        lines.append("")
        lines.append("-" * 60)
        lines.append("EFFICIENCY")
        lines.append("-" * 60)
        
        if self.total_cycles > 0:
            compute_estimate = max(0, self.values_reduced - 1) if self.reductions_completed > 0 else 0
            compute_efficiency = 100 * compute_estimate / self.total_cycles if self.total_cycles > 0 else 0
            memory_fraction = 100 * self.memory_wait_cycles / self.total_cycles
            
            lines.append(f"  Compute efficiency:      {compute_efficiency:5.1f}%  (useful work / total)")
            lines.append(f"  Memory wait fraction:    {memory_fraction:5.1f}%  (time waiting for data)")
            
            if self.memory_latencies:
                avg_mem_lat = sum(self.memory_latencies) / len(self.memory_latencies)
                lines.append(f"  Avg memory latency:      {avg_mem_lat:5.1f} cycles")
            
            # Theoretical minimum (no memory latency)
            if self.reductions_completed > 0:
                # Min = decode(~3) + dispatch(~1) + compute(N-1) + respond(~1)
                theoretical_min = 5 + compute_estimate
                lines.append(f"  Theoretical min latency: {theoretical_min:5d} cycles (zero memory wait)")
                if self.reduction_latencies:
                    actual = self.reduction_latencies[0]
                    speedup_possible = actual / theoretical_min if theoretical_min > 0 else 1
                    lines.append(f"  Actual latency:          {actual:5d} cycles")
                    lines.append(f"  Potential speedup:       {speedup_possible:5.1f}x (with ideal memory)")
        
        # Throughput metrics
        lines.append("")
        lines.append("-" * 60)
        lines.append("THROUGHPUT")
        lines.append("-" * 60)
        
        if self.total_cycles > 0:
            ops = self.reductions_completed + self.multicasts_completed
            ops_per_cycle = ops / self.total_cycles
            values_per_cycle = self.values_reduced / self.total_cycles
            
            lines.append(f"  Operations completed:    {ops:5d}")
            lines.append(f"  Values reduced:          {self.values_reduced:5d}")
            lines.append(f"  Ops/cycle:               {ops_per_cycle:5.3f}")
            lines.append(f"  Values/cycle:            {values_per_cycle:5.3f}")
        
        # Memory operations
        lines.append("")
        lines.append("-" * 60)
        lines.append("MEMORY OPERATIONS")
        lines.append("-" * 60)
        lines.append(f"  Reads issued:            {self.memory_reads_issued:5d}")
        lines.append(f"  Reads completed:         {self.memory_reads_completed:5d}")
        lines.append(f"  Writes issued:           {self.memory_writes_issued:5d}")
        lines.append(f"  Writes completed:        {self.memory_writes_completed:5d}")
        
        if self.total_cycles > 0:
            read_bw = self.memory_reads_completed / self.total_cycles
            write_bw = self.memory_writes_completed / self.total_cycles
            lines.append(f"  Read bandwidth:          {read_bw:5.3f} ops/cycle")
            lines.append(f"  Write bandwidth:         {write_bw:5.3f} ops/cycle")
        
        # Per-port metrics
        lines.append("")
        lines.append("-" * 60)
        lines.append("PER-PORT ACTIVITY")
        lines.append("-" * 60)
        
        for i in range(self.num_ports):
            cmds = self.port_commands[i]
            resps = self.port_responses[i]
            lines.append(f"  Port {i}: {cmds} commands, {resps} responses")
        
        lines.append("")
        lines.append("=" * 60)
        
        return "\n".join(lines)
    
    def log_report(self):
        """Log the performance report."""
        logger.info(self.report())
        
    def get_summary(self) -> Dict:
        """Return metrics as a dictionary for programmatic access."""
        compute_estimate = max(0, self.values_reduced - 1) if self.reductions_completed > 0 else 0
        
        return {
            'total_cycles': self.total_cycles,
            'busy_cycles': self.busy_cycles,
            'memory_wait_cycles': self.memory_wait_cycles,
            'compute_cycles': compute_estimate,
            'reductions_completed': self.reductions_completed,
            'multicasts_completed': self.multicasts_completed,
            'values_reduced': self.values_reduced,
            'memory_reads': self.memory_reads_completed,
            'memory_writes': self.memory_writes_completed,
            'reduction_latencies': self.reduction_latencies.copy(),
            'multicast_latencies': self.multicast_latencies.copy(),
            'memory_latencies': self.memory_latencies.copy(),
            'avg_reduction_latency': sum(self.reduction_latencies) / max(1, len(self.reduction_latencies)),
            'avg_memory_latency': sum(self.memory_latencies) / max(1, len(self.memory_latencies)) if self.memory_latencies else 0,
        }
