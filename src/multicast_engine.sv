// Multicast Engine
// Broadcasts write data to multiple nodes simultaneously
//
// Used for STORE_MC commands where data needs to be written
// to all nodes in a multicast group.

import tswitch_pkg::*;

module multicast_engine #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // Multicast write request
    input  wire                  mc_valid,
    input  wire [ NUM_PORTS-1:0] mc_dst_mask,  // Which nodes to write
    input  wire [ADDR_WIDTH-1:0] mc_addr,      // Address to write
    input  wire [DATA_WIDTH-1:0] mc_data,      // Data to write
    input  wire [ TAG_WIDTH-1:0] mc_tag,
    input  wire [ PORT_BITS-1:0] mc_src_port,  // Original requester
    output wire                  mc_ready,

    // Write requests to port interfaces
    output wire [ NUM_PORTS-1:0] port_write_valid,
    output wire [ADDR_WIDTH-1:0] port_write_addr [NUM_PORTS-1:0],
    output wire [DATA_WIDTH-1:0] port_write_data [NUM_PORTS-1:0],
    input  wire [ NUM_PORTS-1:0] port_write_ready,

    // Write acknowledgments from ports
    input wire [NUM_PORTS-1:0] port_write_done,

    // Completion signal
    output wire                 mc_done,
    output wire [TAG_WIDTH-1:0] mc_done_tag,
    output wire [PORT_BITS-1:0] mc_done_src_port,

    // Status
    output wire busy
);

  // Local parameter for port index width
  localparam PORT_BITS = $clog2(NUM_PORTS);

  // State machine
  multicast_state_t                  state;

  // Request storage
  reg               [ NUM_PORTS-1:0] current_mask;
  reg               [ADDR_WIDTH-1:0] current_addr;
  reg               [DATA_WIDTH-1:0] current_data;
  reg               [ TAG_WIDTH-1:0] current_tag;
  reg               [ PORT_BITS-1:0] current_src_port;

  // Parallel issuer for write requests
  wire                               issuer_start;
  wire                               issuer_clear;
  wire                               issuer_issuing;
  wire                               all_issued;

  // Use input mask directly for issuer (before it's registered)
  wire              [ NUM_PORTS-1:0] issuer_mask = (state == MC_IDLE) ? mc_dst_mask : current_mask;

  parallel_issuer #(
      .NUM_PORTS(NUM_PORTS)
  ) u_issuer (
      .clk        (clk),
      .rst_n      (rst_n),
      .start      (issuer_start),
      .clear      (issuer_clear),
      .target_mask(issuer_mask),
      .port_valid (port_write_valid),
      .port_ready (port_write_ready),
      .issuing    (issuer_issuing),
      .all_issued (all_issued)
  );

  assign issuer_start = (state == MC_IDLE) && mc_valid;
  assign issuer_clear = (state == MC_DONE);

  // Track acknowledgments
  reg  [NUM_PORTS-1:0] acked_mask;

  // All writes acknowledged
  wire                 all_acked = (acked_mask == current_mask);

  // State transitions
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state            <= MC_IDLE;
      current_mask     <= '0;
      current_addr     <= '0;
      current_data     <= '0;
      current_tag      <= '0;
      current_src_port <= '0;
      acked_mask       <= '0;
    end else begin
      case (state)
        MC_IDLE: begin
          if (mc_valid && mc_ready) begin
            current_mask     <= mc_dst_mask;
            current_addr     <= mc_addr;
            current_data     <= mc_data;
            current_tag      <= mc_tag;
            current_src_port <= mc_src_port;
            acked_mask       <= '0;
            state            <= MC_WRITING;
          end
        end

        MC_WRITING: begin
          // Wait for parallel issuer to complete
          if (all_issued || !issuer_issuing) begin
            state <= MC_WAITING;
          end
        end

        MC_WAITING: begin
          // Collect acknowledgments
          for (int i = 0; i < NUM_PORTS; i++) begin
            if (current_mask[i] && port_write_done[i]) begin
              acked_mask[i] <= 1'b1;
            end
          end

          // Check if all writes are acknowledged
          if (all_acked || ((acked_mask | (current_mask & port_write_done)) == current_mask)) begin
            state <= MC_DONE;
          end
        end

        MC_DONE: begin
          // Single cycle to signal completion
          state <= MC_IDLE;
        end

        default: state <= MC_IDLE;
      endcase
    end
  end

  // Generate write addresses and data for each port
  genvar i;
  generate
    for (i = 0; i < NUM_PORTS; i = i + 1) begin : gen_write_data
      assign port_write_addr[i] = current_addr;
      assign port_write_data[i] = current_data;
    end
  endgenerate

  // Output signals
  assign mc_ready         = (state == MC_IDLE);
  assign mc_done          = (state == MC_DONE);
  assign mc_done_tag      = current_tag;
  assign mc_done_src_port = current_src_port;
  assign busy             = (state != MC_IDLE);

  // ==========================================================================
  // SVA Protocol Assertions (for formal verification and simulation debug)
  // ==========================================================================
`ifdef FORMAL
  // State machine should never be in undefined state
  assert property (@(posedge clk) disable iff (!rst_n)
    state inside {MC_IDLE, MC_WRITING, MC_WAITING, MC_DONE})
  else $error("State machine in undefined state");

  // mc_done only in MC_DONE state
  assert property (@(posedge clk) disable iff (!rst_n) mc_done |-> (state == MC_DONE))
  else $error("mc_done asserted outside MC_DONE");

  // mc_ready only in MC_IDLE state
  assert property (@(posedge clk) disable iff (!rst_n) mc_ready |-> (state == MC_IDLE))
  else $error("mc_ready asserted outside MC_IDLE");

  // Acked mask should only have bits set that are in current_mask
  assert property (@(posedge clk) disable iff (!rst_n) (acked_mask & ~current_mask) == '0)
  else $error("acked_mask has bits outside current_mask");

  // Mask must be non-zero when accepted
  assert property (@(posedge clk) disable iff (!rst_n)
    (mc_valid && mc_ready) |-> (mc_dst_mask != '0))
  else $warning("Zero mask request accepted");
`endif

endmodule
