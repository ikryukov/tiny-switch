// Read Requester
// Issues parallel READ requests to all nodes in a multicast group
//
// When a LOAD_REDUCE command is processed, this module sends
// read requests to all participating nodes simultaneously.

import tswitch_pkg::*;

module read_requester #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // Request from command decoder
    input  wire                  req_valid,
    input  wire [ NUM_PORTS-1:0] req_node_mask,  // Which nodes to read
    input  wire [ADDR_WIDTH-1:0] req_addr,       // Address to read
    input  wire [ TAG_WIDTH-1:0] req_tag,        // Request tag
    input  wire [ PORT_BITS-1:0] req_src_port,   // Original requester
    output wire                  req_ready,

    // Read requests to port interfaces (active-high, one per port)
    output wire [ NUM_PORTS-1:0] port_read_valid,
    output wire [ADDR_WIDTH-1:0] port_read_addr [NUM_PORTS-1:0],
    input  wire [ NUM_PORTS-1:0] port_read_ready,

    // To response collector (track pending reads)
    output wire                 pending_valid,
    output wire [NUM_PORTS-1:0] pending_mask,
    output wire [TAG_WIDTH-1:0] pending_tag,
    output wire [PORT_BITS-1:0] pending_src_port,
    input  wire                 pending_ready,

    // Status
    output wire busy
);

  // Local parameter for port index width
  localparam PORT_BITS = $clog2(NUM_PORTS);

  // State machine
  requester_state_t state;

  // Request storage
  reg [NUM_PORTS-1:0] current_mask;
  reg [ADDR_WIDTH-1:0] current_addr;
  reg [TAG_WIDTH-1:0] current_tag;
  reg [PORT_BITS-1:0] current_src_port;

  // Parallel issuer instance
  wire issuer_start;
  wire issuer_clear;
  wire issuer_issuing;
  wire all_issued;

  // Use input mask directly for issuer (before it's registered)
  wire [NUM_PORTS-1:0] issuer_mask = (state == REQ_IDLE) ? req_node_mask : current_mask;

  parallel_issuer #(
      .NUM_PORTS(NUM_PORTS)
  ) u_issuer (
      .clk        (clk),
      .rst_n      (rst_n),
      .start      (issuer_start),
      .clear      (issuer_clear),
      .target_mask(issuer_mask),
      .port_valid (port_read_valid),
      .port_ready (port_read_ready),
      .issuing    (issuer_issuing),
      .all_issued (all_issued)
  );

  assign issuer_start = (state == REQ_IDLE) && req_valid;
  assign issuer_clear = (state == REQ_DONE);

  // State transitions
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state            <= REQ_IDLE;
      current_mask     <= '0;
      current_addr     <= '0;
      current_tag      <= '0;
      current_src_port <= '0;
    end else begin
      case (state)
        REQ_IDLE: begin
          if (req_valid && req_ready) begin
            current_mask     <= req_node_mask;
            current_addr     <= req_addr;
            current_tag      <= req_tag;
            current_src_port <= req_src_port;
            state            <= REQ_ISSUING;
          end
        end

        REQ_ISSUING: begin
          // Wait for parallel issuer to complete
          if (all_issued || !issuer_issuing) begin
            state <= REQ_WAITING;
          end
        end

        REQ_WAITING: begin
          // Wait for pending to be acknowledged by response collector
          if (pending_valid && pending_ready) begin
            state <= REQ_DONE;
          end
        end

        REQ_DONE: begin
          // Single cycle to signal completion
          state <= REQ_IDLE;
        end

        default: state <= REQ_IDLE;
      endcase
    end
  end

  // Generate read addresses for each port
  genvar i;
  generate
    for (i = 0; i < NUM_PORTS; i = i + 1) begin : gen_read_addr
      assign port_read_addr[i] = current_addr;
    end
  endgenerate

  // Output to response collector
  assign pending_valid    = (state == REQ_WAITING);
  assign pending_mask     = current_mask;
  assign pending_tag      = current_tag;
  assign pending_src_port = current_src_port;

  // Control signals
  assign req_ready        = (state == REQ_IDLE);
  assign busy             = (state != REQ_IDLE);

  // ==========================================================================
  // SVA Protocol Assertions (for formal verification and simulation debug)
  // ==========================================================================
`ifdef FORMAL
  // State machine should never be in undefined state
  assert property (@(posedge clk) disable iff (!rst_n)
    state inside {REQ_IDLE, REQ_ISSUING, REQ_WAITING, REQ_DONE})
  else $error("State machine in undefined state");

  // pending_valid only in REQ_WAITING state
  assert property (@(posedge clk) disable iff (!rst_n) pending_valid |-> (state == REQ_WAITING))
  else $error("pending_valid asserted outside REQ_WAITING");

  // req_ready only in REQ_IDLE state
  assert property (@(posedge clk) disable iff (!rst_n) req_ready |-> (state == REQ_IDLE))
  else $error("req_ready asserted outside REQ_IDLE");

  // Mask must be non-zero when accepted
  assert property (@(posedge clk) disable iff (!rst_n)
    (req_valid && req_ready) |-> (req_node_mask != '0))
  else $warning("Zero mask request accepted");
`endif

endmodule
