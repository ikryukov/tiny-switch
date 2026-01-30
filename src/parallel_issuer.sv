// Parallel Issuer
// Common module for issuing requests to multiple ports in parallel
//
// Used by both read_requester (for reads) and multicast_engine (for writes)
// to eliminate duplicated parallel-issue logic.
//
// Tracks which ports have accepted requests and signals when all are done.

import tswitch_pkg::*;

module parallel_issuer #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // Control
    input wire                 start,       // Pulse to begin issuing
    input wire                 clear,       // Clear state (go back to idle)
    input wire [NUM_PORTS-1:0] target_mask, // Which ports to issue to

    // Per-port handshake
    output wire [NUM_PORTS-1:0] port_valid,  // Request valid to each port
    input  wire [NUM_PORTS-1:0] port_ready,  // Ready from each port

    // Status
    output wire issuing,    // Currently issuing requests
    output wire all_issued  // All targeted ports have accepted
);

  // State: are we currently issuing?
  logic active;

  // Track which ports have accepted
  logic [NUM_PORTS-1:0] issued_mask;

  // Current target mask (latched on start)
  logic [NUM_PORTS-1:0] current_mask;

  // All issued when issued_mask covers current_mask
  assign all_issued = active && (issued_mask == current_mask);
  assign issuing = active;

  // Generate valid for ports that need issuing
  genvar i;
  generate
    for (i = 0; i < NUM_PORTS; i = i + 1) begin : gen_valid
      assign port_valid[i] = active && current_mask[i] && !issued_mask[i];
    end
  endgenerate

  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      active       <= 1'b0;
      issued_mask  <= '0;
      current_mask <= '0;
    end else begin
      if (clear) begin
        // Clear state
        active      <= 1'b0;
        issued_mask <= '0;
      end else if (start && !active) begin
        // Begin issuing
        active       <= 1'b1;
        current_mask <= target_mask;
        issued_mask  <= '0;
      end else if (active) begin
        // Update issued mask as ports accept
        for (int j = 0; j < NUM_PORTS; j++) begin
          if (current_mask[j] && port_ready[j] && !issued_mask[j]) begin
            issued_mask[j] <= 1'b1;
          end
        end

        // Check if done (including same-cycle completions)
        if ((issued_mask | (current_mask & port_ready)) == current_mask) begin
          active <= 1'b0;
        end
      end
    end
  end

  // ==========================================================================
  // SVA Protocol Assertions (for formal verification and simulation debug)
  // ==========================================================================
`ifdef FORMAL
  // issued_mask should only have bits set that are in current_mask
  assert property (@(posedge clk) disable iff (!rst_n) (issued_mask & ~current_mask) == '0)
  else $error("issued_mask has bits outside current_mask");

  // port_valid should only be set for ports in current_mask that haven't been issued
  assert property (@(posedge clk) disable iff (!rst_n) (port_valid & ~current_mask) == '0)
  else $error("port_valid set for port not in current_mask");

  // all_issued implies active
  assert property (@(posedge clk) disable iff (!rst_n) all_issued |-> active)
  else $error("all_issued without active");
`endif

endmodule
