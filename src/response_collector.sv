// Response Collector
// Collects READ responses from port interfaces and feeds them to the reduction engine
//
// Tracks which responses are still pending and signals when the last
// response for a reduction has been received.

import tswitch_pkg::*;

module response_collector #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // From read requester (what we're waiting for)
    input  wire                 pending_valid,
    input  wire [NUM_PORTS-1:0] pending_mask,
    input  wire [TAG_WIDTH-1:0] pending_tag,
    input  wire [PORT_BITS-1:0] pending_src_port,
    output wire                 pending_ready,

    // From port interfaces (responses)
    input  wire [ NUM_PORTS-1:0] port_data_valid,
    input  wire [DATA_WIDTH-1:0] port_data      [NUM_PORTS-1:0],
    output wire [ NUM_PORTS-1:0] port_data_ready,

    // To reduction engine (one value at a time)
    output wire                  value_valid,
    output wire [DATA_WIDTH-1:0] value_data,
    output wire [ TAG_WIDTH-1:0] value_tag,
    output wire                  value_last,      // Last value for this reduction
    output wire [ PORT_BITS-1:0] value_src_port,
    input  wire                  value_ready,

    // Status
    output wire busy
);

  // Local parameter for port index width
  localparam PORT_BITS = $clog2(NUM_PORTS);

  // State
  reg                   collecting;
  reg  [ NUM_PORTS-1:0] expected_mask;
  reg  [ NUM_PORTS-1:0] received_mask;
  reg  [ TAG_WIDTH-1:0] current_tag;
  reg  [ PORT_BITS-1:0] current_src_port;

  // Round-robin state for fair port selection
  reg  [ PORT_BITS-1:0] last_sent;

  // Buffer for incoming data (one per port)
  reg  [DATA_WIDTH-1:0] data_buffer                               [NUM_PORTS-1:0];
  reg  [ NUM_PORTS-1:0] data_buffered;

  // Find next port with buffered data to send to reduction engine
  wire [ NUM_PORTS-1:0] sendable = data_buffered & ~received_mask;
  wire                  any_sendable = |sendable;

  // Round-robin select next value to send (fair scheduling)
  reg  [ PORT_BITS-1:0] next_port;
  always_comb begin
    next_port = '0;
    for (int i = 1; i <= NUM_PORTS; i++) begin
      automatic int idx = (last_sent + i) % NUM_PORTS;
      if (sendable[idx]) begin
        next_port = idx[PORT_BITS-1:0];
        break;
      end
    end
  end

  // Check if this is the last value
  wire [NUM_PORTS-1:0] new_received = received_mask | ({{(NUM_PORTS - 1) {1'b0}}, 1'b1} << next_port);
  wire is_last = (new_received == expected_mask);

  // Accept pending request when not busy
  assign pending_ready = !collecting;

  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      collecting       <= 1'b0;
      expected_mask    <= '0;
      received_mask    <= '0;
      current_tag      <= '0;
      current_src_port <= '0;
      last_sent        <= NUM_PORTS - 1;  // Start with port 0 next
      data_buffered    <= '0;
      for (int i = 0; i < NUM_PORTS; i++) begin
        data_buffer[i] <= '0;
      end
    end else begin
      // Accept new pending request
      if (pending_valid && pending_ready) begin
        collecting       <= 1'b1;
        expected_mask    <= pending_mask;
        received_mask    <= '0;
        current_tag      <= pending_tag;
        current_src_port <= pending_src_port;
        data_buffered    <= '0;
      end

      // Buffer incoming data from ports
      for (int i = 0; i < NUM_PORTS; i++) begin
        if (port_data_valid[i] && port_data_ready[i] && collecting && expected_mask[i]) begin
          data_buffer[i]   <= port_data[i];
          data_buffered[i] <= 1'b1;
        end
      end

      // Send data to reduction engine
      if (value_valid && value_ready) begin
        received_mask[next_port] <= 1'b1;
        data_buffered[next_port] <= 1'b0;
        last_sent                <= next_port;  // Update round-robin state

        // Check if all done
        if (is_last) begin
          collecting <= 1'b0;
        end
      end
    end
  end

  // Accept data from ports when collecting and port is expected
  genvar i;
  generate
    for (i = 0; i < NUM_PORTS; i = i + 1) begin : gen_ready
      assign port_data_ready[i] = collecting && expected_mask[i] && !data_buffered[i];
    end
  endgenerate

  // Output to reduction engine
  assign value_valid    = collecting && any_sendable;
  assign value_data     = data_buffer[next_port];
  assign value_tag      = current_tag;
  assign value_last     = is_last;
  assign value_src_port = current_src_port;

  // Status
  assign busy           = collecting;

endmodule
