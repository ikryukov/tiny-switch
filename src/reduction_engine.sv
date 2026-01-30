// Reduction Engine
// Accumulates BFloat16 values using SUM operation
//
// Receives values one at a time from the response collector,
// accumulates them using the BF16 adder, and signals when
// the final result is ready.

import tswitch_pkg::*;

module reduction_engine #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // From response collector (values to accumulate)
    input  wire                  value_valid,
    input  wire [DATA_WIDTH-1:0] value_data,      // BFloat16 value
    input  wire [ TAG_WIDTH-1:0] value_tag,       // Request tag
    input  wire                  value_last,      // Last value for this reduction
    input  wire [ PORT_BITS-1:0] value_src_port,  // Return result to this port
    output wire                  value_ready,

    // Result output
    output wire                  result_valid,
    output wire [DATA_WIDTH-1:0] result_data,      // BFloat16 sum
    output wire [ TAG_WIDTH-1:0] result_tag,
    output wire [ PORT_BITS-1:0] result_dst_port,
    input  wire                  result_ready,

    // Status
    output wire busy
);

  // Local parameter for port index width
  localparam PORT_BITS = $clog2(NUM_PORTS);

  // Simplified state machine: IDLE -> REDUCING -> DONE
  typedef enum logic [1:0] {
    S_IDLE     = 2'b00,
    S_REDUCING = 2'b01,
    S_DONE     = 2'b10
  } state_t;

  state_t                  state;

  // Accumulator register
  reg     [DATA_WIDTH-1:0] accumulator;
  reg     [ TAG_WIDTH-1:0] current_tag;
  reg     [ PORT_BITS-1:0] current_src_port;

  // BFloat16 adder instance
  wire    [DATA_WIDTH-1:0] sum_out;
  bf16_adder adder (
      .a  (accumulator),
      .b  (value_data),
      .sum(sum_out)
  );

  // State and accumulator update
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state            <= S_IDLE;
      accumulator      <= 16'h0000;
      current_tag      <= '0;
      current_src_port <= '0;
    end else begin
      case (state)
        S_IDLE: begin
          if (value_valid) begin
            // First value of a new reduction
            accumulator      <= value_data;
            current_tag      <= value_tag;
            current_src_port <= value_src_port;

            if (value_last) begin
              // Only one value in reduction
              state <= S_DONE;
            end else begin
              state <= S_REDUCING;
            end
          end
        end

        S_REDUCING: begin
          if (value_valid) begin
            // Accumulate: result = accumulator + value_data
            accumulator <= sum_out;

            if (value_last) begin
              state <= S_DONE;
            end
            // Otherwise stay in S_REDUCING for more values
          end
        end

        S_DONE: begin
          if (result_ready) begin
            // Reset for next reduction
            state       <= S_IDLE;
            accumulator <= 16'h0000;
          end
        end

        default: state <= S_IDLE;
      endcase
    end
  end

  // Output assignments
  // Ready to accept values in IDLE or REDUCING states
  assign value_ready     = (state == S_IDLE) || (state == S_REDUCING);
  assign result_valid    = (state == S_DONE);
  assign result_data     = accumulator;
  assign result_tag      = current_tag;
  assign result_dst_port = current_src_port;
  assign busy            = (state != S_IDLE);

endmodule
