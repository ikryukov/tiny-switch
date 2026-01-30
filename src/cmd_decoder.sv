// Command Decoder
// Arbitrates between commands from multiple ports and dispatches
// them to the appropriate engine (reduction or multicast)
//
// Uses round-robin arbitration to ensure fairness between ports

import tswitch_pkg::*;

module cmd_decoder #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // Commands from port interfaces
    input  wire [ NUM_PORTS-1:0] port_cmd_valid,
    input  wire [           2:0] port_cmd_type [NUM_PORTS-1:0],  // cmd_t
    input  wire [ADDR_WIDTH-1:0] port_cmd_addr [NUM_PORTS-1:0],
    input  wire [DATA_WIDTH-1:0] port_cmd_data [NUM_PORTS-1:0],
    output wire [ NUM_PORTS-1:0] port_cmd_ready,

    // To group table (lookup)
    output wire                  lookup_valid,
    output wire [ADDR_WIDTH-1:0] lookup_addr,
    input  wire                  lookup_ready,

    // From group table (result)
    input wire                     lookup_result_valid,
    input wire [    NUM_PORTS-1:0] lookup_member_mask,
    input wire [GROUP_ID_BITS-1:0] lookup_group_id,
    input wire                     lookup_is_multicast,

    // To read requester (for LOAD_REDUCE)
    output wire                  read_req_valid,
    output wire [ NUM_PORTS-1:0] read_req_mask,
    output wire [ADDR_WIDTH-1:0] read_req_addr,
    output wire [ TAG_WIDTH-1:0] read_req_tag,
    output wire [ PORT_BITS-1:0] read_req_src_port,
    input  wire                  read_req_ready,

    // To multicast engine (for STORE_MC)
    output wire                  mc_req_valid,
    output wire [ NUM_PORTS-1:0] mc_req_mask,
    output wire [ADDR_WIDTH-1:0] mc_req_addr,
    output wire [DATA_WIDTH-1:0] mc_req_data,
    output wire [ TAG_WIDTH-1:0] mc_req_tag,
    output wire [ PORT_BITS-1:0] mc_req_src_port,
    input  wire                  mc_req_ready,

    // Completion signals (to send responses back to ports)
    input wire                  reduce_done,
    input wire [DATA_WIDTH-1:0] reduce_result,
    input wire [ TAG_WIDTH-1:0] reduce_tag,
    input wire [ PORT_BITS-1:0] reduce_dst_port,

    input wire                 mc_done,
    input wire [TAG_WIDTH-1:0] mc_done_tag,
    input wire [PORT_BITS-1:0] mc_done_src_port,

    // Response to ports
    output wire [ NUM_PORTS-1:0] port_resp_valid,
    output wire [           1:0] port_resp_type [NUM_PORTS-1:0],  // resp_t
    output wire [DATA_WIDTH-1:0] port_resp_data [NUM_PORTS-1:0],
    input  wire [ NUM_PORTS-1:0] port_resp_ready,

    // Status
    output wire busy
);

  // Local parameter for port index width
  localparam PORT_BITS = $clog2(NUM_PORTS);

  // State machine
  decoder_state_t                  state;

  // Round-robin arbiter state
  reg             [ PORT_BITS-1:0] last_served;

  // Current request being processed
  reg             [ PORT_BITS-1:0] current_port;
  reg             [           2:0] current_cmd;
  reg             [ADDR_WIDTH-1:0] current_addr;
  reg             [DATA_WIDTH-1:0] current_data;
  reg             [ TAG_WIDTH-1:0] current_tag;

  // Tag counter for tracking requests
  reg             [ TAG_WIDTH-1:0] tag_counter;

  // Lookup result storage
  reg             [ NUM_PORTS-1:0] member_mask_reg;

  // Find next port with pending command (round-robin)
  wire            [ NUM_PORTS-1:0] pending = port_cmd_valid;
  wire                             any_pending = |pending;

  // Round-robin selection - find next pending port after last_served
  reg             [ PORT_BITS-1:0] next_port;

  always_comb begin
    next_port = last_served;  // Default to last served
    for (int i = 1; i <= NUM_PORTS; i = i + 1) begin
      automatic int idx = (last_served + i) % NUM_PORTS;
      if (pending[idx]) begin
        next_port = idx[PORT_BITS-1:0];
        break;
      end
    end
  end

  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state           <= DEC_IDLE;
      last_served     <= NUM_PORTS - 1;  // Start with port 0 next
      current_port    <= '0;
      current_cmd     <= CMD_NOP;
      current_addr    <= '0;
      current_data    <= '0;
      current_tag     <= '0;
      tag_counter     <= '0;
      member_mask_reg <= '0;
    end else begin
      case (state)
        DEC_IDLE: begin
          if (any_pending) begin
            current_port <= next_port;
            current_cmd  <= port_cmd_type[next_port];
            current_addr <= port_cmd_addr[next_port];
            current_data <= port_cmd_data[next_port];
            current_tag  <= tag_counter;
            tag_counter  <= tag_counter + 1'b1;
            last_served  <= next_port;
            state        <= DEC_DECODE;
          end
        end

        DEC_DECODE: begin
          // Check command type and proceed
          case (current_cmd)
            CMD_LOAD_REDUCE, CMD_STORE_MC: begin
              // Need group table lookup for multicast operations
              state <= DEC_LOOKUP;
            end
            CMD_READ, CMD_WRITE: begin
              // Passthrough operations: target only the requesting port's memory
              member_mask_reg <= ({{(NUM_PORTS - 1) {1'b0}}, 1'b1} << current_port);
              state           <= DEC_DISPATCH;
            end
            CMD_NOP: begin
              // No-op, go back to idle
              state <= DEC_IDLE;
            end
            default: begin
              state <= DEC_IDLE;
            end
          endcase
        end

        DEC_LOOKUP: begin
          if (lookup_valid && lookup_ready) begin
            state <= DEC_WAIT;  // Wait for lookup result
          end
        end

        DEC_WAIT: begin
          if (lookup_result_valid) begin
            member_mask_reg <= lookup_member_mask;
            state           <= DEC_DISPATCH;
          end
        end

        DEC_DISPATCH: begin
          // Dispatch to appropriate engine
          case (current_cmd)
            CMD_LOAD_REDUCE, CMD_READ: begin
              // Both use read requester (READ is single-node, LOAD_REDUCE is multi-node)
              if (read_req_valid && read_req_ready) begin
                state <= DEC_RESPOND;
              end
            end
            CMD_STORE_MC, CMD_WRITE: begin
              // Both use multicast engine (WRITE is single-node, STORE_MC is multi-node)
              if (mc_req_valid && mc_req_ready) begin
                state <= DEC_RESPOND;
              end
            end
            default: begin
              state <= DEC_IDLE;
            end
          endcase
        end

        DEC_RESPOND: begin
          // Wait for operation completion and send response
          if (((current_cmd == CMD_LOAD_REDUCE || current_cmd == CMD_READ) && reduce_done) ||
              ((current_cmd == CMD_STORE_MC || current_cmd == CMD_WRITE) && mc_done)) begin
            state <= DEC_IDLE;
          end
        end

        default: state <= DEC_IDLE;
      endcase
    end
  end

  // Port ready signals (only accept from selected port in IDLE)
  genvar i;
  generate
    for (i = 0; i < NUM_PORTS; i = i + 1) begin : gen_port_ready
      assign port_cmd_ready[i] = (state == DEC_IDLE) && any_pending && (next_port == i);
    end
  endgenerate

  // Group table lookup
  assign lookup_valid = (state == DEC_LOOKUP);
  assign lookup_addr = current_addr;

  // Read requester interface (used by LOAD_REDUCE and READ)
  assign read_req_valid    = (state == DEC_DISPATCH) && (current_cmd == CMD_LOAD_REDUCE || current_cmd == CMD_READ);
  assign read_req_mask = member_mask_reg;
  assign read_req_addr = current_addr;
  assign read_req_tag = current_tag;
  assign read_req_src_port = current_port;

  // Multicast engine interface (used by STORE_MC and WRITE)
  assign mc_req_valid    = (state == DEC_DISPATCH) && (current_cmd == CMD_STORE_MC || current_cmd == CMD_WRITE);
  assign mc_req_mask = member_mask_reg;
  assign mc_req_addr = current_addr;
  assign mc_req_data = current_data;
  assign mc_req_tag = current_tag;
  assign mc_req_src_port = current_port;

  // Response to ports
  generate
    for (i = 0; i < NUM_PORTS; i = i + 1) begin : gen_port_resp
      assign port_resp_valid[i] = (state == DEC_RESPOND) &&
                                  ((reduce_done && reduce_dst_port == i) ||
                                   (mc_done && mc_done_src_port == i));
      // RESP_DATA for read operations, RESP_ACK for write operations
      assign port_resp_type[i] = (current_cmd == CMD_LOAD_REDUCE || current_cmd == CMD_READ) ? RESP_DATA : RESP_ACK;
      assign port_resp_data[i] = reduce_result;
    end
  endgenerate

  // Status
  assign busy = (state != DEC_IDLE);

  // ==========================================================================
  // SVA Protocol Assertions (for formal verification and simulation debug)
  // ==========================================================================
`ifdef FORMAL
  // Valid/ready protocol: valid must not drop until ready
  property valid_stable_until_ready(valid, ready);
    @(posedge clk) disable iff (!rst_n) (valid && !ready) |=> valid;
  endproperty

  assert property (valid_stable_until_ready(read_req_valid, read_req_ready))
  else $error("read_req_valid dropped before ready");
  assert property (valid_stable_until_ready(mc_req_valid, mc_req_ready))
  else $error("mc_req_valid dropped before ready");
  assert property (valid_stable_until_ready(lookup_valid, lookup_ready))
  else $error("lookup_valid dropped before ready");

  // State machine should never be in undefined state
  assert property (@(posedge clk) disable iff (!rst_n)
    state inside {DEC_IDLE, DEC_DECODE, DEC_LOOKUP, DEC_WAIT, DEC_DISPATCH, DEC_RESPOND})
  else $error("State machine in undefined state");

  // Only one port should get ready at a time
  assert property (@(posedge clk) disable iff (!rst_n) $onehot0(port_cmd_ready))
  else $error("Multiple ports ready simultaneously");

  // Response should only be valid when in DEC_RESPOND state
  assert property (@(posedge clk) disable iff (!rst_n) |port_resp_valid |-> (state == DEC_RESPOND))
  else $error("Response valid outside DEC_RESPOND state");
`endif

endmodule
