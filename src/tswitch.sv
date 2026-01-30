// tiny-switch Top Level Module
// In-network reduction switch with BFloat16 SUM operation
//
// Features:
// - Parameterized number of node ports (default 4)
// - LOAD_REDUCE: Read from all nodes, sum, return to requester
// - STORE_MC: Write to all nodes (multicast)
// - BFloat16 data type

import tswitch_pkg::*;

module tswitch #(
    parameter NUM_PORTS = 4
) (
    input wire clk,
    input wire rst_n,

    // =============== Node Command Interface (from nodes) ===============
    input  wire [NUM_PORTS-1:0]                 node_cmd_valid,
    input  wire [NUM_PORTS-1:0][           2:0] node_cmd,
    input  wire [NUM_PORTS-1:0][ADDR_WIDTH-1:0] node_addr,
    input  wire [NUM_PORTS-1:0][DATA_WIDTH-1:0] node_wdata,
    output wire [NUM_PORTS-1:0]                 node_cmd_ready,

    // =============== Node Response Interface (to nodes) ===============
    output wire [NUM_PORTS-1:0]                 node_resp_valid,
    output wire [NUM_PORTS-1:0][           1:0] node_resp_type,
    output wire [NUM_PORTS-1:0][DATA_WIDTH-1:0] node_resp_data,
    input  wire [NUM_PORTS-1:0]                 node_resp_ready,

    // =============== Node Memory Read Interface (switch reads from node memory) ===============
    output wire [NUM_PORTS-1:0]                 node_mem_read_valid,
    output wire [NUM_PORTS-1:0][ADDR_WIDTH-1:0] node_mem_read_addr,
    input  wire [NUM_PORTS-1:0]                 node_mem_read_data_valid,
    input  wire [NUM_PORTS-1:0][DATA_WIDTH-1:0] node_mem_read_data,

    // =============== Node Memory Write Interface (switch writes to node memory) ===============
    output wire [NUM_PORTS-1:0]                 node_mem_write_valid,
    output wire [NUM_PORTS-1:0][ADDR_WIDTH-1:0] node_mem_write_addr,
    output wire [NUM_PORTS-1:0][DATA_WIDTH-1:0] node_mem_write_data,
    input  wire [NUM_PORTS-1:0]                 node_mem_write_done,

    // =============== Status ===============
    output wire busy
);

  // Local parameter for port index width
  localparam PORT_BITS = $clog2(NUM_PORTS);

  // =============== Internal Wires ===============

  // Port interface to decoder
  wire [    NUM_PORTS-1:0] pi_cmd_valid;
  wire [              2:0] pi_cmd_type          [NUM_PORTS-1:0];
  wire [   ADDR_WIDTH-1:0] pi_cmd_addr          [NUM_PORTS-1:0];
  wire [   DATA_WIDTH-1:0] pi_cmd_data          [NUM_PORTS-1:0];
  wire [    NUM_PORTS-1:0] pi_cmd_ready;

  // Decoder to port interface (responses)
  wire [    NUM_PORTS-1:0] dec_resp_valid;
  wire [              1:0] dec_resp_type        [NUM_PORTS-1:0];
  wire [   DATA_WIDTH-1:0] dec_resp_data        [NUM_PORTS-1:0];
  wire [    NUM_PORTS-1:0] dec_resp_ready;

  // Read requester to ports
  wire [    NUM_PORTS-1:0] rr_read_valid;
  wire [   ADDR_WIDTH-1:0] rr_read_addr         [NUM_PORTS-1:0];
  wire [    NUM_PORTS-1:0] rr_read_ready;

  // Port read responses to collector
  wire [    NUM_PORTS-1:0] port_read_resp_valid;
  wire [   DATA_WIDTH-1:0] port_read_resp_data  [NUM_PORTS-1:0];
  wire [    NUM_PORTS-1:0] port_read_resp_ready;

  // Multicast to ports
  wire [    NUM_PORTS-1:0] mc_write_valid;
  wire [   ADDR_WIDTH-1:0] mc_write_addr        [NUM_PORTS-1:0];
  wire [   DATA_WIDTH-1:0] mc_write_data        [NUM_PORTS-1:0];
  wire [    NUM_PORTS-1:0] mc_write_ready;
  wire [    NUM_PORTS-1:0] mc_write_done;

  // Group table
  wire                     gt_lookup_valid;
  wire [   ADDR_WIDTH-1:0] gt_lookup_addr;
  wire                     gt_lookup_ready;
  wire                     gt_result_valid;
  wire [    NUM_PORTS-1:0] gt_member_mask;
  wire [GROUP_ID_BITS-1:0] gt_group_id;
  wire                     gt_is_multicast;

  // Read requester
  wire                     rr_req_valid;
  wire [    NUM_PORTS-1:0] rr_req_mask;
  wire [   ADDR_WIDTH-1:0] rr_req_addr;
  wire [    TAG_WIDTH-1:0] rr_req_tag;
  wire [    PORT_BITS-1:0] rr_req_src_port;
  wire                     rr_req_ready;
  wire                     rr_pending_valid;
  wire [    NUM_PORTS-1:0] rr_pending_mask;
  wire [    TAG_WIDTH-1:0] rr_pending_tag;
  wire [    PORT_BITS-1:0] rr_pending_src_port;
  wire                     rr_pending_ready;

  // Response collector to reduction engine
  wire                     rc_value_valid;
  wire [   DATA_WIDTH-1:0] rc_value_data;
  wire [    TAG_WIDTH-1:0] rc_value_tag;
  wire                     rc_value_last;
  wire [    PORT_BITS-1:0] rc_value_src_port;
  wire                     rc_value_ready;

  // Reduction engine output
  wire                     re_result_valid;
  wire [   DATA_WIDTH-1:0] re_result_data;
  wire [    TAG_WIDTH-1:0] re_result_tag;
  wire [    PORT_BITS-1:0] re_result_dst_port;
  wire                     re_result_ready;

  // Multicast engine
  wire                     mc_req_valid;
  wire [    NUM_PORTS-1:0] mc_req_mask;
  wire [   ADDR_WIDTH-1:0] mc_req_addr;
  wire [   DATA_WIDTH-1:0] mc_req_data;
  wire [    TAG_WIDTH-1:0] mc_req_tag;
  wire [    PORT_BITS-1:0] mc_req_src_port;
  wire                     mc_req_ready;
  wire                     mc_done;
  wire [    TAG_WIDTH-1:0] mc_done_tag;
  wire [    PORT_BITS-1:0] mc_done_src_port;

  // Module busy signals
  wire                     decoder_busy;
  wire                     rr_busy;
  wire                     rc_busy;
  wire                     re_busy;
  wire                     mc_busy;

  // =============== Port Interface Mapping ===============
  genvar p;
  generate
    for (p = 0; p < NUM_PORTS; p = p + 1) begin : gen_port_map
      // Command interface
      assign pi_cmd_valid[p]         = node_cmd_valid[p];
      assign pi_cmd_type[p]          = node_cmd[p];
      assign pi_cmd_addr[p]          = node_addr[p];
      assign pi_cmd_data[p]          = node_wdata[p];
      assign node_cmd_ready[p]       = pi_cmd_ready[p];

      // Response interface
      assign node_resp_valid[p]      = dec_resp_valid[p];
      assign node_resp_type[p]       = dec_resp_type[p];
      assign node_resp_data[p]       = dec_resp_data[p];
      assign dec_resp_ready[p]       = node_resp_ready[p];

      // Memory read interface
      assign node_mem_read_valid[p]  = rr_read_valid[p];
      assign node_mem_read_addr[p]   = rr_read_addr[p];
      assign rr_read_ready[p]        = 1'b1;  // Always ready to accept reads
      assign port_read_resp_valid[p] = node_mem_read_data_valid[p];
      assign port_read_resp_data[p]  = node_mem_read_data[p];

      // Memory write interface
      assign node_mem_write_valid[p] = mc_write_valid[p];
      assign node_mem_write_addr[p]  = mc_write_addr[p];
      assign node_mem_write_data[p]  = mc_write_data[p];
      assign mc_write_ready[p]       = 1'b1;  // Always ready
      assign mc_write_done[p]        = node_mem_write_done[p];
    end
  endgenerate

  // =============== Group Table ===============
  group_table #(
      .NUM_PORTS(NUM_PORTS)
  ) u_group_table (
      .clk              (clk),
      .rst_n            (rst_n),
      .lookup_valid     (gt_lookup_valid),
      .lookup_addr      (gt_lookup_addr),
      .lookup_ready     (gt_lookup_ready),
      .result_valid     (gt_result_valid),
      .member_mask      (gt_member_mask),
      .group_id         (gt_group_id),
      .is_multicast_addr(gt_is_multicast),
      .cfg_write        (1'b0),
      .cfg_group_id     ({GROUP_ID_BITS{1'b0}}),
      .cfg_base_addr    ({ADDR_WIDTH{1'b0}}),
      .cfg_addr_mask    ({ADDR_WIDTH{1'b0}}),
      .cfg_member_mask  ({NUM_PORTS{1'b0}})
  );

  // =============== Command Decoder ===============
  cmd_decoder #(
      .NUM_PORTS(NUM_PORTS)
  ) u_cmd_decoder (
      .clk                (clk),
      .rst_n              (rst_n),
      .port_cmd_valid     (pi_cmd_valid),
      .port_cmd_type      (pi_cmd_type),
      .port_cmd_addr      (pi_cmd_addr),
      .port_cmd_data      (pi_cmd_data),
      .port_cmd_ready     (pi_cmd_ready),
      .lookup_valid       (gt_lookup_valid),
      .lookup_addr        (gt_lookup_addr),
      .lookup_ready       (gt_lookup_ready),
      .lookup_result_valid(gt_result_valid),
      .lookup_member_mask (gt_member_mask),
      .lookup_group_id    (gt_group_id),
      .lookup_is_multicast(gt_is_multicast),
      .read_req_valid     (rr_req_valid),
      .read_req_mask      (rr_req_mask),
      .read_req_addr      (rr_req_addr),
      .read_req_tag       (rr_req_tag),
      .read_req_src_port  (rr_req_src_port),
      .read_req_ready     (rr_req_ready),
      .mc_req_valid       (mc_req_valid),
      .mc_req_mask        (mc_req_mask),
      .mc_req_addr        (mc_req_addr),
      .mc_req_data        (mc_req_data),
      .mc_req_tag         (mc_req_tag),
      .mc_req_src_port    (mc_req_src_port),
      .mc_req_ready       (mc_req_ready),
      .reduce_done        (re_result_valid),
      .reduce_result      (re_result_data),
      .reduce_tag         (re_result_tag),
      .reduce_dst_port    (re_result_dst_port),
      .mc_done            (mc_done),
      .mc_done_tag        (mc_done_tag),
      .mc_done_src_port   (mc_done_src_port),
      .port_resp_valid    (dec_resp_valid),
      .port_resp_type     (dec_resp_type),
      .port_resp_data     (dec_resp_data),
      .port_resp_ready    (dec_resp_ready),
      .busy               (decoder_busy)
  );

  // =============== Read Requester ===============
  read_requester #(
      .NUM_PORTS(NUM_PORTS)
  ) u_read_requester (
      .clk             (clk),
      .rst_n           (rst_n),
      .req_valid       (rr_req_valid),
      .req_node_mask   (rr_req_mask),
      .req_addr        (rr_req_addr),
      .req_tag         (rr_req_tag),
      .req_src_port    (rr_req_src_port),
      .req_ready       (rr_req_ready),
      .port_read_valid (rr_read_valid),
      .port_read_addr  (rr_read_addr),
      .port_read_ready (rr_read_ready),
      .pending_valid   (rr_pending_valid),
      .pending_mask    (rr_pending_mask),
      .pending_tag     (rr_pending_tag),
      .pending_src_port(rr_pending_src_port),
      .pending_ready   (rr_pending_ready),
      .busy            (rr_busy)
  );

  // =============== Response Collector ===============
  response_collector #(
      .NUM_PORTS(NUM_PORTS)
  ) u_response_collector (
      .clk             (clk),
      .rst_n           (rst_n),
      .pending_valid   (rr_pending_valid),
      .pending_mask    (rr_pending_mask),
      .pending_tag     (rr_pending_tag),
      .pending_src_port(rr_pending_src_port),
      .pending_ready   (rr_pending_ready),
      .port_data_valid (port_read_resp_valid),
      .port_data       (port_read_resp_data),
      .port_data_ready (port_read_resp_ready),
      .value_valid     (rc_value_valid),
      .value_data      (rc_value_data),
      .value_tag       (rc_value_tag),
      .value_last      (rc_value_last),
      .value_src_port  (rc_value_src_port),
      .value_ready     (rc_value_ready),
      .busy            (rc_busy)
  );

  // =============== Reduction Engine ===============
  reduction_engine #(
      .NUM_PORTS(NUM_PORTS)
  ) u_reduction_engine (
      .clk            (clk),
      .rst_n          (rst_n),
      .value_valid    (rc_value_valid),
      .value_data     (rc_value_data),
      .value_tag      (rc_value_tag),
      .value_last     (rc_value_last),
      .value_src_port (rc_value_src_port),
      .value_ready    (rc_value_ready),
      .result_valid   (re_result_valid),
      .result_data    (re_result_data),
      .result_tag     (re_result_tag),
      .result_dst_port(re_result_dst_port),
      .result_ready   (1'b1),                // Always ready to accept result
      .busy           (re_busy)
  );

  // =============== Multicast Engine ===============
  multicast_engine #(
      .NUM_PORTS(NUM_PORTS)
  ) u_multicast_engine (
      .clk             (clk),
      .rst_n           (rst_n),
      .mc_valid        (mc_req_valid),
      .mc_dst_mask     (mc_req_mask),
      .mc_addr         (mc_req_addr),
      .mc_data         (mc_req_data),
      .mc_tag          (mc_req_tag),
      .mc_src_port     (mc_req_src_port),
      .mc_ready        (mc_req_ready),
      .port_write_valid(mc_write_valid),
      .port_write_addr (mc_write_addr),
      .port_write_data (mc_write_data),
      .port_write_ready(mc_write_ready),
      .port_write_done (mc_write_done),
      .mc_done         (mc_done),
      .mc_done_tag     (mc_done_tag),
      .mc_done_src_port(mc_done_src_port),
      .busy            (mc_busy)
  );

  // =============== Overall Busy Signal ===============
  assign busy = decoder_busy | rr_busy | rc_busy | re_busy | mc_busy;

endmodule
