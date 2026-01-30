// Group Table
// Maps multicast addresses to node membership
//
// When a LOAD_REDUCE or STORE_MC command arrives, the group table
// is consulted to determine which nodes should participate.
//
// Default configuration:
//   Address 0x1000_0000 - 0x1FFF_FFFF: All nodes (mask = all 1s)
//   Address 0x2000_0000 - 0x2FFF_FFFF: Lower half nodes
//   Address 0x3000_0000 - 0x3FFF_FFFF: Upper half nodes
//   Other addresses: Single node (based on address bits)

import tswitch_pkg::*;

module group_table #(
    parameter NUM_PORTS = 4,
    // Default group configurations (can be overridden at instantiation)
    parameter [31:0] GROUP0_BASE = 32'h1000_0000,  // All nodes
    parameter [31:0] GROUP0_MASK = 32'hF000_0000,
    parameter [31:0] GROUP1_BASE = 32'h2000_0000,  // Lower half nodes
    parameter [31:0] GROUP1_MASK = 32'hF000_0000,
    parameter [31:0] GROUP2_BASE = 32'h3000_0000,  // Upper half nodes
    parameter [31:0] GROUP2_MASK = 32'hF000_0000
) (
    input wire clk,
    input wire rst_n,

    // Lookup request
    input  wire                  lookup_valid,
    input  wire [ADDR_WIDTH-1:0] lookup_addr,
    output wire                  lookup_ready,

    // Lookup result (combinational, 1-cycle latency)
    output wire                     result_valid,
    output wire [    NUM_PORTS-1:0] member_mask,       // Which nodes participate
    output wire [GROUP_ID_BITS-1:0] group_id,
    output wire                     is_multicast_addr, // True if multicast address

    // Configuration interface (optional, for runtime updates)
    input wire                     cfg_write,
    input wire [GROUP_ID_BITS-1:0] cfg_group_id,
    input wire [   ADDR_WIDTH-1:0] cfg_base_addr,
    input wire [   ADDR_WIDTH-1:0] cfg_addr_mask,
    input wire [    NUM_PORTS-1:0] cfg_member_mask
);

  // Number of configurable groups
  localparam NUM_GROUPS = 4;

  // Group table entries
  reg  [ADDR_WIDTH-1:0] group_base_addr  [NUM_GROUPS-1:0];
  reg  [ADDR_WIDTH-1:0] group_addr_mask  [NUM_GROUPS-1:0];
  reg  [ NUM_PORTS-1:0] group_member_mask[NUM_GROUPS-1:0];
  reg                   group_valid      [NUM_GROUPS-1:0];

  // Lookup state
  reg                   lookup_pending;
  reg  [ADDR_WIDTH-1:0] lookup_addr_reg;

  // Match results
  wire [NUM_GROUPS-1:0] group_match;

  // Generate match signals for each group
  genvar g;
  generate
    for (g = 0; g < NUM_GROUPS; g = g + 1) begin : gen_match
      assign group_match[g] = group_valid[g] &&
                              ((lookup_addr_reg & group_addr_mask[g]) == group_base_addr[g]);
    end
  endgenerate

  // Priority encoder to select matching group
  wire any_match = |group_match;
  reg [GROUP_ID_BITS-1:0] matched_group_id;
  reg [NUM_PORTS-1:0] matched_member_mask;

  // Select first matching group (priority order) - generic for any NUM_GROUPS
  always_comb begin
    matched_group_id = '0;
    matched_member_mask = {{(NUM_PORTS - 1) {1'b0}}, 1'b1};  // Default: single node
    for (int i = 0; i < NUM_GROUPS; i++) begin
      if (group_match[i]) begin
        matched_group_id    = i[GROUP_ID_BITS-1:0];
        matched_member_mask = group_member_mask[i];
        break;
      end
    end
  end

  // Initialize default groups (using parameterized addresses)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // Group 0: All nodes
      group_base_addr[0]   <= GROUP0_BASE;
      group_addr_mask[0]   <= GROUP0_MASK;
      group_member_mask[0] <= {NUM_PORTS{1'b1}};  // All nodes
      group_valid[0]       <= 1'b1;

      // Group 1: Lower half nodes
      group_base_addr[1]   <= GROUP1_BASE;
      group_addr_mask[1]   <= GROUP1_MASK;
      group_member_mask[1] <= {{(NUM_PORTS / 2) {1'b0}}, {(NUM_PORTS / 2) {1'b1}}};
      group_valid[1]       <= 1'b1;

      // Group 2: Upper half nodes
      group_base_addr[2]   <= GROUP2_BASE;
      group_addr_mask[2]   <= GROUP2_MASK;
      group_member_mask[2] <= {{(NUM_PORTS / 2) {1'b1}}, {(NUM_PORTS / 2) {1'b0}}};
      group_valid[2]       <= 1'b1;

      // Group 3: Reserved (disabled by default)
      group_base_addr[3]   <= 32'h0000_0000;
      group_addr_mask[3]   <= 32'h0000_0000;
      group_member_mask[3] <= '0;
      group_valid[3]       <= 1'b0;

      lookup_pending       <= 1'b0;
      lookup_addr_reg      <= '0;
    end else begin
      // Handle lookup requests
      if (lookup_valid && lookup_ready) begin
        lookup_pending  <= 1'b1;
        lookup_addr_reg <= lookup_addr;
      end else if (lookup_pending) begin
        lookup_pending <= 1'b0;
      end

      // Handle configuration writes
      if (cfg_write && (cfg_group_id < NUM_GROUPS)) begin
        group_base_addr[cfg_group_id]   <= cfg_base_addr;
        group_addr_mask[cfg_group_id]   <= cfg_addr_mask;
        group_member_mask[cfg_group_id] <= cfg_member_mask;
        group_valid[cfg_group_id]       <= 1'b1;
      end
    end
  end

  // Output assignments
  assign lookup_ready      = !lookup_pending;
  assign result_valid      = lookup_pending;
  assign member_mask       = any_match ? matched_member_mask : {{(NUM_PORTS - 1) {1'b0}}, 1'b1};
  assign group_id          = matched_group_id;
  assign is_multicast_addr = any_match;

endmodule
