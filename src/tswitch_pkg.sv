`ifndef TSWITCH_PKG_SV
`define TSWITCH_PKG_SV

// tiny-switch Package - Shared constants, types, and parameters
// This eliminates magic numbers throughout the codebase

package tswitch_pkg;

  // ============== GLOBAL PARAMETERS ==============
  parameter NUM_PORTS = 4;  // Number of connected nodes (default, can be overridden)
  parameter PORT_BITS = $clog2(NUM_PORTS);  // Bits needed for port index
  parameter DATA_WIDTH = 16;  // BFloat16 = 16 bits
  parameter ADDR_WIDTH = 32;  // 32-bit addresses
  parameter TAG_WIDTH = 8;  // Request tag for tracking
  parameter GROUP_ID_BITS = 4;  // Up to 16 multicast groups
  parameter MAX_PENDING = 4;  // Max in-flight operations

  // ============== COMMAND TYPES (Node → Switch) ==============
  typedef enum logic [2:0] {
    CMD_NOP         = 3'b000,  // No operation
    CMD_LOAD_REDUCE = 3'b001,  // Read from all nodes, reduce, return result
    CMD_STORE_MC    = 3'b010,  // Write to all nodes (multicast)
    CMD_READ        = 3'b011,  // Normal read (passthrough)
    CMD_WRITE       = 3'b100   // Normal write (passthrough)
  } cmd_t;

  // ============== RESPONSE TYPES (Switch → Node) ==============
  typedef enum logic [1:0] {
    RESP_DATA  = 2'b00,  // Read data response
    RESP_ACK   = 2'b01,  // Write acknowledgment
    RESP_ERROR = 2'b11   // Error response
  } resp_t;

  // ============== PORT INTERFACE STATES ==============
  typedef enum logic [1:0] {
    PORT_IDLE    = 2'b00,
    PORT_BUSY    = 2'b01,
    PORT_WAITING = 2'b10,
    PORT_RESPOND = 2'b11
  } port_state_t;

  // ============== REDUCTION ENGINE STATES ==============
  typedef enum logic [2:0] {
    RED_IDLE     = 3'b000,  // Waiting for values
    RED_FIRST    = 3'b001,  // Received first value
    RED_REDUCING = 3'b010,  // Accumulating values
    RED_DONE     = 3'b011,  // Result ready
    RED_RESPOND  = 3'b100   // Sending response
  } reduction_state_t;

  // ============== COMMAND DECODER STATES ==============
  typedef enum logic [2:0] {
    DEC_IDLE     = 3'b000,  // Waiting for command
    DEC_DECODE   = 3'b001,  // Decoding command
    DEC_LOOKUP   = 3'b010,  // Looking up group table
    DEC_DISPATCH = 3'b011,  // Dispatching to engines
    DEC_WAIT     = 3'b100,  // Waiting for completion
    DEC_RESPOND  = 3'b101   // Sending response
  } decoder_state_t;

  // ============== READ REQUESTER STATES ==============
  typedef enum logic [1:0] {
    REQ_IDLE    = 2'b00,  // Waiting for request
    REQ_ISSUING = 2'b01,  // Issuing read requests
    REQ_WAITING = 2'b10,  // Waiting for responses
    REQ_DONE    = 2'b11   // All responses received
  } requester_state_t;

  // ============== MULTICAST ENGINE STATES ==============
  typedef enum logic [1:0] {
    MC_IDLE    = 2'b00,  // Waiting for write request
    MC_WRITING = 2'b01,  // Writing to nodes
    MC_WAITING = 2'b10,  // Waiting for acknowledgments
    MC_DONE    = 2'b11   // All writes complete
  } multicast_state_t;

  // ============== INTERNAL REQUEST STRUCTURE ==============
  // Used for tracking in-flight operations
  typedef struct packed {
    logic [NUM_PORTS-1:0]     node_mask;  // Which nodes participate
    logic [ADDR_WIDTH-1:0]    addr;       // Memory address
    logic [DATA_WIDTH-1:0]    data;       // Data (for writes)
    logic [GROUP_ID_BITS-1:0] group_id;   // Multicast group ID
    logic [1:0]               src_port;   // Requesting port (0-3)
    logic [TAG_WIDTH-1:0]     tag;        // Request identifier
    cmd_t                     cmd;        // Command type
  } request_t;

  // ============== GROUP TABLE ENTRY ==============
  typedef struct packed {
    logic                  valid;        // Entry is valid
    logic [ADDR_WIDTH-1:0] base_addr;    // Base address of range
    logic [ADDR_WIDTH-1:0] addr_mask;    // Address mask for matching
    logic [NUM_PORTS-1:0]  member_mask;  // Which nodes are members
  } group_entry_t;

  // ============== HELPER FUNCTIONS ==============

  // Count number of set bits (population count) - generic width
  function automatic logic [7:0] popcount(input logic [15:0] bits, input int width);
    logic [7:0] count;
    count = 0;
    for (int i = 0; i < width; i++) begin
      count = count + bits[i];
    end
    return count;
  endfunction

  // Find first set bit (priority encoder) - generic width
  // Returns the index of the first set bit, or 0 if none set
  function automatic logic [3:0] find_first_set(input logic [15:0] bits, input int width);
    for (int i = 0; i < width; i++) begin
      if (bits[i]) return i[3:0];
    end
    return 0;
  endfunction

  // Legacy 4-bit versions for backward compatibility
  function automatic logic [2:0] popcount4(input logic [3:0] bits);
    return popcount({12'b0, bits}, 4);
  endfunction

  function automatic logic [1:0] find_first_set4(input logic [3:0] bits);
    return find_first_set({12'b0, bits}, 4);
  endfunction

endpackage

`endif
