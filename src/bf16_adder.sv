// BFloat16 Adder
// Performs addition of two BFloat16 values
//
// BFloat16 Format (16 bits):
//   Bit 15:    Sign (1 bit)
//   Bits 14-7: Exponent (8 bits, bias 127)
//   Bits 6-0:  Mantissa (7 bits, implicit leading 1)
//
// BFloat16 is identical to the upper 16 bits of IEEE 754 float32

module bf16_adder (
    input  wire [15:0] a,
    input  wire [15:0] b,
    output wire [15:0] sum
);

  // Extract fields from operand A
  wire sign_a = a[15];
  wire [7:0] exp_a = a[14:7];
  // Implicit leading 1 only for normalized numbers (exp != 0)
  wire [7:0] mant_a = {(exp_a != 8'h00), a[6:0]};

  // Extract fields from operand B
  wire sign_b = b[15];
  wire [7:0] exp_b = b[14:7];
  // Implicit leading 1 only for normalized numbers (exp != 0)
  wire [7:0] mant_b = {(exp_b != 8'h00), b[6:0]};

  // Special case detection
  wire a_is_zero = (exp_a == 8'h00) && (a[6:0] == 7'h00);
  wire b_is_zero = (exp_b == 8'h00) && (b[6:0] == 7'h00);
  wire a_is_inf = (exp_a == 8'hFF) && (a[6:0] == 7'h00);
  wire b_is_inf = (exp_b == 8'hFF) && (b[6:0] == 7'h00);
  wire a_is_nan = (exp_a == 8'hFF) && (a[6:0] != 7'h00);
  wire b_is_nan = (exp_b == 8'hFF) && (b[6:0] != 7'h00);

  // Canonical NaN value (quiet NaN)
  localparam [15:0] CANONICAL_NAN = 16'h7FC0;
  // Positive and negative infinity
  localparam [15:0] POS_INF = 16'h7F80;
  localparam [15:0] NEG_INF = 16'hFF80;

  // Determine which operand has larger magnitude
  wire a_gt_b = (exp_a > exp_b) || ((exp_a == exp_b) && (mant_a >= mant_b));

  // Arrange operands so op_large >= op_small
  wire sign_large = a_gt_b ? sign_a : sign_b;
  wire sign_small = a_gt_b ? sign_b : sign_a;
  wire [7:0] exp_large = a_gt_b ? exp_a : exp_b;
  wire [7:0] exp_small = a_gt_b ? exp_b : exp_a;
  wire [7:0] mant_large = a_gt_b ? mant_a : mant_b;
  wire [7:0] mant_small = a_gt_b ? mant_b : mant_a;

  // Calculate exponent difference for alignment
  wire [7:0] exp_diff = exp_large - exp_small;

  // Align smaller mantissa (shift right by exp_diff)
  // Use wider mantissa for precision during alignment
  wire [15:0] mant_small_aligned = (exp_diff < 8'd16) ? ({mant_small, 8'b0} >> exp_diff) : 16'b0;
  wire [15:0] mant_large_ext = {mant_large, 8'b0};

  // Add or subtract mantissas based on signs
  wire subtract = sign_large ^ sign_small;
  wire [16:0] mant_sum = subtract ? 
                         (mant_large_ext - mant_small_aligned) :
                         (mant_large_ext + mant_small_aligned);

  // Count leading zeros for normalization (combinational)
  function automatic [3:0] clz16(input [15:0] val);
    begin
      casez (val)
        16'b1???????????????: clz16 = 4'd0;
        16'b01??????????????: clz16 = 4'd1;
        16'b001?????????????: clz16 = 4'd2;
        16'b0001????????????: clz16 = 4'd3;
        16'b00001???????????: clz16 = 4'd4;
        16'b000001??????????: clz16 = 4'd5;
        16'b0000001?????????: clz16 = 4'd6;
        16'b00000001????????: clz16 = 4'd7;
        16'b000000001???????: clz16 = 4'd8;
        16'b0000000001??????: clz16 = 4'd9;
        16'b00000000001?????: clz16 = 4'd10;
        16'b000000000001????: clz16 = 4'd11;
        16'b0000000000001???: clz16 = 4'd12;
        16'b00000000000001??: clz16 = 4'd13;
        16'b000000000000001?: clz16 = 4'd14;
        16'b0000000000000001: clz16 = 4'd15;
        default: clz16 = 4'd15;  // All zeros
      endcase
    end
  endfunction

  // Handle overflow (carry out from addition)
  wire overflow = mant_sum[16];

  // Normalization
  wire [15:0] mant_for_norm = overflow ? mant_sum[16:1] : mant_sum[15:0];
  wire [3:0] lz = clz16(mant_for_norm);

  // Shift to normalize
  wire [15:0] mant_shifted = mant_for_norm << lz;

  // Adjust exponent
  // If overflow: exp + 1 (we shifted right by 1)
  // If leading zeros: exp - lz (we shifted left to normalize)
  // Note: lz counts leading zeros in mant_for_norm, which has the implicit 1 at bit 15 for normalized numbers
  wire [8:0] exp_calc = overflow ? ({1'b0, exp_large} + 9'd1) : ({1'b0, exp_large} - {5'b0, lz});

  // Detect underflow/overflow
  wire exp_underflow = exp_calc[8] || (exp_calc == 9'd0);
  wire exp_overflow = (exp_calc >= 9'd255);

  // Final exponent (clamped)
  wire [7:0] exp_result = exp_underflow ? 8'd0 : exp_overflow ? 8'd255 : exp_calc[7:0];

  // Final mantissa (take upper 7 bits after the implicit 1)
  wire [6:0] mant_result = mant_shifted[14:8];

  // Result sign: same as larger operand, unless result is zero
  wire result_is_zero = (mant_sum == 17'd0) || exp_underflow;
  wire final_sign = result_is_zero ? 1'b0 : sign_large;

  // Handle special cases
  wire [15:0] result_normal = {final_sign, exp_result, mant_result};

  // Infinity arithmetic results
  // inf + inf (same sign) = inf, inf - inf (opposite signs when adding) = NaN
  wire inf_plus_inf_same_sign = a_is_inf && b_is_inf && (sign_a == sign_b);
  wire inf_minus_inf = a_is_inf && b_is_inf && (sign_a != sign_b);
  wire [15:0] inf_result = sign_a ? NEG_INF : POS_INF;

  // Special case handling (priority order: NaN > Inf > Zero > Normal)
  assign sum = (a_is_nan || b_is_nan) ? CANONICAL_NAN :  // NaN propagates
      inf_minus_inf ? CANONICAL_NAN :  // inf - inf = NaN
      inf_plus_inf_same_sign ? inf_result :  // inf + inf = inf
      a_is_inf ? a :  // inf + finite = inf
      b_is_inf ? b :  // finite + inf = inf
      a_is_zero ? b :  // 0 + x = x
      b_is_zero ? a :  // x + 0 = x
      result_is_zero ? 16'h0000 :  // Result underflowed to zero
      result_normal;

endmodule
