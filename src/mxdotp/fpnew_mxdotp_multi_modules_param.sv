// Copyright 2025 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: SHL-0.51

// Author: Jayanth Jonnalagadda <jjonnalagadd@iis.ee.ethz.ch>

module fpnew_mxdotp_param_l1_lane
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type          SrcType         = logic,
  parameter int unsigned  LocalVectorSize = 8,
  parameter int unsigned  PrecisionBits   = 4,
  parameter int unsigned  ExpWidth        = 6,
  parameter int           MaxQWidth       = 8,
  parameter int           MinShift        = 0,
  parameter int           MaxShift        = 0,
  parameter int           MinExactShift   = 0,
  parameter logic         IntEnable       = 1'b0,
  parameter int           IntShift        = 0,
  parameter int unsigned  L1Width         = 72,
  parameter logic         L1Wrap          = 1'b0,
  // Do not change the following parameters
  localparam int unsigned MAX_Q_WIDTH     = (MaxQWidth > 1) ? MaxQWidth : 1,
  localparam int unsigned TERM_WIDTH      = (L1Wrap && (MAX_Q_WIDTH >= L1Width)) ? L1Width :
                                            ((MAX_Q_WIDTH < L1Width) ? MAX_Q_WIDTH : L1Width) + 1
) (
  input  SrcType              [LocalVectorSize-1:0]                 operands_a,
  input  SrcType              [LocalVectorSize-1:0]                 operands_b,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0]                 info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0]                 info_b,
  input  fpnew_pkg::fp_format_e                                     src_fmt,
  input  fpnew_pkg::int_format_e                                    int_fmt,
  input  logic                                                      src_is_int,
  input  logic signed         [7:0]                                 shift_offset,
  output logic signed         [LocalVectorSize-1:0][TERM_WIDTH-1:0] term,
  output logic                [LocalVectorSize-1:0]                 term_carry
);
  localparam int unsigned MUL_WIDTH     = IntEnable ? 8 : PrecisionBits;
  localparam int unsigned PRODUCT_WIDTH = IntEnable ? 2*MUL_WIDTH : 2*PrecisionBits + 1;
  localparam logic        CLIP          = !L1Wrap && (MAX_Q_WIDTH > L1Width);
  localparam int unsigned Q_WIDTH       = (MAX_Q_WIDTH < L1Width) ? MAX_Q_WIDTH : L1Width;
  localparam int          MAX_SHIFT_ALL = (IntEnable && (IntShift > MaxShift)) ? IntShift : MaxShift;
  localparam int unsigned CLIP_WIDTH    = PRODUCT_WIDTH + ((MAX_SHIFT_ALL > 0) ? MAX_SHIFT_ALL : 0);
  localparam int unsigned WIDE_WIDTH    = !CLIP ? TERM_WIDTH : ((CLIP_WIDTH > Q_WIDTH + 1) ? CLIP_WIDTH : Q_WIDTH + 1);
  localparam int unsigned EXT_WIDTH     = (WIDE_WIDTH > PRODUCT_WIDTH) ? WIDE_WIDTH : PRODUCT_WIDTH;
  localparam int unsigned RIGHT_BITS    = (MinShift < 0) ? -MinShift : 0;
  localparam int          AMT_RANGE     = MaxShift + int'(RIGHT_BITS);
  localparam int unsigned AMT_WIDTH     = (AMT_RANGE > 1) ? $clog2(AMT_RANGE + 1) : 1;
  localparam logic        FP_STICKY     = (MinExactShift < 0);
  localparam int unsigned INT_RIGHT     = (IntShift < 0) ? -IntShift : 0;
  localparam int unsigned INT_DROP      = (INT_RIGHT < PRODUCT_WIDTH) ? INT_RIGHT : PRODUCT_WIDTH;

  logic is_int8;

  assign is_int8 = IntEnable && src_is_int && (int_fmt == fpnew_pkg::INT8);

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_lane
    logic signed [PRODUCT_WIDTH-1:0] product;
    logic signed [ExpWidth-1:0]      exponent_product;
    logic signed [7:0]               shift;
    logic        [AMT_WIDTH-1:0]     shift_amount;
    logic signed [WIDE_WIDTH-1:0]    floor_fp;
    logic signed [WIDE_WIDTH-1:0]    floor_value;
    logic                            sticky_fp;
    logic                            sticky;
    logic                            negative;

    if (IntEnable) begin : gen_signed_product
      logic signed [MUL_WIDTH-1:0] mantissa_a, mantissa_b;

      always_comb begin : signed_operands
        if (is_int8) begin
          mantissa_a = operands_a[i][7:0];
          mantissa_b = operands_b[i][7:0];
        end else begin
          mantissa_a = MUL_WIDTH'({info_a[i].is_normal, operands_a[i].mantissa});
          mantissa_b = MUL_WIDTH'({info_b[i].is_normal, operands_b[i].mantissa});
          if (operands_a[i].sign ^ operands_b[i].sign) mantissa_a = -mantissa_a;
        end
      end

      assign product = mantissa_a * mantissa_b;
    end else begin : gen_unsigned_product
      logic [2*PrecisionBits-1:0] magnitude;

      assign magnitude = {info_a[i].is_normal, operands_a[i].mantissa} * {info_b[i].is_normal, operands_b[i].mantissa};
      assign product   = (operands_a[i].sign ^ operands_b[i].sign) ? -signed'({1'b0, magnitude}) : signed'({1'b0, magnitude});
    end

    assign exponent_product = operands_a[i].exponent + info_a[i].is_subnormal
                              + operands_b[i].exponent + info_b[i].is_subnormal
                              - 2*signed'(bias_constant(src_fmt));
    assign shift            = signed'(exponent_product) + shift_offset;
    assign shift_amount     = AMT_WIDTH'(shift + signed'(9'(RIGHT_BITS)));

    if (RIGHT_BITS > 0) begin : gen_bidirectional_shift
      logic [EXT_WIDTH+RIGHT_BITS-1:0] shifted;

      assign shifted  = (EXT_WIDTH+RIGHT_BITS)'(product) << shift_amount;
      assign floor_fp = shifted[RIGHT_BITS+:WIDE_WIDTH];
    end else begin : gen_left_shift
      assign floor_fp = WIDE_WIDTH'(EXT_WIDTH'(product) << shift_amount);
    end

    if (FP_STICKY) begin : gen_fp_sticky
      logic [cc_pkg::idx_width(PRODUCT_WIDTH)-1:0] trailing_zeros;
      logic                                        product_zero;

      cc_lzc #(
        .Width ( PRODUCT_WIDTH                 ),
        .Mode  ( cc_pkg::LZC_TRAILING_ZERO_CNT )
      ) i_trailing_zeros (
        .in_i    ( product        ),
        .cnt_o   ( trailing_zeros ),
        .empty_o ( product_zero   )
      );

      assign sticky_fp = !product_zero && (shift < 0) && (signed'({1'b0, trailing_zeros}) < -shift);
    end else begin : gen_no_fp_sticky
      assign sticky_fp = 1'b0;
    end

    if (IntEnable) begin : gen_int_shift
      logic signed [WIDE_WIDTH-1:0] floor_int;
      logic                         sticky_int;

      if (IntShift >= 0) begin : gen_int_left
        assign floor_int  = WIDE_WIDTH'(EXT_WIDTH'(product) << IntShift);
        assign sticky_int = 1'b0;
      end else begin : gen_int_right
        assign floor_int  = WIDE_WIDTH'(EXT_WIDTH'(product) >>> INT_RIGHT);
        assign sticky_int = |product[INT_DROP-1:0];
      end

      assign floor_value = is_int8 ? floor_int  : floor_fp;
      assign sticky      = is_int8 ? sticky_int : sticky_fp;
    end else begin : gen_fp_shift
      assign floor_value = floor_fp;
      assign sticky      = sticky_fp;
    end

    assign negative = product[PRODUCT_WIDTH-1];

    if (CLIP) begin : gen_clipped_term
      logic overflow;

      assign overflow      = negative ? ((floor_value[WIDE_WIDTH-1:Q_WIDTH] != '1) ||
                                         ((floor_value[Q_WIDTH-1:0] == '0) && !sticky)) :
                                        (floor_value[WIDE_WIDTH-1:Q_WIDTH] != '0);
      assign term[i]       = overflow ? {negative, {Q_WIDTH{~negative}}} : floor_value[Q_WIDTH:0];
      assign term_carry[i] = negative && (overflow || sticky);
    end else begin : gen_term
      assign term[i]       = floor_value;
      assign term_carry[i] = negative && sticky;
    end
  end
endmodule

module fpnew_mxdotp_anchorin_l1_lane
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type          SrcType         = logic,
  parameter int unsigned  LocalVectorSize = 8,
  parameter int unsigned  PrecisionBits   = 4,
  parameter int unsigned  ExpWidth        = 6,
  parameter int           MaxQWidth       = 8,
  parameter int           MinShift        = 0,
  parameter int           MaxShift        = 0,
  parameter int           MinExactShift   = 0,
  parameter logic         IntEnable       = 1'b0,
  parameter int unsigned  L1Width         = 72,
  parameter logic         L1Wrap          = 1'b0,
  // Do not change the following parameters
  localparam int unsigned MAX_Q_WIDTH     = (MaxQWidth > 1) ? MaxQWidth : 1,
  localparam int unsigned TERM_WIDTH      = (L1Wrap && (MAX_Q_WIDTH >= L1Width)) ? L1Width :
                                            ((MAX_Q_WIDTH < L1Width) ? MAX_Q_WIDTH : L1Width) + 1
) (
  input  SrcType              [LocalVectorSize-1:0]                 operands_a,
  input  SrcType              [LocalVectorSize-1:0]                 operands_b,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0]                 info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0]                 info_b,
  input  fpnew_pkg::fp_format_e                                     src_fmt,
  input  fpnew_pkg::int_format_e                                    int_fmt,
  input  logic                                                      src_is_int,
  input  logic signed         [7:0]                                 shift_offset,
  output logic signed         [LocalVectorSize-1:0][TERM_WIDTH-1:0] term,
  output logic                [LocalVectorSize-1:0]                 term_carry
);
  localparam int unsigned MUL_WIDTH     = IntEnable ? 8 : PrecisionBits;
  localparam int unsigned PRODUCT_WIDTH = IntEnable ? 2*MUL_WIDTH : 2*PrecisionBits + 1;
  localparam logic        CLIP          = !L1Wrap && (MAX_Q_WIDTH > L1Width);
  localparam int unsigned Q_WIDTH       = (MAX_Q_WIDTH < L1Width) ? MAX_Q_WIDTH : L1Width;
  localparam int unsigned CLIP_WIDTH    = PRODUCT_WIDTH + ((MaxShift > 0) ? MaxShift : 0);
  localparam int unsigned WIDE_WIDTH    = !CLIP ? TERM_WIDTH : ((CLIP_WIDTH > Q_WIDTH + 1) ? CLIP_WIDTH : Q_WIDTH + 1);
  localparam int unsigned EXT_WIDTH     = (WIDE_WIDTH > PRODUCT_WIDTH) ? WIDE_WIDTH : PRODUCT_WIDTH;
  localparam int unsigned RIGHT_BITS    = (MinShift < 0) ? -MinShift : 0;
  localparam int          AMT_RANGE     = MaxShift + int'(RIGHT_BITS);
  localparam int unsigned AMT_WIDTH     = (AMT_RANGE > 1) ? $clog2(AMT_RANGE + 1) : 1;
  localparam logic        STICKY        = (MinExactShift < 0);

  logic is_int8;

  assign is_int8 = IntEnable && src_is_int && (int_fmt == fpnew_pkg::INT8);

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_lane
    logic signed [PRODUCT_WIDTH-1:0] product;
    logic signed [ExpWidth-1:0]      exponent_product;
    logic signed [7:0]               shift;
    logic        [AMT_WIDTH-1:0]     shift_amount;
    logic signed [WIDE_WIDTH-1:0]    floor_value;
    logic                            sticky;
    logic                            negative;

    if (IntEnable) begin : gen_signed_product
      logic signed [MUL_WIDTH-1:0] mantissa_a, mantissa_b;

      always_comb begin : signed_operands
        if (is_int8) begin
          mantissa_a = operands_a[i][7:0];
          mantissa_b = operands_b[i][7:0];
        end else begin
          mantissa_a = MUL_WIDTH'({info_a[i].is_normal, operands_a[i].mantissa});
          mantissa_b = MUL_WIDTH'({info_b[i].is_normal, operands_b[i].mantissa});
          if (operands_a[i].sign ^ operands_b[i].sign) mantissa_a = -mantissa_a;
        end
      end

      assign product = mantissa_a * mantissa_b;
    end else begin : gen_unsigned_product
      logic [2*PrecisionBits-1:0] magnitude;

      assign magnitude = {info_a[i].is_normal, operands_a[i].mantissa} * {info_b[i].is_normal, operands_b[i].mantissa};
      assign product   = (operands_a[i].sign ^ operands_b[i].sign) ? -signed'({1'b0, magnitude}) : signed'({1'b0, magnitude});
    end

    assign exponent_product = is_int8 ? '0 :
                                        operands_a[i].exponent + info_a[i].is_subnormal
                                        + operands_b[i].exponent + info_b[i].is_subnormal
                                        - 2*signed'(bias_constant(src_fmt));
    assign shift            = signed'(exponent_product) + shift_offset;
    assign shift_amount     = AMT_WIDTH'(shift + signed'(9'(RIGHT_BITS)));

    if (RIGHT_BITS > 0) begin : gen_bidirectional_shift
      logic [EXT_WIDTH+RIGHT_BITS-1:0] shifted;

      assign shifted     = (EXT_WIDTH+RIGHT_BITS)'(product) << shift_amount;
      assign floor_value = shifted[RIGHT_BITS+:WIDE_WIDTH];
    end else begin : gen_left_shift
      assign floor_value = WIDE_WIDTH'(EXT_WIDTH'(product) << shift_amount);
    end

    if (STICKY) begin : gen_sticky
      logic [cc_pkg::idx_width(PRODUCT_WIDTH)-1:0] trailing_zeros;
      logic                                        product_zero;

      cc_lzc #(
        .Width ( PRODUCT_WIDTH                 ),
        .Mode  ( cc_pkg::LZC_TRAILING_ZERO_CNT )
      ) i_trailing_zeros (
        .in_i    ( product        ),
        .cnt_o   ( trailing_zeros ),
        .empty_o ( product_zero   )
      );

      assign sticky = !product_zero && (shift < 0) && (signed'({1'b0, trailing_zeros}) < -shift);
    end else begin : gen_no_sticky
      assign sticky = 1'b0;
    end

    assign negative = product[PRODUCT_WIDTH-1];

    if (CLIP) begin : gen_clipped_term
      logic overflow;

      assign overflow      = negative ? ((floor_value[WIDE_WIDTH-1:Q_WIDTH] != '1) ||
                                         ((floor_value[Q_WIDTH-1:0] == '0) && !sticky)) :
                                        (floor_value[WIDE_WIDTH-1:Q_WIDTH] != '0);
      assign term[i]       = overflow ? {negative, {Q_WIDTH{~negative}}} : floor_value[Q_WIDTH:0];
      assign term_carry[i] = negative && (overflow || sticky);
    end else begin : gen_term
      assign term[i]       = floor_value;
      assign term_carry[i] = negative && sticky;
    end
  end
endmodule

module fpnew_mxdotp_dynanchor_l1_lane
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type          SrcType         = logic,
  parameter int unsigned  LocalVectorSize = 8,
  parameter int unsigned  PrecisionBits   = 4,
  parameter int unsigned  ExpWidth        = 6,
  parameter int unsigned  TermWidth       = 8,
  parameter int           MinShift        = 0,
  parameter int           MaxShift        = 0,
  parameter int           MinExactShift   = 0,
  parameter logic         IntEnable       = 1'b0
) (
  input  SrcType              [LocalVectorSize-1:0]                operands_a,
  input  SrcType              [LocalVectorSize-1:0]                operands_b,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0]                info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0]                info_b,
  input  fpnew_pkg::fp_format_e                                    src_fmt,
  input  fpnew_pkg::int_format_e                                   int_fmt,
  input  logic                                                     src_is_int,
  input  logic signed         [7:0]                                shift_offset,
  output logic signed         [LocalVectorSize-1:0][7:0]           exponent_sum,
  output logic                [LocalVectorSize-1:0]                exponent_valid,
  output logic signed         [LocalVectorSize-1:0][TermWidth-1:0] term,
  output logic                [LocalVectorSize-1:0]                term_carry
);
  localparam int unsigned MUL_WIDTH     = IntEnable ? 8 : PrecisionBits;
  localparam int unsigned PRODUCT_WIDTH = IntEnable ? 2*MUL_WIDTH : 2*PrecisionBits + 1;
  localparam logic        SHIFT_CLAMP   = (MinShift < -int'(PRODUCT_WIDTH));
  localparam int          LO_SHIFT      = SHIFT_CLAMP ? -int'(PRODUCT_WIDTH) : MinShift;
  localparam int unsigned EXT_WIDTH     = (TermWidth > PRODUCT_WIDTH) ? TermWidth : PRODUCT_WIDTH;
  localparam int unsigned RIGHT_BITS    = (LO_SHIFT < 0) ? -LO_SHIFT : 0;
  localparam int          AMT_RANGE     = MaxShift + int'(RIGHT_BITS);
  localparam int unsigned AMT_WIDTH     = (AMT_RANGE > 1) ? $clog2(AMT_RANGE + 1) : 1;
  localparam logic        STICKY        = (MinExactShift < 0);

  logic is_int8;

  assign is_int8 = IntEnable && src_is_int && (int_fmt == fpnew_pkg::INT8);

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_lane
    logic signed [PRODUCT_WIDTH-1:0] product;
    logic signed [ExpWidth-1:0]      exponent_product;
    logic signed [7:0]               shift_raw;
    logic signed [7:0]               shift;
    logic        [AMT_WIDTH-1:0]     shift_amount;
    logic signed [TermWidth-1:0]     floor_value;
    logic                            sticky;

    if (IntEnable) begin : gen_signed_product
      logic signed [MUL_WIDTH-1:0] mantissa_a, mantissa_b;

      always_comb begin : signed_operands
        if (is_int8) begin
          mantissa_a = operands_a[i][7:0];
          mantissa_b = operands_b[i][7:0];
        end else begin
          mantissa_a = MUL_WIDTH'({info_a[i].is_normal, operands_a[i].mantissa});
          mantissa_b = MUL_WIDTH'({info_b[i].is_normal, operands_b[i].mantissa});
          if (operands_a[i].sign ^ operands_b[i].sign) mantissa_a = -mantissa_a;
        end
      end

      assign product = mantissa_a * mantissa_b;
    end else begin : gen_unsigned_product
      logic [2*PrecisionBits-1:0] magnitude;

      assign magnitude = {info_a[i].is_normal, operands_a[i].mantissa} * {info_b[i].is_normal, operands_b[i].mantissa};
      assign product   = (operands_a[i].sign ^ operands_b[i].sign) ? -signed'({1'b0, magnitude}) : signed'({1'b0, magnitude});
    end

    assign exponent_product = is_int8 ? '0 :
                                        operands_a[i].exponent + info_a[i].is_subnormal
                                        + operands_b[i].exponent + info_b[i].is_subnormal
                                        - 2*signed'(bias_constant(src_fmt));
    assign shift_raw        = signed'(exponent_product) + shift_offset;

    if (SHIFT_CLAMP) begin : gen_shift_clamp
      assign shift = (shift_raw < 8'(LO_SHIFT)) ? 8'(LO_SHIFT) : shift_raw;
    end else begin : gen_no_shift_clamp
      assign shift = shift_raw;
    end

    assign shift_amount = AMT_WIDTH'(shift + signed'(9'(RIGHT_BITS)));

    if (RIGHT_BITS > 0) begin : gen_bidirectional_shift
      logic [EXT_WIDTH+RIGHT_BITS-1:0] shifted;

      assign shifted     = (EXT_WIDTH+RIGHT_BITS)'(product) << shift_amount;
      assign floor_value = shifted[RIGHT_BITS+:TermWidth];
    end else begin : gen_left_shift
      assign floor_value = TermWidth'(EXT_WIDTH'(product) << shift_amount);
    end

    if (STICKY) begin : gen_sticky
      logic [cc_pkg::idx_width(PRODUCT_WIDTH)-1:0] trailing_zeros;
      logic                                        product_zero;

      cc_lzc #(
        .Width ( PRODUCT_WIDTH                 ),
        .Mode  ( cc_pkg::LZC_TRAILING_ZERO_CNT )
      ) i_trailing_zeros (
        .in_i    ( product        ),
        .cnt_o   ( trailing_zeros ),
        .empty_o ( product_zero   )
      );

      assign sticky = !product_zero && (shift < 0) && (signed'({1'b0, trailing_zeros}) < -shift);
    end else begin : gen_no_sticky
      assign sticky = 1'b0;
    end

    assign exponent_sum[i]   = 8'(exponent_product);
    assign exponent_valid[i] = !info_a[i].is_zero && !info_b[i].is_zero;
    assign term[i]           = floor_value;
    assign term_carry[i]     = product[PRODUCT_WIDTH-1] && sticky;
  end
endmodule

module fpnew_mxdotp_max_tree #(
  parameter int unsigned NumInputs = 32,
  parameter int unsigned Width     = 8,
  localparam int unsigned LEVELS   = (NumInputs > 1) ? $clog2(NumInputs) : 1,
  localparam int unsigned NUM_PAD  = 2**LEVELS
) (
  input  logic signed [NumInputs-1:0][Width-1:0] value,
  input  logic        [NumInputs-1:0]            valid,
  output logic signed [Width-1:0]                max_value,
  output logic                                   max_valid
);
  logic [2*NUM_PAD-2:0][Width-1:0] node_value;
  logic [2*NUM_PAD-2:0]            node_valid;

  for (genvar i = 0; i < NUM_PAD; i++) begin : gen_leaf
    if (i < NumInputs) begin : gen_input
      assign node_value[NUM_PAD-1+i] = value[i];
      assign node_valid[NUM_PAD-1+i] = valid[i];
    end else begin : gen_pad
      assign node_value[NUM_PAD-1+i] = '0;
      assign node_valid[NUM_PAD-1+i] = 1'b0;
    end
  end

  for (genvar n = 0; n < NUM_PAD-1; n++) begin : gen_node
    logic pick_right;

    assign pick_right    = node_valid[2*n+2] && (!node_valid[2*n+1] || (signed'(node_value[2*n+2]) > signed'(node_value[2*n+1])));
    assign node_value[n] = pick_right ? node_value[2*n+2] : node_value[2*n+1];
    assign node_valid[n] = node_valid[2*n+1] || node_valid[2*n+2];
  end

  assign max_value = node_value[0];
  assign max_valid = node_valid[0];
endmodule

module fpnew_mxdotp_l1_sum
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned LocalVectorSize = 32,
  parameter int unsigned TermWidth       = 67,
  parameter int unsigned SumWidth        = 72
) (
  input  logic signed [LocalVectorSize-1:0][TermWidth-1:0] term,
  input  logic        [LocalVectorSize-1:0]                carry,
  output logic signed [SumWidth-1:0]                       sum
);
  always_comb begin : plain_accumulation
    sum = '0;
    for (int i = 0; i < LocalVectorSize; i++) begin
      sum = sum + signed'(term[i]) + signed'({1'b0, carry[i]});
    end
  end
endmodule

module fpnew_mxdotp_param_early_accumulate
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned  SoPWidth   = 72,
  parameter int           Anchor     = 34,
  parameter int unsigned  Window     = 24,
  parameter int unsigned  ScaleWidth = SCALE_WIDTH + 1,
  // Do not change the following parameters
  localparam int unsigned D_WIDTH    = DST_PRECISION_BITS + 1,
  localparam int unsigned EXT_WIDTH  = SoPWidth + D_WIDTH + Window,
  localparam int unsigned MAG_WIDTH  = EXT_WIDTH - 1
) (
  input  logic signed [SoPWidth-1:0]   sum_product,
  input  logic signed [ScaleWidth-1:0] scale,
  input  fp_dst_t                     operand_d,
  output logic                        result_is_accumulator,
  output logic                        sum_product_is_zero,
  output logic                        final_sign,
  output logic        [MAG_WIDTH-1:0] sum_magnitude,
  output logic                        accumulator_sticky
);
  localparam int          DST_BIAS          = fpnew_pkg::bias(fpnew_pkg::FP32);
  localparam int          SHIFT_OFFSET      = Anchor - int'(SUPER_DST_MAN_BITS) - DST_BIAS;
  localparam int unsigned RIGHT_SHAMT_WIDTH = $clog2(D_WIDTH + 1);

  logic                                d_is_normal;
  logic                                d_is_subnormal;
  logic signed [D_WIDTH-1:0]           signed_mantissa_d;
  logic signed [DST_EXP_WIDTH-1:0]     accumulator_shift_amount;
  logic        [RIGHT_SHAMT_WIDTH-1:0] accumulator_right_shift_amount;
  logic signed [D_WIDTH-1:0]           accumulator_right_shifted;
  logic        [D_WIDTH-1:0]           accumulator_sticky_bits;
  logic signed [EXT_WIDTH-1:0]         accumulator_aligned;
  logic signed [EXT_WIDTH-1:0]         sum_extended;

  assign d_is_normal       = (operand_d.exponent != '0);
  assign d_is_subnormal    = (operand_d.exponent == '0) && (operand_d.mantissa != '0);
  assign signed_mantissa_d = operand_d.sign ? -signed'({1'b0, d_is_normal, operand_d.mantissa}) :
                                               signed'({1'b0, d_is_normal, operand_d.mantissa});

  assign accumulator_shift_amount = signed'(DST_EXP_WIDTH'(SHIFT_OFFSET)) + signed'({2'b0, operand_d.exponent})
                                    + signed'({1'b0, d_is_subnormal}) - scale;

  assign accumulator_right_shift_amount = (accumulator_shift_amount < -signed'(Window + D_WIDTH)) ? D_WIDTH :
                                          RIGHT_SHAMT_WIDTH'(-signed'(Window) - accumulator_shift_amount);

  assign {accumulator_right_shifted, accumulator_sticky_bits} = signed'({signed_mantissa_d, D_WIDTH'(0)})
                                                                >>> accumulator_right_shift_amount;

  always_comb begin : accumulator_alignment
    if (accumulator_shift_amount >= -signed'(Window)) begin
      accumulator_aligned = EXT_WIDTH'(signed_mantissa_d) <<< (accumulator_shift_amount + signed'(Window));
      accumulator_sticky  = 1'b0;
    end else begin
      accumulator_aligned = EXT_WIDTH'(accumulator_right_shifted);
      accumulator_sticky  = |accumulator_sticky_bits;
    end
  end

  assign sum_extended = (EXT_WIDTH'(sum_product) <<< Window) + accumulator_aligned;

  assign sum_product_is_zero   = (sum_product == '0);
  assign result_is_accumulator = (accumulator_shift_amount > signed'(SoPWidth)) ||
                                 ((accumulator_shift_amount < -signed'(Window)) && sum_product_is_zero);
  assign final_sign            = sum_extended[EXT_WIDTH-1];
  assign sum_magnitude         = final_sign ? (~sum_extended[MAG_WIDTH-1:0] + !accumulator_sticky) :
                                              sum_extended[MAG_WIDTH-1:0];
endmodule
