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

module fpnew_mxdotp_l1_term
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned  ProductWidth = 8,
  parameter int           MaxQWidth    = 8,
  parameter int unsigned  L1Width      = 72,
  parameter logic         L1Wrap       = 1'b0,
  // Do not change the following parameters
  localparam int unsigned MAX_Q_WIDTH  = (MaxQWidth > 1) ? MaxQWidth : 1,
  localparam logic        CLIP         = !L1Wrap && (MAX_Q_WIDTH > L1Width),
  localparam int unsigned Q_WIDTH      = (MAX_Q_WIDTH < L1Width) ? MAX_Q_WIDTH : L1Width,
  localparam int unsigned TERM_WIDTH   = (L1Wrap && (MAX_Q_WIDTH >= L1Width)) ? L1Width : Q_WIDTH + 1
) (
  input  logic        [ProductWidth-1:0] product,
  input  logic                           product_sign,
  input  logic signed [7:0]              shift,
  output logic signed [TERM_WIDTH-1:0]   term
);
  localparam int unsigned WIDE_WIDTH = CLIP ? L1Width + ProductWidth :
                                       ((Q_WIDTH > ProductWidth) ? Q_WIDTH : ProductWidth);

  logic [WIDE_WIDTH-1:0] shifted;
  logic [Q_WIDTH-1:0]    magnitude;

  always_comb begin : l1_shift
    if (shift >= 0) shifted = WIDE_WIDTH'(product) << shift;
    else            shifted = WIDE_WIDTH'(product) >> (-shift);
  end

  assign magnitude = shifted[Q_WIDTH-1:0];

  if (CLIP) begin : gen_clipped_term
    logic               overflow;
    logic [Q_WIDTH-1:0] clipped;

    assign overflow = (shift >= signed'(L1Width)) ? (product != '0) : (shifted[WIDE_WIDTH-1:L1Width] != '0);
    assign clipped  = overflow ? '1 : magnitude;
    assign term     = product_sign ? -signed'({1'b0, clipped}) : signed'({1'b0, clipped});
  end else if (TERM_WIDTH == Q_WIDTH) begin : gen_wrapped_term
    assign term = product_sign ? -signed'(magnitude) : signed'(magnitude);
  end else begin : gen_exact_term
    assign term = product_sign ? -signed'({1'b0, magnitude}) : signed'({1'b0, magnitude});
  end
endmodule

module fpnew_mxdotp_param_l1_lane
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type          SrcType         = logic,
  parameter int unsigned  LocalVectorSize = 8,
  parameter int unsigned  PrecisionBits   = 4,
  parameter int unsigned  ExpWidth        = 6,
  parameter int           MaxQWidth       = 8,
  parameter logic         IntEnable       = 1'b0,
  parameter int unsigned  L1Width         = 72,
  parameter logic         L1Wrap          = 1'b0,
  // Do not change the following parameters
  localparam int unsigned PRODUCT_WIDTH   = IntEnable ? 16 : 2*PrecisionBits,
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
  output logic signed         [LocalVectorSize-1:0][TERM_WIDTH-1:0] term
);
  logic is_int8;

  assign is_int8 = IntEnable && src_is_int && (int_fmt == fpnew_pkg::INT8);

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_lane
    logic        [PRODUCT_WIDTH-1:0] product;
    logic                            product_sign;
    logic signed [ExpWidth-1:0]      exponent_product;
    logic signed [7:0]               shift;

    if (IntEnable) begin : gen_int_product
      logic [7:0] magnitude_a, magnitude_b;

      assign magnitude_a  = operands_a[i][7] ? -operands_a[i][7:0] : operands_a[i][7:0];
      assign magnitude_b  = operands_b[i][7] ? -operands_b[i][7:0] : operands_b[i][7:0];
      assign product      = is_int8 ? (magnitude_a * magnitude_b) :
                                      PRODUCT_WIDTH'({info_a[i].is_normal, operands_a[i].mantissa} *
                                                     {info_b[i].is_normal, operands_b[i].mantissa});
      assign product_sign = is_int8 ? (operands_a[i][7] ^ operands_b[i][7]) : (operands_a[i].sign ^ operands_b[i].sign);
    end else begin : gen_fp_product
      assign product      = {info_a[i].is_normal, operands_a[i].mantissa} * {info_b[i].is_normal, operands_b[i].mantissa};
      assign product_sign = operands_a[i].sign ^ operands_b[i].sign;
    end

    assign exponent_product = operands_a[i].exponent + info_a[i].is_subnormal
                              + operands_b[i].exponent + info_b[i].is_subnormal
                              - 2*signed'(bias_constant(src_fmt));
    assign shift            = is_int8 ? shift_offset : (signed'(exponent_product) + shift_offset);

    fpnew_mxdotp_l1_term #(
      .ProductWidth ( PRODUCT_WIDTH ),
      .MaxQWidth    ( MAX_Q_WIDTH   ),
      .L1Width      ( L1Width       ),
      .L1Wrap       ( L1Wrap        )
    ) i_l1_term (
      .product      ( product      ),
      .product_sign ( product_sign ),
      .shift        ( shift        ),
      .term         ( term[i]      )
    );
  end
endmodule

module fpnew_mxdotp_l1_sum
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned LocalVectorSize = 32,
  parameter int unsigned TermWidth       = 67,
  parameter int unsigned SumWidth        = 72,
  parameter logic        Saturate        = 1'b0
) (
  input  logic signed [LocalVectorSize-1:0][TermWidth-1:0] term,
  output logic signed [SumWidth-1:0]                       sum
);
  if (Saturate) begin : gen_saturating_sum
    localparam int unsigned          NEXT_WIDTH = ((SumWidth > TermWidth) ? SumWidth : TermWidth) + 1;
    localparam logic signed [SumWidth-1:0] SUM_MAX = {1'b0, {(SumWidth-1){1'b1}}};
    localparam logic signed [SumWidth-1:0] SUM_MIN = {1'b1, {(SumWidth-1){1'b0}}};

    always_comb begin : saturating_accumulation
      logic signed [NEXT_WIDTH-1:0] sum_next;
      sum = '0;
      for (int i = 0; i < LocalVectorSize; i++) begin
        sum_next = signed'(sum) + signed'(term[i]);
        if ((sum_next[NEXT_WIDTH-1:SumWidth-1] == '0) || (sum_next[NEXT_WIDTH-1:SumWidth-1] == '1)) sum = sum_next[SumWidth-1:0];
        else                                                                                         sum = sum_next[NEXT_WIDTH-1] ? SUM_MIN : SUM_MAX;
      end
    end
  end else begin : gen_plain_sum
    always_comb begin : plain_accumulation
      sum = '0;
      for (int i = 0; i < LocalVectorSize; i++) begin
        sum = sum + signed'(term[i]);
      end
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
