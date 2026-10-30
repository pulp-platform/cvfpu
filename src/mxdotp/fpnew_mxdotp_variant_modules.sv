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

module fpnew_mxdotp_fixed_normalize
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned  MagWidth   = 71,
  parameter int           Anchor     = 34,
  parameter int unsigned  ScaleWidth = SCALE_WIDTH + 1,
  parameter int           MaxScale   = 2**SCALE_WIDTH - 2,
  parameter int           MinScale   = -(2**SCALE_WIDTH - 2),
  // Do not change the following parameters
  localparam int unsigned LZC_WIDTH  = cc_pkg::idx_width(MagWidth)
) (
  input  logic        [MagWidth-1:0]           magnitude,
  input  logic        [LZC_WIDTH-1:0]          leading_zero_count,
  input  logic                                 lzc_zeroes,
  input  logic signed [ScaleWidth-1:0]         scale,
  input  logic                                 sticky_in,
  output logic        [DST_EXP_WIDTH-1:0]      final_exponent,
  output logic        [DST_PRECISION_BITS-1:0] final_mantissa,
  output logic                                 sticky_after_norm
);
  localparam int unsigned SIG_WIDTH        = DST_PRECISION_BITS + 2;
  localparam int unsigned NORM_WIDTH       = (MagWidth > SIG_WIDTH) ? MagWidth : SIG_WIDTH;
  localparam int unsigned SUB_SHAMT_WIDTH  = $clog2(SIG_WIDTH + 1);
  localparam int          DST_BIAS         = fpnew_pkg::bias(fpnew_pkg::FP32);
  localparam int          EXPONENT_OFFSET  = int'(MagWidth) - 1 - Anchor + DST_BIAS;

  if ((EXPONENT_OFFSET + MaxScale > 2**(DST_EXP_WIDTH-1) - 1) ||
      (EXPONENT_OFFSET - int'(MagWidth) + 1 + MinScale < -2**(DST_EXP_WIDTH-1))) begin
    $fatal(1, "fpnew_mxdotp_fixed_normalize: exponent range exceeds DST_EXP_WIDTH for MagWidth=%0d Anchor=%0d", MagWidth, Anchor);
  end

  logic        [NORM_WIDTH-1:0]      padded_magnitude;
  logic        [NORM_WIDTH-1:0]      normalized;
  logic        [SIG_WIDTH-1:0]       significand;
  logic signed [DST_EXP_WIDTH-1:0]   tentative_exponent;
  logic                              is_normal;
  logic        [SUB_SHAMT_WIDTH-1:0] subnormal_shamt;
  logic        [SIG_WIDTH-1:0]       subnormal_significand;
  logic        [SIG_WIDTH-1:0]       subnormal_sticky_bits;

  assign padded_magnitude = NORM_WIDTH'(magnitude) << (NORM_WIDTH - MagWidth);
  assign normalized       = padded_magnitude << leading_zero_count;
  assign significand      = {normalized[NORM_WIDTH-1-:SIG_WIDTH-1], (|normalized[NORM_WIDTH-SIG_WIDTH:0]) | sticky_in};

  assign tentative_exponent = signed'(DST_EXP_WIDTH'(EXPONENT_OFFSET)) - signed'({1'b0, leading_zero_count}) + scale;
  assign is_normal          = !lzc_zeroes && (tentative_exponent > 0);

  assign subnormal_shamt = (tentative_exponent <= 1 - signed'(SIG_WIDTH)) ? SIG_WIDTH :
                                                                            SUB_SHAMT_WIDTH'(1 - tentative_exponent);

  assign {subnormal_significand, subnormal_sticky_bits} = {significand, SIG_WIDTH'(0)} >> subnormal_shamt;

  assign final_exponent    = is_normal ? tentative_exponent : '0;
  assign final_mantissa    = is_normal ? significand[SIG_WIDTH-2:1] : subnormal_significand[SIG_WIDTH-2:1];
  assign sticky_after_norm = is_normal ? significand[0] : (subnormal_significand[0] | (|subnormal_sticky_bits));
endmodule

module fpnew_mxdotp_acc_adder
  import fpnew_mxdotp_multi_pkg::*;
(
  input  fp_dst_t                              operand_a,
  input  fp_dst_t                              operand_b,
  input  fpnew_pkg::roundmode_e                rnd_mode,
  output logic                                 final_sign,
  output logic        [DST_EXP_WIDTH-1:0]      final_exponent,
  output logic        [DST_PRECISION_BITS-1:0] final_mantissa,
  output logic                                 sticky_after_norm
);
  localparam int unsigned ALIGN_WIDTH       = DST_PRECISION_BITS + 2;
  localparam int unsigned ALIGN_SHAMT_WIDTH = $clog2(ALIGN_WIDTH + 1);
  localparam int unsigned SUM_WIDTH         = DST_PRECISION_BITS + 4;
  localparam int unsigned SUM_LZC_WIDTH     = cc_pkg::idx_width(SUM_WIDTH);

  logic                            swap;
  fp_dst_t                         operand_big, operand_small;
  logic [SUPER_DST_EXP_BITS-1:0]   exponent_big, exponent_small, exponent_difference;
  logic [DST_PRECISION_BITS-1:0]   mantissa_big, mantissa_small;
  logic [ALIGN_SHAMT_WIDTH-1:0]    align_shamt;
  logic [ALIGN_WIDTH-1:0]          aligned_small, align_sticky_bits;
  logic                            effective_subtraction;
  logic [SUM_WIDTH-1:0]            addend_big, addend_small, sum;
  logic [SUM_LZC_WIDTH-1:0]        sum_lzc;
  logic                            sum_zero;
  logic                            result_is_subnormal;
  logic [SUM_LZC_WIDTH-1:0]        norm_shamt;
  logic [SUM_WIDTH-1:0]            sum_normalized;
  logic                            zero_sign;

  assign swap          = {operand_b.exponent, operand_b.mantissa} > {operand_a.exponent, operand_a.mantissa};
  assign operand_big   = swap ? operand_b : operand_a;
  assign operand_small = swap ? operand_a : operand_b;

  assign exponent_big        = operand_big.exponent   + (operand_big.exponent   == '0);
  assign exponent_small      = operand_small.exponent + (operand_small.exponent == '0);
  assign mantissa_big        = {(operand_big.exponent   != '0), operand_big.mantissa};
  assign mantissa_small      = {(operand_small.exponent != '0), operand_small.mantissa};
  assign exponent_difference = exponent_big - exponent_small;

  assign align_shamt = (exponent_difference > ALIGN_WIDTH) ? ALIGN_WIDTH : exponent_difference[ALIGN_SHAMT_WIDTH-1:0];

  assign {aligned_small, align_sticky_bits} = {mantissa_small, 2'b00, ALIGN_WIDTH'(0)} >> align_shamt;

  assign effective_subtraction = operand_big.sign ^ operand_small.sign;
  assign addend_big            = {1'b0, mantissa_big, 3'b000};
  assign addend_small          = {1'b0, aligned_small, |align_sticky_bits};
  assign sum                   = addend_big + (effective_subtraction ? ~addend_small : addend_small)
                                 + SUM_WIDTH'(effective_subtraction);

  cc_lzc #(
    .Width ( SUM_WIDTH                    ),
    .Mode  ( cc_pkg::LZC_LEADING_ZERO_CNT )
  ) i_sum_lzc (
    .in_i    ( sum      ),
    .cnt_o   ( sum_lzc  ),
    .empty_o ( sum_zero )
  );

  assign result_is_subnormal = (SUPER_DST_EXP_BITS'(sum_lzc) > exponent_big);
  assign norm_shamt          = result_is_subnormal ? exponent_big[SUM_LZC_WIDTH-1:0] : sum_lzc;
  assign sum_normalized      = sum << norm_shamt;

  assign zero_sign = (operand_a.sign == operand_b.sign) ? operand_a.sign : (rnd_mode == fpnew_pkg::RDN);

  assign final_sign        = sum_zero ? zero_sign : operand_big.sign;
  assign final_exponent    = (sum_zero || result_is_subnormal) ? '0 : (DST_EXP_WIDTH'(exponent_big) + 1 - sum_lzc);
  assign final_mantissa    = sum_normalized[SUM_WIDTH-2-:DST_PRECISION_BITS];
  assign sticky_after_norm = |sum_normalized[SUM_WIDTH-DST_PRECISION_BITS-2:0];
endmodule

module fpnew_mxdotp_round
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter fpnew_pkg::fmt_logic_t FpDstFmtConfig = MxdotpDstFpFmtConfig
) (
  input  logic                                 clk_i,
  input  logic                                 rst_ni,
  input  logic                                 final_sign,
  input  logic        [DST_EXP_WIDTH-1:0]      final_exponent,
  input  logic        [DST_PRECISION_BITS-1:0] final_mantissa,
  input  logic                                 sticky_after_norm,
  input  fpnew_pkg::fp_format_e                dst_fmt,
  input  fpnew_pkg::roundmode_e                rnd_mode,
  output logic        [DST_WIDTH-1:0]          result,
  output fpnew_pkg::status_t                   status
);
  logic                                                              of_before_round;
  logic [NUM_FORMATS-1:0][SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] fmt_pre_round_abs;
  logic [NUM_FORMATS-1:0][1:0]                                       fmt_round_sticky_bits;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0]                  pre_round_abs;
  logic [1:0]                                                        round_sticky_bits;
  logic                                                              rounded_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0]                  rounded_abs;
  logic                                                              result_zero;
  logic [NUM_FORMATS-1:0][DST_WIDTH-1:0]                             fmt_result;
  logic [NUM_FORMATS-1:0]                                            fmt_of_after_round;
  logic [NUM_FORMATS-1:0]                                            fmt_uf_after_round;
  logic                                                              of_after_round;
  logic                                                              uf_after_round;
  logic                                                              inexact;

  assign of_before_round = (final_exponent >= DST_EXP_WIDTH'(2**SUPER_DST_EXP_BITS - 1));

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_res_assemble
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpDstFmtConfig[fmt]) begin : active_dst_format
      logic [EXP_BITS-1:0] pre_round_exponent;
      logic [MAN_BITS-1:0] pre_round_mantissa;

      assign pre_round_exponent     = of_before_round ? EXP_BITS'(2**EXP_BITS - 2) : final_exponent[EXP_BITS-1:0];
      assign pre_round_mantissa     = of_before_round ? '1 : final_mantissa[SUPER_DST_MAN_BITS-:MAN_BITS];
      assign fmt_pre_round_abs[fmt] = {pre_round_exponent, pre_round_mantissa};

      assign fmt_round_sticky_bits[fmt][1] = final_mantissa[SUPER_DST_MAN_BITS-MAN_BITS] | of_before_round;
      if (MAN_BITS < SUPER_DST_MAN_BITS) begin : narrow_sticky
        assign fmt_round_sticky_bits[fmt][0] = (|final_mantissa[SUPER_DST_MAN_BITS-MAN_BITS-1:0]) | sticky_after_norm |
                                               of_before_round;
      end else begin : normal_sticky
        assign fmt_round_sticky_bits[fmt][0] = sticky_after_norm | of_before_round;
      end
    end else begin : inactive_format
      assign fmt_pre_round_abs[fmt]     = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_round_sticky_bits[fmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  assign pre_round_abs     = fmt_pre_round_abs[dst_fmt];
  assign round_sticky_bits = fmt_round_sticky_bits[dst_fmt];

  fpnew_rounding #(
    .AbsWidth ( SUPER_DST_EXP_BITS + SUPER_DST_MAN_BITS )
  ) i_fpnew_rounding (
    .clk_i                      ( clk_i             ),
    .rst_ni                     ( rst_ni            ),
    .id_i                       ( '0                ),
    .abs_value_i                ( pre_round_abs     ),
    .en_rsr_i                   ( 1'b0              ),
    .sign_i                     ( final_sign        ),
    .round_sticky_bits_i        ( round_sticky_bits ),
    .stochastic_rounding_bits_i ( '0                ),
    .rnd_mode_i                 ( rnd_mode          ),
    .effective_subtraction_i    ( 1'b0              ),
    .abs_rounded_o              ( rounded_abs       ),
    .sign_o                     ( rounded_sign      ),
    .exact_zero_o               ( result_zero       )
  );

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_sign_inject
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpDstFmtConfig[fmt]) begin : active_dst_format
      always_comb begin : post_process
        fmt_uf_after_round[fmt]       = (rounded_abs[EXP_BITS+MAN_BITS-1:MAN_BITS] == '0);
        fmt_of_after_round[fmt]       = (rounded_abs[EXP_BITS+MAN_BITS-1:MAN_BITS] == '1);
        fmt_result[fmt]               = '1;
        fmt_result[fmt][FP_WIDTH-1:0] = {rounded_sign, rounded_abs[EXP_BITS+MAN_BITS-1:0]};
      end
    end else begin : inactive_format
      assign fmt_uf_after_round[fmt] = fpnew_pkg::DONT_CARE;
      assign fmt_of_after_round[fmt] = fpnew_pkg::DONT_CARE;
      assign fmt_result[fmt]         = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  assign of_after_round = fmt_of_after_round[dst_fmt];
  assign uf_after_round = fmt_uf_after_round[dst_fmt];

  assign inexact = (|round_sticky_bits) | of_before_round | of_after_round;

  assign result = fmt_result[dst_fmt];
  assign status = '{NV: 1'b0, DZ: 1'b0, OF: of_before_round | of_after_round, UF: uf_after_round & inexact, NX: inexact};
endmodule
