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

module fpnew_mxdotp_slim_decode
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter fpnew_pkg::fmt_logic_t FmtConfig   = '0,
  parameter int unsigned           NumOperands = 1,
  parameter int unsigned           OutExpBits  = 1,
  parameter int unsigned           OutManBits  = 1
) (
  input  logic                [NumOperands-1:0][SRC_WIDTH-1:0]  operands_i,
  input  logic                [NumOperands-1:0]                 is_boxed_i,
  input  logic                [NUM_FORMATS-1:0]                 fmt_sel_i,
  output logic                [NumOperands-1:0]                 sign_o,
  output logic                [NumOperands-1:0][OutExpBits-1:0] exponent_o,
  output logic                [NumOperands-1:0][OutManBits-1:0] mantissa_o,
  output fpnew_pkg::fp_info_t [NumOperands-1:0]                 info_o
);

  logic [NUM_FORMATS-1:0]                                  sel;
  logic [NUM_FORMATS-1:0]                                  ieee_fmt;
  logic [NUM_FORMATS-1:0]                                  e4m3_fmt;
  logic [NUM_FORMATS-1:0][NumOperands-1:0]                 cand_sign;
  logic [NUM_FORMATS-1:0][NumOperands-1:0][OutExpBits-1:0] cand_exponent;
  logic [NUM_FORMATS-1:0][NumOperands-1:0][OutManBits-1:0] cand_mantissa;
  logic [NUM_FORMATS-1:0][NumOperands-1:0]                 cand_exp_ones;
  logic [NUM_FORMATS-1:0][NumOperands-1:0]                 cand_man_ones;
  logic                                                    ieee_sel;
  logic                                                    e4m3_sel;

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_fmt
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam logic        NO_SPEC  = (fmt == int'(fpnew_pkg::FP6)) || (fmt == int'(fpnew_pkg::FP6ALT)) ||
                                       (fmt == int'(fpnew_pkg::FP4));
    localparam logic        E4M3     = (fmt == int'(fpnew_pkg::FP8ALT));

    if (FmtConfig[fmt]) begin : active_format
      assign sel[fmt]      = fmt_sel_i[fmt];
      assign ieee_fmt[fmt] = !NO_SPEC && !E4M3;
      assign e4m3_fmt[fmt] = E4M3;
      for (genvar op = 0; op < int'(NumOperands); op++) begin : gen_operands
        assign cand_sign[fmt][op]     = sel[fmt] & operands_i[op][FP_WIDTH-1];
        assign cand_exponent[fmt][op] = {OutExpBits{sel[fmt]}} & OutExpBits'(operands_i[op][MAN_BITS+:EXP_BITS]);
        assign cand_mantissa[fmt][op] = {OutManBits{sel[fmt]}} &
                                        (OutManBits'(operands_i[op][MAN_BITS-1:0]) << (OutManBits - MAN_BITS));
        if (NO_SPEC) begin : gen_no_special
          assign cand_exp_ones[fmt][op] = 1'b0;
          assign cand_man_ones[fmt][op] = 1'b0;
        end else begin : gen_special
          assign cand_exp_ones[fmt][op] = sel[fmt] & (operands_i[op][MAN_BITS+:EXP_BITS] == '1);
          assign cand_man_ones[fmt][op] = sel[fmt] & (operands_i[op][MAN_BITS-1:0] == '1);
        end
      end
    end else begin : inactive_format
      assign sel[fmt]           = 1'b0;
      assign ieee_fmt[fmt]      = 1'b0;
      assign e4m3_fmt[fmt]      = 1'b0;
      assign cand_sign[fmt]     = '0;
      assign cand_exponent[fmt] = '0;
      assign cand_mantissa[fmt] = '0;
      assign cand_exp_ones[fmt] = '0;
      assign cand_man_ones[fmt] = '0;
    end
  end

  assign ieee_sel = |(sel & ieee_fmt);
  assign e4m3_sel = |(sel & e4m3_fmt);

  for (genvar op = 0; op < int'(NumOperands); op++) begin : gen_classify
    logic                  sign;
    logic [OutExpBits-1:0] exponent;
    logic [OutManBits-1:0] mantissa;
    logic                  exp_ones;
    logic                  man_ones;
    logic                  boxed;
    logic                  exp_zero;
    logic                  man_zero;
    logic                  is_nan;
    logic                  is_signalling;

    always_comb begin : select_fields
      sign     = 1'b0;
      exponent = '0;
      mantissa = '0;
      exp_ones = 1'b0;
      man_ones = 1'b0;
      for (int unsigned fmt = 0; fmt < NUM_FORMATS; fmt++) begin
        sign     |= cand_sign[fmt][op];
        exponent |= cand_exponent[fmt][op];
        mantissa |= cand_mantissa[fmt][op];
        exp_ones |= cand_exp_ones[fmt][op];
        man_ones |= cand_man_ones[fmt][op];
      end
    end

    assign boxed         = is_boxed_i[op];
    assign exp_zero      = (exponent == '0);
    assign man_zero      = (mantissa == '0);
    assign is_nan        = ((ieee_sel || e4m3_sel) && !boxed) || (ieee_sel && exp_ones && !man_zero) ||
                           (e4m3_sel && exp_ones && man_ones);
    assign is_signalling = boxed && is_nan && !mantissa[OutManBits-1];

    assign sign_o[op]                = sign;
    assign exponent_o[op]            = exponent;
    assign mantissa_o[op]            = mantissa;
    assign info_o[op].is_normal      = boxed && !exp_zero && !(ieee_sel && exp_ones) && !(e4m3_sel && exp_ones && man_ones);
    assign info_o[op].is_subnormal   = boxed && exp_zero && !man_zero;
    assign info_o[op].is_zero        = boxed && exp_zero && man_zero;
    assign info_o[op].is_inf         = boxed && ieee_sel && exp_ones && man_zero;
    assign info_o[op].is_nan         = is_nan;
    assign info_o[op].is_signalling  = is_signalling;
    assign info_o[op].is_quiet       = is_nan && !is_signalling;
    assign info_o[op].is_boxed       = boxed;
  end
endmodule


module fpnew_mxdotp_slim_classifier
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter fpnew_pkg::fmt_logic_t FpSrcFmtConfig = MxdotpSrcFpFmtConfig,
  parameter fpnew_pkg::fmt_logic_t FpDstFmtConfig = MxdotpDstFpFmtConfig,
  parameter int unsigned           VectorSize     = 8,
  parameter int unsigned           FP6VectorSize  = 3,
  parameter int unsigned           FP4VectorSize  = 5
) (
  input  logic                [2*VectorSize-1:0][SRC_WIDTH-1:0]    operands_post_inp_pipe,
  input  logic                [2*FP6VectorSize-1:0][SRC_WIDTH-1:0] fp6_operands_post_inp_pipe,
  input  logic                [2*FP4VectorSize-1:0][SRC_WIDTH-1:0] fp4_operands_post_inp_pipe,
  input  logic signed         [1:0][SCALE_WIDTH-1:0]               operands_c_in,
  input  logic                [DST_WIDTH-1:0]                      operand_d_in,
  input  logic                [NUM_FORMATS-1:0][2:0]               is_boxed,
  input  fpnew_pkg::fp_format_e                                    src_fmt,
  input  logic                                                     src_is_int,
  input  fpnew_pkg::fp_format_e                                    dst_fmt,
  output fpnew_pkg::fp_info_t [VectorSize-1:0]                     info_a,
  output fpnew_pkg::fp_info_t [FP6VectorSize-1:0]                  fp6_info_a,
  output fpnew_pkg::fp_info_t [FP4VectorSize-1:0]                  fp4_info_a,
  output fpnew_pkg::fp_info_t [VectorSize-1:0]                     info_b,
  output fpnew_pkg::fp_info_t [FP6VectorSize-1:0]                  fp6_info_b,
  output fpnew_pkg::fp_info_t [FP4VectorSize-1:0]                  fp4_info_b,
  output fpnew_pkg::fp_info_t [1:0]                                info_c,
  output fpnew_pkg::fp_info_t                                      info_d,
  output fp_src_t             [VectorSize-1:0]                     operands_a,
  output fp6_src_t            [FP6VectorSize-1:0]                  fp6_operands_a,
  output fp4_src_t            [FP4VectorSize-1:0]                  fp4_operands_a,
  output fp_src_t             [VectorSize-1:0]                     operands_b,
  output fp6_src_t            [FP6VectorSize-1:0]                  fp6_operands_b,
  output fp4_src_t            [FP4VectorSize-1:0]                  fp4_operands_b,
  output logic signed         [1:0][SCALE_WIDTH-1:0]               operands_c,
  output fp_dst_t                                                  operand_d
);

  localparam fpnew_pkg::fmt_logic_t FP6_LANE_FMTS = FpSrcFmtConfig & 9'b000000111;
  localparam fpnew_pkg::fmt_logic_t FP4_LANE_FMTS = FpSrcFmtConfig & 9'b000000001;

  logic [NUM_FORMATS-1:0]     fmt_sel;
  logic [NUM_FORMATS-1:0]     dst_sel;
  logic                       boxed_a;
  logic                       boxed_b;
  logic [2*VectorSize-1:0]    fp8_boxed;
  logic [2*FP6VectorSize-1:0] fp6_boxed;
  logic [2*FP4VectorSize-1:0] fp4_boxed;

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_fmt_sel
    assign fmt_sel[fmt] = FpSrcFmtConfig[fmt] && !src_is_int && (src_fmt == fpnew_pkg::fp_format_e'(fmt));
    assign dst_sel[fmt] = FpDstFmtConfig[fmt] && (dst_fmt == fpnew_pkg::fp_format_e'(fmt));
  end

  always_comb begin : boxed_select
    boxed_a = 1'b0;
    boxed_b = 1'b0;
    for (int unsigned fmt = 0; fmt < NUM_FORMATS; fmt++) begin
      boxed_a |= fmt_sel[fmt] & is_boxed[fmt][0];
      boxed_b |= fmt_sel[fmt] & is_boxed[fmt][1];
    end
  end

  assign fp8_boxed = {{VectorSize{boxed_b}}, {VectorSize{boxed_a}}};
  assign fp6_boxed = {{FP6VectorSize{boxed_b}}, {FP6VectorSize{boxed_a}}};
  assign fp4_boxed = {{FP4VectorSize{boxed_b}}, {FP4VectorSize{boxed_a}}};

  logic                [2*VectorSize-1:0]                     fp8_sign;
  logic                [2*VectorSize-1:0][SUPER_EXP_BITS-1:0] fp8_exponent;
  logic                [2*VectorSize-1:0][SUPER_MAN_BITS-1:0] fp8_mantissa;
  fpnew_pkg::fp_info_t [2*VectorSize-1:0]                     fp8_info;

  logic                [2*FP6VectorSize-1:0]                   fp6_sign;
  logic                [2*FP6VectorSize-1:0][FP6_EXP_BITS-1:0] fp6_exponent;
  logic                [2*FP6VectorSize-1:0][FP6_MAN_BITS-1:0] fp6_mantissa;
  fpnew_pkg::fp_info_t [2*FP6VectorSize-1:0]                   fp6_info;

  logic                [2*FP4VectorSize-1:0]                   fp4_sign;
  logic                [2*FP4VectorSize-1:0][FP4_EXP_BITS-1:0] fp4_exponent;
  logic                [2*FP4VectorSize-1:0][FP4_MAN_BITS-1:0] fp4_mantissa;
  fpnew_pkg::fp_info_t [2*FP4VectorSize-1:0]                   fp4_info;

  fpnew_mxdotp_slim_decode #(
    .FmtConfig   ( FpSrcFmtConfig ),
    .NumOperands ( 2*VectorSize   ),
    .OutExpBits  ( SUPER_EXP_BITS ),
    .OutManBits  ( SUPER_MAN_BITS )
  ) i_fp8_decode (
    .operands_i  ( operands_post_inp_pipe ),
    .is_boxed_i  ( fp8_boxed              ),
    .fmt_sel_i   ( fmt_sel                ),
    .sign_o      ( fp8_sign               ),
    .exponent_o  ( fp8_exponent           ),
    .mantissa_o  ( fp8_mantissa           ),
    .info_o      ( fp8_info               )
  );

  fpnew_mxdotp_slim_decode #(
    .FmtConfig   ( FP6_LANE_FMTS   ),
    .NumOperands ( 2*FP6VectorSize ),
    .OutExpBits  ( FP6_EXP_BITS    ),
    .OutManBits  ( FP6_MAN_BITS    )
  ) i_fp6_decode (
    .operands_i  ( fp6_operands_post_inp_pipe ),
    .is_boxed_i  ( fp6_boxed                  ),
    .fmt_sel_i   ( fmt_sel                    ),
    .sign_o      ( fp6_sign                   ),
    .exponent_o  ( fp6_exponent               ),
    .mantissa_o  ( fp6_mantissa               ),
    .info_o      ( fp6_info                   )
  );

  fpnew_mxdotp_slim_decode #(
    .FmtConfig   ( FP4_LANE_FMTS   ),
    .NumOperands ( 2*FP4VectorSize ),
    .OutExpBits  ( FP4_EXP_BITS    ),
    .OutManBits  ( FP4_MAN_BITS    )
  ) i_fp4_decode (
    .operands_i  ( fp4_operands_post_inp_pipe ),
    .is_boxed_i  ( fp4_boxed                  ),
    .fmt_sel_i   ( fmt_sel                    ),
    .sign_o      ( fp4_sign                   ),
    .exponent_o  ( fp4_exponent               ),
    .mantissa_o  ( fp4_mantissa               ),
    .info_o      ( fp4_info                   )
  );

  logic                [NUM_FORMATS-1:0]                         cand_dst_sign;
  logic                [NUM_FORMATS-1:0][SUPER_DST_EXP_BITS-1:0] cand_dst_exponent;
  logic                [NUM_FORMATS-1:0][SUPER_DST_MAN_BITS-1:0] cand_dst_mantissa;
  fpnew_pkg::fp_info_t [NUM_FORMATS-1:0]                         cand_dst_info;

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_dst_fmt
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpDstFmtConfig[fmt]) begin : active_dst_format
      fpnew_pkg::fp_info_t           dst_info;
      logic [SUPER_DST_MAN_BITS-1:0] dst_mantissa;

      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( operand_d_in[FP_WIDTH-1:0] ),
        .is_boxed_i  ( is_boxed[fmt][2]           ),
        .info_o      ( dst_info                   )
      );

      assign dst_mantissa            = {dst_info.is_normal, operand_d_in[MAN_BITS-1:0]} << (SUPER_DST_MAN_BITS - MAN_BITS);
      assign cand_dst_sign[fmt]      = dst_sel[fmt] & operand_d_in[FP_WIDTH-1];
      assign cand_dst_exponent[fmt]  = {SUPER_DST_EXP_BITS{dst_sel[fmt]}} & SUPER_DST_EXP_BITS'(operand_d_in[MAN_BITS+:EXP_BITS]);
      assign cand_dst_mantissa[fmt]  = {SUPER_DST_MAN_BITS{dst_sel[fmt]}} & dst_mantissa;
      assign cand_dst_info[fmt]      = {$bits(fpnew_pkg::fp_info_t){dst_sel[fmt]}} & dst_info;
    end else begin : inactive_dst_format
      assign cand_dst_sign[fmt]      = 1'b0;
      assign cand_dst_exponent[fmt]  = '0;
      assign cand_dst_mantissa[fmt]  = '0;
      assign cand_dst_info[fmt]      = '0;
    end
  end

  always_comb begin : op_select
    for (int i = 0; i < VectorSize; i++) begin
      operands_a[i] = {fp8_sign[i], fp8_exponent[i], fp8_mantissa[i]} |
                      ({$bits(fp_src_t){src_is_int}} & $bits(fp_src_t)'(operands_post_inp_pipe[i]));
      operands_b[i] = {fp8_sign[i+VectorSize], fp8_exponent[i+VectorSize], fp8_mantissa[i+VectorSize]} |
                      ({$bits(fp_src_t){src_is_int}} & $bits(fp_src_t)'(operands_post_inp_pipe[i+VectorSize]));
      info_a[i]     = fp8_info[i];
      info_b[i]     = fp8_info[i+VectorSize];
    end
    for (int i = 0; i < FP6VectorSize; i++) begin
      fp6_operands_a[i] = {fp6_sign[i], fp6_exponent[i], fp6_mantissa[i]} |
                          ({$bits(fp6_src_t){src_is_int}} & $bits(fp6_src_t)'(fp6_operands_post_inp_pipe[i]));
      fp6_operands_b[i] = {fp6_sign[i+FP6VectorSize], fp6_exponent[i+FP6VectorSize], fp6_mantissa[i+FP6VectorSize]} |
                          ({$bits(fp6_src_t){src_is_int}} & $bits(fp6_src_t)'(fp6_operands_post_inp_pipe[i+FP6VectorSize]));
      fp6_info_a[i]     = fp6_info[i];
      fp6_info_b[i]     = fp6_info[i+FP6VectorSize];
    end
    for (int i = 0; i < FP4VectorSize; i++) begin
      fp4_operands_a[i] = {fp4_sign[i], fp4_exponent[i], fp4_mantissa[i]} |
                          ({$bits(fp4_src_t){src_is_int}} & $bits(fp4_src_t)'(fp4_operands_post_inp_pipe[i]));
      fp4_operands_b[i] = {fp4_sign[i+FP4VectorSize], fp4_exponent[i+FP4VectorSize], fp4_mantissa[i+FP4VectorSize]} |
                          ({$bits(fp4_src_t){src_is_int}} & $bits(fp4_src_t)'(fp4_operands_post_inp_pipe[i+FP4VectorSize]));
      fp4_info_a[i]     = fp4_info[i];
      fp4_info_b[i]     = fp4_info[i+FP4VectorSize];
    end
    for (int i = 0; i < 2; i++) begin
      operands_c[i] = signed'(operands_c_in[i]) - 127;
      info_c[i]     = '{is_normal: 1'b1, is_nan: operands_c_in[i] == 2**SCALE_WIDTH-1, is_boxed: 1'b1, default: 1'b0};
    end
    operand_d = '0;
    info_d    = '0;
    for (int unsigned fmt = 0; fmt < NUM_FORMATS; fmt++) begin
      operand_d |= {cand_dst_sign[fmt], cand_dst_exponent[fmt], cand_dst_mantissa[fmt]};
      info_d    |= cand_dst_info[fmt];
    end
  end
endmodule
