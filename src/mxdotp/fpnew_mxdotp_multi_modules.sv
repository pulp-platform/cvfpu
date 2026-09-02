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

// Author: Gamze Islamoglu <gislamoglu@iis.ee.ethz.ch>

// Classifies and unpacks input operands (FP8/FP6/FP4 vectors, scales, accumulator) into sign/exponent/mantissa
// fields and fp_info structs. Converts unsigned scales (0-255) to signed offsets (-127 to +128).
module fpnew_mxdotp_classifier
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter fpnew_pkg::fmt_logic_t FpSrcFmtConfig = MxdotpSrcFpFmtConfig,
  parameter fpnew_pkg::fmt_logic_t FpDstFmtConfig = MxdotpDstFpFmtConfig,
  parameter int unsigned           VectorSize     = 8,
  parameter int unsigned           FP6VectorSize  = 3,
  parameter int unsigned           FP4VectorSize  = 5,
  parameter int unsigned           NumInpRegs     = 0,
  // Do not change the following parameters
  localparam int unsigned          NUM_OPERANDS   = 2*VectorSize+1
) (
  // Input signals
  input logic [2*VectorSize-1:0][SRC_WIDTH-1:0] operands_post_inp_pipe,
  // Per-format packing views (see fpnew_mxdotp_multi): the classifier bank
  // reads these instead of the src_fmt-muxed array.
  input logic [2*VectorSize-1:0][SRC_WIDTH-1:0] operands_default_view,
  input logic [2*VectorSize-1:0][SRC_WIDTH-1:0] operands_fp6_view,
  input logic [2*FP6VectorSize-1:0][SRC_WIDTH-1:0] fp6_operands_post_inp_pipe,
  input logic [2*FP4VectorSize-1:0][SRC_WIDTH-1:0] fp4_operands_post_inp_pipe,
  input logic signed [1:0][SCALE_WIDTH-1:0] operands_c_in,
  input logic [DST_WIDTH-1:0] operand_d_in,
  input logic [0:NumInpRegs][NUM_FORMATS-1:0][NUM_OPERANDS-1:0] inp_pipe_is_boxed,
  input fpnew_pkg::fp_format_e src_fmt,
  input logic src_is_int,
  input fpnew_pkg::fp_format_e dst_fmt,
  input logic [0:NumInpRegs] inp_pipe_op_mod,
  // Output signals
  output fpnew_pkg::fp_info_t [VectorSize-1:0] info_a,
  output fpnew_pkg::fp_info_t [FP6VectorSize-1:0] fp6_info_a,
  output fpnew_pkg::fp_info_t [FP4VectorSize-1:0] fp4_info_a,
  output fpnew_pkg::fp_info_t [VectorSize-1:0] info_b,
  output fpnew_pkg::fp_info_t [FP6VectorSize-1:0] fp6_info_b,
  output fpnew_pkg::fp_info_t [FP4VectorSize-1:0] fp4_info_b,
  output fpnew_pkg::fp_info_t [1:0] info_c,
  output fpnew_pkg::fp_info_t info_d,
  output fp_src_t [VectorSize-1:0] operands_a,
  output fp6_src_t [FP6VectorSize-1:0] fp6_operands_a,
  output fp4_src_t [FP4VectorSize-1:0] fp4_operands_a,
  output fp_src_t [VectorSize-1:0] operands_b,
  output fp6_src_t [FP6VectorSize-1:0] fp6_operands_b,
  output fp4_src_t [FP4VectorSize-1:0] fp4_operands_b,
  output logic signed [1:0][SCALE_WIDTH-1:0] operands_c,
  output fp_dst_t operand_d
);

  // -----------------
  // Source operands
  // -----------------
  logic        [NUM_FORMATS-1:0][2*VectorSize-1:0]                     fmt_sign;
  logic signed [NUM_FORMATS-1:0][2*VectorSize-1:0][SUPER_EXP_BITS-1:0] fmt_exponent;
  logic        [NUM_FORMATS-1:0][2*VectorSize-1:0][SUPER_MAN_BITS-1:0] fmt_mantissa;

  fpnew_pkg::fp_info_t [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] info_q;

  // FP6
  logic        [NUM_FORMATS-1:0][2*FP6VectorSize-1:0]                   fp6_fmt_sign;
  logic signed [NUM_FORMATS-1:0][2*FP6VectorSize-1:0][FP6_EXP_BITS-1:0] fp6_fmt_exponent;
  logic        [NUM_FORMATS-1:0][2*FP6VectorSize-1:0][FP6_MAN_BITS-1:0] fp6_fmt_mantissa;

  fpnew_pkg::fp_info_t [NUM_FORMATS-1:0][2*FP6VectorSize-1:0] fp6_info_q;

  // FP4
  logic        [NUM_FORMATS-1:0][2*FP4VectorSize-1:0]                   fp4_fmt_sign;
  logic signed [NUM_FORMATS-1:0][2*FP4VectorSize-1:0][FP4_EXP_BITS-1:0] fp4_fmt_exponent;
  logic        [NUM_FORMATS-1:0][2*FP4VectorSize-1:0][FP4_MAN_BITS-1:0] fp4_fmt_mantissa;

  fpnew_pkg::fp_info_t [NUM_FORMATS-1:0][2*FP4VectorSize-1:0] fp4_info_q;

  // FP Input initialization (Src)
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : fmt_src_init_inputs
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpSrcFmtConfig[fmt]) begin : active_src_format
      logic [2*VectorSize-1:0][FP_WIDTH-1:0]  trimmed_ops;
      logic [2*VectorSize-1:0][SRC_WIDTH-1:0] sel_ops;

      // ELABORATION-TIME choice, not a multiplexer: this classifier's result
      // is only ever consumed through `[src_fmt]` below, so it may be wired
      // to the packing that holds when src_fmt == fmt.
      if ((fmt == int'(fpnew_pkg::FP6)) || (fmt == int'(fpnew_pkg::FP6ALT))) begin : gen_fp6_pack
        assign sel_ops = operands_fp6_view;
      end else begin : gen_default_pack
        assign sel_ops = operands_default_view;
      end

      // Classify input
      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 2*VectorSize                 ),
        .MX          ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_ops                                          ),
        .is_boxed_i  ( inp_pipe_is_boxed[NumInpRegs][fmt][2*VectorSize-1:0] ),
        .info_o      ( info_q[fmt][2*VectorSize-1:0]                        )
      );
      for (genvar op = 0; op < 2*VectorSize; op++) begin : gen_operands
        assign trimmed_ops[op]       = sel_ops[op][FP_WIDTH-1:0];
        assign fmt_sign[fmt][op]     = sel_ops[op][FP_WIDTH-1];
        assign fmt_exponent[fmt][op] = signed'({1'b0, sel_ops[op][MAN_BITS+:EXP_BITS]});
        assign fmt_mantissa[fmt][op] = sel_ops[op][MAN_BITS-1:0] <<
                                       (SUPER_MAN_BITS - MAN_BITS); // move to left of mantissa
      end
    end else begin : inactive_src_format
      assign info_q[fmt][2*VectorSize-1:0]  = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_sign[fmt]                  = fpnew_pkg::DONT_CARE;             // format disabled
      assign fmt_exponent[fmt]              = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_mantissa[fmt]              = '{default: fpnew_pkg::DONT_CARE}; // format disabled
    end
  end

  if (FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) begin : fp6_classifier
    for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : fp6_fmt_src_init_inputs
      // Set up some constants
      localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
      localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
      localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

      if (FpSrcFmtConfig[fmt]) begin : active_src_format
        logic [2*FP6VectorSize-1:0][FP_WIDTH-1:0] trimmed_ops;

        // Classify input
        fpnew_classifier #(
          .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
          .NumOperands ( 2*FP6VectorSize              ),
          .MX          ( 1                            )
        ) i_fpnew_classifier (
          .operands_i  ( trimmed_ops                                             ),
          .is_boxed_i  ( inp_pipe_is_boxed[NumInpRegs][fmt][2*FP6VectorSize-1:0] ),
          .info_o      ( fp6_info_q[fmt][2*FP6VectorSize-1:0]                    )
        );
        for (genvar op = 0; op < 2*FP6VectorSize; op++) begin : gen_operands
          assign trimmed_ops[op]           = fp6_operands_post_inp_pipe[op][FP_WIDTH-1:0];
          assign fp6_fmt_sign[fmt][op]     = fp6_operands_post_inp_pipe[op][FP_WIDTH-1];
          assign fp6_fmt_exponent[fmt][op] = fp6_operands_post_inp_pipe[op][MAN_BITS+:EXP_BITS];
          assign fp6_fmt_mantissa[fmt][op] = fp6_operands_post_inp_pipe[op][MAN_BITS-1:0] <<
                                        (SUPER_MAN_BITS - MAN_BITS); // move to left of mantissa
        end
      end else begin : inactive_src_format
        assign fp6_info_q[fmt][2*FP6VectorSize-1:0] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
        assign fp6_fmt_sign[fmt]                    = fpnew_pkg::DONT_CARE;             // format disabled
        assign fp6_fmt_exponent[fmt]                = '{default: fpnew_pkg::DONT_CARE}; // format disabled
        assign fp6_fmt_mantissa[fmt]                = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      end
    end
  end

  if (FpSrcFmtConfig[fpnew_pkg::FP4]) begin : fp4_classifier
    for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : fp4_fmt_src_init_inputs
      // Set up some constants
      localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
      localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
      localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

      if (FpSrcFmtConfig[fmt]) begin : active_src_format
        logic [2*FP4VectorSize-1:0][FP_WIDTH-1:0] trimmed_ops;

        // Classify input
        fpnew_classifier #(
          .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
          .NumOperands ( 2*FP4VectorSize              ),
          .MX          ( 1                            )
        ) i_fpnew_classifier (
          .operands_i  ( trimmed_ops                                             ),
          .is_boxed_i  ( inp_pipe_is_boxed[NumInpRegs][fmt][2*FP4VectorSize-1:0] ),
          .info_o      ( fp4_info_q[fmt][2*FP4VectorSize-1:0]                    )
        );
        for (genvar op = 0; op < 2*FP4VectorSize; op++) begin : gen_operands
          assign trimmed_ops[op]           = fp4_operands_post_inp_pipe[op][FP_WIDTH-1:0];
          assign fp4_fmt_sign[fmt][op]     = fp4_operands_post_inp_pipe[op][FP_WIDTH-1];
          assign fp4_fmt_exponent[fmt][op] = fp4_operands_post_inp_pipe[op][MAN_BITS+:EXP_BITS];
          assign fp4_fmt_mantissa[fmt][op] = fp4_operands_post_inp_pipe[op][MAN_BITS-1:0];
        end
      end else begin : inactive_src_format
        assign fp4_info_q[fmt][2*FP4VectorSize-1:0] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
        assign fp4_fmt_sign[fmt]                    = fpnew_pkg::DONT_CARE;             // format disabled
        assign fp4_fmt_exponent[fmt]                = '{default: fpnew_pkg::DONT_CARE}; // format disabled
        assign fp4_fmt_mantissa[fmt]                = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      end
    end
  end

  // ----------------------------
  // Destination operand
  // ----------------------------
  logic        [NUM_FORMATS-1:0]                         fmt_dst_sign;
  logic signed [NUM_FORMATS-1:0][SUPER_DST_EXP_BITS-1:0] fmt_dst_exponent;
  logic        [NUM_FORMATS-1:0][SUPER_DST_MAN_BITS-1:0] fmt_dst_mantissa;

  // FP Input initialization (Src)
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : fmt_dst_init_inputs
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpDstFmtConfig[fmt]) begin : active_dst_format
      logic [FP_WIDTH-1:0] trimmed_dst_ops;
      logic                dst_ops_is_boxed;

      assign dst_ops_is_boxed = inp_pipe_is_boxed[NumInpRegs][fmt][NUM_OPERANDS-1];

      // Classify input
      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_dst_ops             ),
        .is_boxed_i  ( dst_ops_is_boxed            ),
        .info_o      ( info_q[fmt][NUM_OPERANDS-1] )
      );
      assign trimmed_dst_ops       = operand_d_in[FP_WIDTH-1:0];
      assign fmt_dst_sign[fmt]     = operand_d_in[FP_WIDTH-1];
      assign fmt_dst_exponent[fmt] = signed'({1'b0, operand_d_in[MAN_BITS+:EXP_BITS]});
      assign fmt_dst_mantissa[fmt] = {info_q[fmt][NUM_OPERANDS-1].is_normal, operand_d_in[MAN_BITS-1:0]}
                                         << (SUPER_DST_MAN_BITS - MAN_BITS);
    end else begin : inactive_dst_format
      assign info_q[fmt][NUM_OPERANDS-1] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_dst_sign[fmt]           = fpnew_pkg::DONT_CARE;             // format disabled
      assign fmt_dst_exponent[fmt]       = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_dst_mantissa[fmt]       = '{default: fpnew_pkg::DONT_CARE}; // format disabled
    end
  end

  // -------------------------------------------
  // Operation selection and operand adjustment
  // -------------------------------------------

  always_comb begin : op_select
    // Default assignments - packing-order-agnostic
    if (src_is_int) begin : gen_int_default_assignments
      // Integer operands
      for (int i = 0; i < VectorSize; i++) begin : gen_default_assignments_int
        operands_a[i] = operands_post_inp_pipe[i];
        operands_b[i] = operands_post_inp_pipe[i+VectorSize];
        // set to zero
        info_a[i]     = fpnew_pkg::fp_info_t'(0);
        info_b[i]     = fpnew_pkg::fp_info_t'(0);
      end
      for (int i = 0; i < FP6VectorSize; i++) begin : gen_default_assignments_fp6_int
        // FP6
        fp6_operands_a[i] = fp6_operands_post_inp_pipe[i];
        fp6_operands_b[i] = fp6_operands_post_inp_pipe[i+FP6VectorSize];
        // set to zero
        fp6_info_a[i]     = fpnew_pkg::fp_info_t'(0);
        fp6_info_b[i]     = fpnew_pkg::fp_info_t'(0);
      end
      for (int i = 0; i < FP4VectorSize; i++) begin : gen_default_assignments_fp4_int
        // FP4
        fp4_operands_a[i] = fp4_operands_post_inp_pipe[i];
        fp4_operands_b[i] = fp4_operands_post_inp_pipe[i+FP4VectorSize];
        // set to zero
        fp4_info_a[i]     = fpnew_pkg::fp_info_t'(0);
        fp4_info_b[i]     = fpnew_pkg::fp_info_t'(0);
      end
    end else begin : gen_fp_default_assignments
      // Floating-point operands
      for (int i = 0; i < VectorSize; i++) begin : gen_default_assignments_fp
        operands_a[i] = {fmt_sign[src_fmt][i], fmt_exponent[src_fmt][i], fmt_mantissa[src_fmt][i]};
        operands_b[i] = {fmt_sign[src_fmt][i+VectorSize], fmt_exponent[src_fmt][i+VectorSize], fmt_mantissa[src_fmt][i+VectorSize]};
        info_a[i]     = info_q[src_fmt][i];
        info_b[i]     = info_q[src_fmt][i+VectorSize];
      end
      for (int i = 0; i < FP6VectorSize; i++) begin : gen_default_assignments_fp6
        // FP6
        fp6_operands_a[i] = {fp6_fmt_sign[src_fmt][i], fp6_fmt_exponent[src_fmt][i], fp6_fmt_mantissa[src_fmt][i]};
        fp6_operands_b[i] = {fp6_fmt_sign[src_fmt][i+FP6VectorSize], fp6_fmt_exponent[src_fmt][i+FP6VectorSize], fp6_fmt_mantissa[src_fmt][i+FP6VectorSize]};
        fp6_info_a[i]     = fp6_info_q[src_fmt][i];
        fp6_info_b[i]     = fp6_info_q[src_fmt][i+FP6VectorSize];
      end
      for (int i = 0; i < FP4VectorSize; i++) begin : gen_default_assignments_fp4
        // FP4
        fp4_operands_a[i] = {fp4_fmt_sign[src_fmt][i], fp4_fmt_exponent[src_fmt][i], fp4_fmt_mantissa[src_fmt][i]};
        fp4_operands_b[i] = {fp4_fmt_sign[src_fmt][i+FP4VectorSize], fp4_fmt_exponent[src_fmt][i+FP4VectorSize], fp4_fmt_mantissa[src_fmt][i+FP4VectorSize]};
        fp4_info_a[i]     = fp4_info_q[src_fmt][i];
        fp4_info_b[i]     = fp4_info_q[src_fmt][i+FP4VectorSize];
      end
    end
    for (int i = 0; i < 2; i++) begin : gen_default_assignments_c
      operands_c[i] = signed'(operands_c_in[i]) - 127; // signed scale, 127 = signed'(2**(SCALE_WIDTH-1)-1)
      info_c[i] = '{is_normal: 1'b1, is_nan: operands_c_in[i] == 2**SCALE_WIDTH-1, is_boxed: 1'b1, default: 1'b0}; // normal, boxed value, scale can be NaN
    end
    operand_d = {fmt_dst_sign[dst_fmt], fmt_dst_exponent[dst_fmt], fmt_dst_mantissa[dst_fmt]};
    info_d    = info_q[dst_fmt][NUM_OPERANDS-1];
  end
endmodule

// Detects special cases (NaN, infinity, invalid operations like 0×inf) and generates canonical results.
// Only FP8 sources can have inf/nan; FP6 and FP4 have limited exponent ranges.
module fpnew_mxdotp_special_cases
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned VectorSize = 8
) (
  // Input signals
  input  fp_src_t [VectorSize-1:0]             operands_a,
  input  fp_src_t [VectorSize-1:0]             operands_b,
  input  logic signed [1:0][SCALE_WIDTH-1:0]   operands_c,
  input  fp_dst_t                              operand_d,
  input  fpnew_pkg::fp_info_t [VectorSize-1:0] info_a,
  input  fpnew_pkg::fp_info_t [VectorSize-1:0] info_b,
  input  fpnew_pkg::fp_info_t [1:0]            info_c,
  input  fpnew_pkg::fp_info_t                  info_d,
  // Output signals: the 4-bit special-case verdict (format independent).
  // fpnew_mxdotp_special_assemble turns it back into the 32-bit result and
  // the status word at the very end of the pipeline.
  output logic                                 result_is_special_raw,
  output logic                                 special_nv,
  output logic                                 special_is_inf,
  output logic                                 special_inf_sign
);

  // ---------------------
  // Input classification
  // ---------------------
  logic any_operand_inf;
  logic any_operand_nan;
  logic signalling_nan;
  logic any_produced_nan;
  logic any_pos_inf;
  logic any_neg_inf;

  // Intermediate signals for each condition
  logic [VectorSize-1:0] operand_inf_conditions;
  logic [VectorSize-1:0] operand_nan_conditions;
  logic [VectorSize-1:0] signalling_nan_conditions;
  logic [VectorSize-1:0] nan_conditions;
  logic [VectorSize-1:0] pos_inf_conditions;
  logic [VectorSize-1:0] neg_inf_conditions;

  // Single generate block for all conditions
  generate
    for (genvar i = 0; i < VectorSize; i = i + 1) begin : gen_conditions
      // Check if any operand is infinite
      assign operand_inf_conditions[i] = info_a[i].is_inf || info_b[i].is_inf;

      // Check if any operand is NaN
      assign operand_nan_conditions[i] = info_a[i].is_nan || info_b[i].is_nan;

      // Check for signalling NaN
      assign signalling_nan_conditions[i] = info_a[i].is_signalling || info_b[i].is_signalling;

      // Check for produced NaN (0 * inf or inf * 0)
      assign nan_conditions[i] = (info_a[i].is_inf && info_b[i].is_zero) ||
                                  (info_b[i].is_inf && info_a[i].is_zero);

      // Check for positive infinity (inf with same sign)
      assign pos_inf_conditions[i] = (info_a[i].is_inf && ~(operands_a[i].sign ^ operands_b[i].sign)) ||
                                      (info_b[i].is_inf && ~(operands_a[i].sign ^ operands_b[i].sign));

      // Check for negative infinity (inf with opposite sign)
      assign neg_inf_conditions[i] = (info_a[i].is_inf && (operands_a[i].sign ^ operands_b[i].sign)) ||
                                      (info_b[i].is_inf && (operands_a[i].sign ^ operands_b[i].sign));
    end
  endgenerate

  // Reduction for final results
  assign any_operand_inf = |operand_inf_conditions || info_d.is_inf;
  assign any_operand_nan = |operand_nan_conditions || info_c[0].is_nan || info_c[1].is_nan || info_d.is_nan;
  assign signalling_nan  = |signalling_nan_conditions || info_c[0].is_signalling || info_c[1].is_signalling || info_d.is_signalling;
  assign any_produced_nan = |nan_conditions;
  assign any_pos_inf = |pos_inf_conditions || (info_d.is_inf && ~operand_d.sign);
  assign any_neg_inf = |neg_inf_conditions || (info_d.is_inf && operand_d.sign);

  // ----------------------
  // Special case verdict (format independent -- the three branches of the
  // original per-format always_comb, transcribed one for one)
  // ----------------------
  //   if (any_produced_nan)      -> special, NV=1,             result = qNaN
  //   else if (any_operand_nan)  -> special, NV=signalling_nan, result = qNaN
  //   else if (any_operand_inf)  -> special,
  //        pos & neg  -> NV=1,  result = qNaN
  //        pos        ->        result = +inf
  //        neg        ->        result = -inf
  //   else                       -> not special (result/status unused)
  assign result_is_special_raw = any_produced_nan | any_operand_nan | any_operand_inf;
  assign special_nv            = any_produced_nan ? 1'b1
                               : any_operand_nan  ? signalling_nan
                               : any_operand_inf  ? (any_pos_inf & any_neg_inf)
                               :                    1'b0;
  assign special_is_inf        = ~any_produced_nan & ~any_operand_nan & any_operand_inf
                               & ~(any_pos_inf & any_neg_inf) & (any_pos_inf | any_neg_inf);
  assign special_inf_sign      = ~any_pos_inf;
endmodule

// Rebuilds the 32-bit special result and the status word from the 4-bit verdict
// carried through the pipeline.  This is the former per-format assembly block
// of fpnew_mxdotp_special_cases, verbatim, with `special_res` driven by the two
// encoded bits instead of by the condition chain -- including the NaN-boxing,
// the `'{default: fpnew_pkg::DONT_CARE}` for formats outside FpDstFmtConfig and
// the `dst_fmt` selects (which is what gates `result_is_special` to 0 when the
// destination format is not built).
module fpnew_mxdotp_special_assemble
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter fpnew_pkg::fmt_logic_t FpDstFmtConfig = MxdotpDstFpFmtConfig
) (
  input  logic                  result_is_special_raw,
  input  logic                  special_nv,
  input  logic                  special_is_inf,
  input  logic                  special_inf_sign,
  input  fpnew_pkg::fp_format_e dst_fmt,
  output logic [DST_WIDTH-1:0]  special_result,
  output fpnew_pkg::status_t    special_status,
  output logic                  result_is_special
);
  logic               [NUM_FORMATS-1:0][DST_WIDTH-1:0] fmt_special_result;
  fpnew_pkg::status_t [NUM_FORMATS-1:0]                fmt_special_status;
  logic               [NUM_FORMATS-1:0]                fmt_result_is_special;

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_special_results
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    localparam logic [EXP_BITS-1:0] QNAN_EXPONENT = '1;
    localparam logic [MAN_BITS-1:0] QNAN_MANTISSA = 2**(MAN_BITS-1);
    localparam logic [MAN_BITS-1:0] ZERO_MANTISSA = '0;

    if (FpDstFmtConfig[fmt]) begin : active_format
      always_comb begin : special_cases
        logic [FP_WIDTH-1:0] special_res;
        special_res                = special_is_inf
                                   ? {special_inf_sign, QNAN_EXPONENT, ZERO_MANTISSA}
                                   : {1'b0,             QNAN_EXPONENT, QNAN_MANTISSA};
        fmt_special_status[fmt]    = '0;
        fmt_special_status[fmt].NV = special_nv;
        fmt_result_is_special[fmt] = result_is_special_raw;
        // Initialize special result with ones (NaN-box)
        fmt_special_result[fmt]               = '1;
        fmt_special_result[fmt][FP_WIDTH-1:0] = special_res;
      end
    end else begin : inactive_format
      assign fmt_special_result[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_special_status[fmt] = '0;
      assign fmt_result_is_special[fmt] = 1'b0;
    end
  end

  assign result_is_special = fmt_result_is_special[dst_fmt];
  assign special_status    = fmt_special_status[dst_fmt];
  assign special_result    = fmt_special_result[dst_fmt];
endmodule

// Adds two signed 8-bit scale values to produce a 9-bit combined scale.
module fpnew_mxdotp_scale_adder
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1) // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
) (
  // Input signals
  input  logic signed [1:0][SCALE_WIDTH-1:0] operands_c,
  // The LZC-INDEPENDENT part of the final exponent, i.e. the original
  //   exponent_major = 127 - ANCHOR + scale + FIXED_SUM_WIDTH - 1
  // with the constant folded into THIS adder's already-constant term.  The
  // 9-bit `scale` never wraps (operands_c are 8-bit signed, so the
  // sum lies in [-256,254]), hence scale + 187 in [-69,441] is exact in
  // DST_EXP_WIDTH=10 bits and this is bit-identical to the original two-step
  // computation.  `scale` itself has no other consumer once
  // fpnew_mxdotp_accumulator_prep absorbs the same offset.
  output logic signed [DST_EXP_WIDTH-1:0] exponent_major
);
  // ------------------
  // Scale data path
  // ------------------
  localparam int EXP_MAJOR_OFFSET = 127 - int'(ANCHOR) + int'(FIXED_SUM_WIDTH) - 1;
  assign exponent_major = signed'(operands_c[0]) + signed'(operands_c[1]) + EXP_MAJOR_OFFSET;
endmodule

// Multiplies two vectors of mantissas (with implicit bit prepended) element-wise, applying sign logic.
// Produces signed products (2p+1 bits) based on XOR of input signs.
module fpnew_mxdotp_vector_multiplier
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type         SrcType         = logic,
  parameter int unsigned LocalVectorSize = 8,
  parameter int unsigned PrecisionBits   = 4
) (
  // Input signals
  input  SrcType [LocalVectorSize-1:0] operands_a,
  input  SrcType [LocalVectorSize-1:0] operands_b,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_b,
  output logic signed [LocalVectorSize-1:0][2*PrecisionBits :0] product_signed
);
  // ------------------
  // Product data path
  // ------------------
  logic [LocalVectorSize-1:0][  PrecisionBits-1:0] mantissa_a, mantissa_b;
  logic [LocalVectorSize-1:0][2*PrecisionBits-1:0] product;  // the p*p product is 2p-bit wide

  // Add implicit bits to mantissae
  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_mantissa
    assign mantissa_a[i] = {info_a[i].is_normal, operands_a[i].mantissa};
    assign mantissa_b[i] = {info_b[i].is_normal, operands_b[i].mantissa};
    assign product[i]    = mantissa_a[i] * mantissa_b[i];
    assign product_signed[i] = (operands_a[i].sign ^ operands_b[i].sign) ? -product[i] : product[i];
  end
endmodule

// Multiplies vectors of signed integers (INT8) or floating-point mantissas (FP8) with sign handling.
// For FP8: adds implicit bit and applies sign via negation. For INT8: uses full 8-bit signed values.
module fpnew_mxdotp_signed_vector_multiplier
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type         SrcType         = logic,
  parameter int unsigned LocalVectorSize = 8,
  parameter int unsigned PrecisionBits   = 8
) (
  // Input signals
  input  SrcType [LocalVectorSize-1:0] operands_a,
  input  SrcType [LocalVectorSize-1:0] operands_b,
  input  fpnew_pkg::fp_format_e  src_fmt,
  input  fpnew_pkg::int_format_e int_fmt,
  input  logic src_is_int,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_b,
  output logic signed [LocalVectorSize-1:0][2*PrecisionBits-1:0] product_signed
);
  // ------------------
  // Product data path
  // ------------------
  logic signed [LocalVectorSize-1:0][  PrecisionBits-1:0] mantissa_a, mantissa_b;
  // Extra partial-product row that carries the FP8 sign (see below)
  logic        [LocalVectorSize-1:0][  PrecisionBits-1:0] sign_row;

  // ----------------------------------------------------------------------
  // The FP8 sign no longer sits in FRONT of the multiplier array.
  //
  // The original code negated mantissa_a before multiplying, so the operand sign
  // had to traverse a 4-bit negate (complement + increment) and the format
  // mux before a single partial product could be formed.  For a magnitude
  // a in [0,15] the 8-bit one's complement is exactly -a-1 in two's
  // complement, hence
  //       (-a) * b  ==  (~a) * b + b
  // so the sign now costs ONE XOR on mantissa_a (a single gate, in
  // parallel with the format mux) plus ONE extra row in the compressor
  // tree the multiplier already builds.  Nothing downstream changes:
  // product_signed is bit-identical.
  // ----------------------------------------------------------------------
  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_mantissa_fp8
    logic sign_prod;
    assign sign_prod = operands_a[i].sign ^ operands_b[i].sign;
    always_comb begin
      if (src_is_int && int_fmt == fpnew_pkg::INT8) begin : int8
        // For INT8, we use the full 8-bit mantissa
        mantissa_a[i] = operands_a[i][7:0];
        mantissa_b[i] = operands_b[i][7:0];
        sign_row[i]   = '0;
      end else begin : fp8
        // Add implicit bits to mantissae and pad with zeros
        mantissa_a[i] = {4'b0, info_a[i].is_normal, operands_a[i].mantissa}
                        ^ {PrecisionBits{sign_prod}};
        mantissa_b[i] = {4'b0, info_b[i].is_normal, operands_b[i].mantissa};
        sign_row[i]   = sign_prod
                      ? {4'b0, info_b[i].is_normal, operands_b[i].mantissa}
                      : '0;
      end
    end
  end

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_mantissa
    assign product_signed[i] = signed'(mantissa_a[i]) * signed'(mantissa_b[i])
                             + signed'({{PrecisionBits{1'b0}}, sign_row[i]});
  end
endmodule

// Early half of the former fpnew_mxdotp_product_shifter: the per-lane product exponent.
// Depends only on the (classified) operands, never on the product, so it can sit
// in a different pipeline stage than the alignment shift below.
module fpnew_mxdotp_product_exponent
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type         SrcType          = logic,
  parameter int unsigned LocalVectorSize  = 8,
  parameter int unsigned ExpWidth         = 8,
  // Constant part of the alignment shift that the LATE half used to add to the
  // product exponent (SOP_SHIFT for FP8, 4 for FP6, 0 for FP4).  It is folded
  // into THIS adder, where it merges with the -2*bias constant of the same
  // four-term sum and therefore costs nothing, instead of sitting as a separate
  // carry-propagate stage in FRONT of the alignment shifter's select decode.
  parameter int          ShiftOffset      = 0,
  parameter int unsigned AmtWidth         = ExpWidth,
  // When set, the alignment shift amount is forced to ALL ONES in the INT8
  // case.  All ones is >= the late half's OutputWidth, so its variable shifter
  // returns zero there, which is what lets fpnew_mxdotp_product_align drop the
  // INT8/FP8 select from the low ANCHOR bits of its output (they are zero in
  // BOTH arms).  Pure constant forcing: the FP8/FP6/FP4 value is untouched.
  parameter bit          ForceOnInt8      = 1'b0
) (
  input  SrcType [LocalVectorSize-1:0] operands_a,
  input  SrcType [LocalVectorSize-1:0] operands_b,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_b,
  input  fpnew_pkg::fp_format_e src_fmt,
  input  fpnew_pkg::int_format_e int_fmt,
  input  logic src_is_int,
  output logic [LocalVectorSize-1:0][AmtWidth-1:0] shift_amount
);
  logic force_int8;
  assign force_int8 = ForceOnInt8 && src_is_int && (int_fmt == fpnew_pkg::INT8);
  // Calculate the non-biased exponent of the product (verbatim from the former
  // fpnew_mxdotp_product_shifter).
  logic signed [LocalVectorSize-1:0][ExpWidth-1:0] exponent_product;

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_exponent_adjustment
    assign exponent_product[i] = operands_a[i].exponent + info_a[i].is_subnormal
                                + operands_b[i].exponent + info_b[i].is_subnormal
                                - 2*signed'(bias_constant(src_fmt));
    // AmtWidth is chosen wide enough (ExpWidth+1 wherever ShiftOffset != 0) that
    // signed'(ShiftOffset) + signed'(exponent_product[i]) is representable, so
    // this is the same integer the original code handed to `<<`.  Shift amounts that
    // are negative there produced a >= 2**31 unsigned shift and hence an
    // all-zero result; here they produce a >= 2**(AmtWidth-1) one, which is
    // still wider than OutputWidth, hence the same all-zero result.
    assign shift_amount[i] = AmtWidth'(signed'(ShiftOffset) + signed'(exponent_product[i]))
                           | {AmtWidth{force_int8}};
  end
endmodule

// Late half of the former fpnew_mxdotp_product_shifter: the variable alignment shift.
// Body copied verbatim from that module; only the SHIFT AMOUNT now
// arrives as a port, with the constant offset already folded in upstream.
module fpnew_mxdotp_product_align
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned LocalVectorSize  = 8,
  parameter fpnew_pkg::fp_format_e SrcFmt = fpnew_pkg::FP8,
  parameter int unsigned ProductBits      = 4,
  parameter int unsigned AmtWidth         = 8,
  parameter int unsigned OutputWidth      = 70
) (
  input  logic [LocalVectorSize-1:0][ProductBits-1:0] product_signed,
  // The FULL alignment shift amount, constant offset already applied upstream.
  input  logic [LocalVectorSize-1:0][AmtWidth-1:0] shift_amount,
  input  fpnew_pkg::int_format_e int_fmt,
  input  logic src_is_int,
  output logic signed [LocalVectorSize-1:0][OutputWidth-1:0] shifted_product
);
  // The original branch select, hoisted out of the per-lane loop.  The INT8
  // arm `signed'(product_signed[i]) << ANCHOR` has its low ANCHOR bits ZERO,
  // and the FP8 arm is zero for the WHOLE word whenever is_int8 because
  // fpnew_mxdotp_product_exponent (ForceOnInt8=1) drives shift_amount to all
  // ones there, which is >= OutputWidth.  The two arms are therefore disjoint
  // and only the top OutputWidth-ANCHOR bits still need a select.
  logic is_int8;
  assign is_int8 = src_is_int && (int_fmt == fpnew_pkg::INT8);

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_align
    if (SrcFmt == fpnew_pkg::FP8) begin : gen_align_fp8
      localparam int unsigned HI_BITS = OutputWidth - ANCHOR;
      logic signed [OutputWidth-1:0] barrel;
      logic signed [HI_BITS-1:0]     int8_hi;
      // Only the 9 significant product bits enter the variable shifter; the
      // sign extension is re-created by the signed widening (as before).
      assign barrel  = signed'(product_signed[i][2*PRECISION_BITS:0]) << shift_amount[i];
      // Disjoint arms -> the select is an OR, and the gating collapses onto the
      // ProductBits-wide product instead of the OutputWidth-wide shifted word.
      logic [ProductBits-1:0] p_gated;
      assign p_gated = product_signed[i] & {ProductBits{is_int8}};
      assign int8_hi = signed'(p_gated);
      assign shifted_product[i] = barrel | {int8_hi, {ANCHOR{1'b0}}};
    end else begin : gen_align_other
      assign shifted_product[i] = signed'(product_signed[i]) << shift_amount[i];
    end
  end
endmodule

// Shifts accumulator right to align with sum-of-products based on scale and accumulator exponent.
// Computes shift amount, handles sticky bits, and detects if accumulator dominates the result.
// Early half of fpnew_mxdotp_accumulator_shift (STAGE 1): everything that
// depends only on the classified accumulator operand, the scale and the
// destination format -- i.e. the 24-bit conditional negate that builds
// signed_mantissa_d and the four-term shift-amount sum.  Both sat in FRONT of
// the 95-bit accumulator barrel shifter in stage 2; the accumulator lane of
// stage 1 was empty (only the 9-bit scale adder), so they move into slack.
// The INP-MID bank stops carrying info_d (8 b, this was its only consumer) and
// carries the 25-bit signed mantissa and the 10-bit shift amount instead.
module fpnew_mxdotp_accumulator_prep
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1) // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
) (
  input  logic signed [DST_EXP_WIDTH-1:0] exponent_major,
  input  fp_dst_t operand_d,
  input  fpnew_pkg::fp_info_t info_d,
  input  fpnew_pkg::fp_format_e dst_fmt,
  output logic signed [9:0] accumulator_shift_amount,
  output logic signed [DST_PRECISION_BITS :0] signed_mantissa_d
);
  logic signed [DST_EXP_WIDTH-1:0] exponent_d;
  logic [DST_PRECISION_BITS-1:0] mantissa_d;

  // Zero-extend exponents into signed container - implicit width extension
  assign exponent_d = {1'b0, operand_d.exponent};
  assign mantissa_d = {info_d.is_normal, operand_d.mantissa};
  assign signed_mantissa_d = operand_d.sign ? -mantissa_d : mantissa_d;

  // Calculate the shift amount for the accumulator, range=[-370,394-9b -> signed 10b]
  // exponent_major == scale + EXP_MAJOR_OFFSET exactly (no wrap, see
  // fpnew_mxdotp_scale_adder), so -scale == EXP_MAJOR_OFFSET - exponent_major
  // and the whole expression is the original integer, hence the original value
  // after the truncation to 10 bits.
  localparam int EXP_MAJOR_OFFSET = 127 - int'(ANCHOR) + int'(FIXED_SUM_WIDTH) - 1;
  assign accumulator_shift_amount = signed'(int'(ANCHOR) - int'(SUPER_DST_MAN_BITS)
                                            + EXP_MAJOR_OFFSET)
                                     - signed'(exponent_major)
                                     + signed'(exponent_d + info_d.is_subnormal)
                                     - signed'(bias_constant(dst_fmt));
endmodule

module fpnew_mxdotp_accumulator_shift
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int signed MAX_ACC_SHIFT_AMOUNT = FIXED_SUM_WIDTH - DST_PRECISION_BITS - 1
) (
  // Input signals (pre-computed in stage 1 by fpnew_mxdotp_accumulator_prep)
  input  logic signed [9:0] accumulator_shift_amount,
  input  logic signed [DST_PRECISION_BITS :0] signed_mantissa_d,
  output logic result_is_accumulator_uncond,
  output logic result_is_accumulator_if_sop_zero,
  output logic signed [DST_PRECISION_BITS-1:0] accumulator_remaining,
  output logic accumulator_sticky,
  output logic signed [FIXED_SUM_WIDTH-1:0] accumulator_shifted
);

  // -----------------------------
  // Accumulator shift data path
  // -----------------------------
  // {signed_mantissa_d, 24'b0} >>> accumulator_right_shift_amount_w, 49 bits.
  // The shift amount is taken from a wire (not from the always_comb output) so
  // that the funnel stays outside the procedural block.
  logic signed [9:0] accumulator_right_shift_amount_w;
  logic signed [2*DST_PRECISION_BITS:0] accumulator_funnel;
  assign accumulator_right_shift_amount_w = -accumulator_shift_amount;
  assign accumulator_funnel = signed'({signed_mantissa_d, {DST_PRECISION_BITS{1'b0}}})
                              >>> accumulator_right_shift_amount_w;

  always_comb begin : accumulator_shift
    result_is_accumulator_uncond = 1'b0;
    result_is_accumulator_if_sop_zero = 1'b0;
    accumulator_remaining = '0;
    accumulator_sticky = 1'b0;
    if (accumulator_shift_amount > MAX_ACC_SHIFT_AMOUNT) begin
      // SoP is too small to change the accumulator, result is the accumulator
      accumulator_shifted = '0;
      result_is_accumulator_uncond = 1'b1;
    end else if (accumulator_shift_amount >= 0) begin
      accumulator_shifted = signed'(signed_mantissa_d) <<< accumulator_shift_amount;
    end else begin
      // ONE 49-bit arithmetic right shift serves both outputs: its top 25 bits
      // are exactly signed'(signed_mantissa_d) >>> r evaluated in 25-bit
      // arithmetic, whose 95-bit sign extension is the original wide shift,
      // and its low 24 bits are accumulator_remaining (see below).
      accumulator_shifted = FIXED_SUM_WIDTH'(signed'(
          accumulator_funnel[2*DST_PRECISION_BITS:DST_PRECISION_BITS]));
      // The two branches below differ only in the DIRECTION of a shift by
      // |r - DST_PRECISION_BITS|, so they are one arithmetic right shift of
      // the mantissa pre-placed at bit DST_PRECISION_BITS:
      //   remaining = ({m, 24'b0} >>> r)[23:0]
      // r <= 24 : bits [23:0] of the shifted word are m's bits from index
      //           24-r downwards, i.e. exactly m << (24-r) truncated.
      // r >  24 : the same slice is m >>> (r-24), sign-extended from the
      //           49-bit container's MSB, which IS m's sign bit.
      // One shifter instead of two; identical bits in both branches.
      accumulator_remaining = accumulator_funnel[DST_PRECISION_BITS-1:0];
      if (accumulator_right_shift_amount_w > DST_PRECISION_BITS) begin
        result_is_accumulator_if_sop_zero = 1'b1;
        accumulator_sticky = |(signed'(signed_mantissa_d) & ((1 << (accumulator_right_shift_amount_w - DST_PRECISION_BITS)) - 1));
      end else begin
        accumulator_sticky = 1'b0;
      end
    end
  end
endmodule


// Fused sum-of-products + accumulator adder.
// Sums the eight aligned FP8/INT8 products, the (constant-shifted) FP6 and FP4
// lane sums and the aligned accumulator in ONE arithmetic expression, so that
// synthesis builds a single carry-save compressor tree with a single final CPA
// instead of the three back-to-back carry-propagate stages (per-lane adder
// tree -> format adder -> accumulator adder) of the original design.
// `sum_product_is_zero` reproduces the original `sum_product == 0` test without
// materialising sum_product: because the fused sum is computed modulo 2^95 and
// sum_product is exactly 95 bits wide,
//   sum_product == 0  <=>  (sum_product + accumulator_shifted) == accumulator_shifted.
module fpnew_mxdotp_fused_sop_accumulator
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned LocalVectorSize = 8,
  parameter int unsigned Fp6VectorSize   = 3,
  parameter int unsigned Fp4VectorSize   = 5,
  parameter int unsigned Fp6ProdWidth    = FP6_PROD_SHIFT_WIDTH,
  parameter int unsigned Fp4ProdWidth    = FP4_PROD_SHIFT_WIDTH,
  parameter int unsigned Fp6SumWidth     = FP6_PROD_SHIFT_WIDTH,
  parameter int unsigned Fp4SumWidth     = FP4_PROD_SHIFT_WIDTH,
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS
) (
  input  logic signed [LocalVectorSize-1:0][PROD_SHIFT_WIDTH-1:0] shifted_product,
  input  logic signed [Fp6VectorSize-1:0][Fp6ProdWidth-1:0]    fp6_shifted_product,
  input  logic signed [Fp4VectorSize-1:0][Fp4ProdWidth-1:0]    fp4_shifted_product,
  input  logic signed [FIXED_SUM_WIDTH-1:0]    accumulator_shifted,
  input  logic signed [DST_PRECISION_BITS-1:0] accumulator_remaining,
  output logic                                 sum_product_is_zero,
  output logic signed [LZC_SUM_WIDTH-1:0]      sum_product_accumulator_extended
);
  logic signed [SoPFixedWidth-1:0] sum_product_fp8;
  logic signed [Fp6SumWidth-1:0]     sum_product_fp6;
  logic signed [Fp4SumWidth-1:0]     sum_product_fp4;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_fp4_shifted;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_fp6_shifted;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_accumulator;

  // One arithmetic expression tree, one module: the FP8/INT8 lane sum, the FP6
  // and FP4 lane sums, the format merge and the accumulator add are now a
  // single datapath block, so synthesis compresses all SIXTEEN aligned terms in
  // carry-save form and pays for exactly ONE carry-propagate adder at the end.
  // Previously the FP6 (3 terms, 21 bit) and FP4 (5 terms, 9 bit) lane sums
  // were separate carry-propagate adders sitting IN SERIES in front of this
  // one.
  //
  // The association is unchanged (per-lane `+=` chains, then the format
  // merge, then the accumulator), so no re-association is done in RTL --
  // that is left to synthesis.  Each lane sum is exact
  // at its own width (8 x 67b into 70b, 3 x 21b into 23b, 5 x 9b into 12b all
  // fit without wrapping), so hoisting the lane sums into the same expression
  // preserves the value bit for bit.
  always_comb begin : sum_products_fp8
    sum_product_fp8 = '0;
    for (int i = 0; i < LocalVectorSize; i++) begin
      sum_product_fp8 += signed'(shifted_product[i]);
    end
  end
  always_comb begin : sum_products_fp6
    sum_product_fp6 = '0;
    for (int i = 0; i < Fp6VectorSize; i++) begin
      sum_product_fp6 += signed'(fp6_shifted_product[i]);
    end
  end
  always_comb begin : sum_products_fp4
    sum_product_fp4 = '0;
    for (int i = 0; i < Fp4VectorSize; i++) begin
      sum_product_fp4 += signed'(fp4_shifted_product[i]);
    end
  end
  assign sum_product_fp4_shifted = signed'(sum_product_fp4) << (SOP_SHIFT+2*(SUPER_MAN_BITS-FP4_MAN_BITS));
  assign sum_product_fp6_shifted = signed'(sum_product_fp6) << (SOP_SHIFT-4+2*(SUPER_MAN_BITS-FP6_MAN_BITS));
  assign sum_product             = sum_product_fp8 + sum_product_fp4_shifted + sum_product_fp6_shifted;
  assign sum_product_accumulator = sum_product + accumulator_shifted;

  // 70-bit test, not 95.  sum_product is the sum of a 70-bit-exact FP8 lane
  // sum (|.| <= 2^69) and the FP6/FP4 lane terms (|.| <= 2^46 + 2^43), so its
  // exact value has magnitude < 2^70 and is carried in the 95-bit container
  // WITHOUT wrapping.  Hence sum_product == 0  <=>  sum_product[69:0] == 0,
  // and because sum_product_accumulator = sum_product + accumulator_shifted
  // (mod 2^95), that is exactly the equality of the low SoPFixedWidth bits.
  // Twenty-five comparator bits and one level of the AND tree disappear.
  assign sum_product_is_zero              = (sum_product_accumulator[SoPFixedWidth-1:0]
                                             == accumulator_shifted[SoPFixedWidth-1:0]);
  assign sum_product_accumulator_extended = {sum_product_accumulator, accumulator_remaining};
endmodule

// Converts results to sign-magnitude format using two's complement.
module fpnew_mxdotp_twos_compl
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS
) (
  // Input signals
  input  logic [LZC_SUM_WIDTH-1:0] sum_product_accumulator_extended,
  // Output signals
  output logic final_sign,
  // ONE'S complement of the sum when negative (the +1 is applied in
  // fpnew_mxdotp_norm_finalize, off the LZC path)
  output logic [LZC_SUM_WIDTH-1:0] sum_magnitude
);
  // If sum is negative, complement to feed into leading zero counter
  assign final_sign = sum_product_accumulator_extended[LZC_SUM_WIDTH-1];

  // The original code guarded the one's-complement (round-to-odd) case with
  //   accumulator right-shifted by more than DST_PRECISION_BITS
  //   && signed_mantissa_d != 0 && accumulator_sticky
  // but `accumulator_sticky` already implies the other conjuncts:
  // accumulator_shift only ever raises it inside the branch where the
  // accumulator is right-shifted by more than DST_PRECISION_BITS, and it is
  // an OR-reduction of a mask of signed_mantissa_d, so it can only be 1 when
  // signed_mantissa_d != 0.
  // The predicate therefore collapses to accumulator_sticky, which turns the
  // conditional-complement's carry-in into a plain signal and drops a 10-bit
  // comparator plus a 25-bit zero-test from this module.
  // ------------------------------------------------------------------
  // The +1 of the two's complement has MOVED DOWNSTREAM (see
  // fpnew_mxdotp_norm_finalize).  This module now emits only the ONE'S
  // complement `sum_magnitude_ones = x ^ {119{sign}}`, which is one XOR
  // deep instead of a 119-bit carry-propagate incrementer.  The leading
  // zero counter runs directly on it; norm_finalize both (a) re-applies
  // the +1 for the window data, where there is slack, and (b) corrects
  // the leading-zero count, which differs from the true one by exactly
  // one only when ~x is 0^k 1^m (m>=1), i.e. when the magnitude is a
  // power of two -- a condition detected in parallel with the LZC.
  // ------------------------------------------------------------------
  assign sum_magnitude = sum_product_accumulator_extended
                       ^ {LZC_SUM_WIDTH{final_sign}};
endmodule

// Normalisation window extractor with fused sticky collection.
//
// The original design left-shifted the full LZC_SUM_WIDTH (=119) bit magnitude by
// `norm_shamt` and then used only
//     final_mantissa  = sum_shifted[118:95]      (the top DST_PRECISION_BITS)
//     sticky_bits_or  = |sum_shifted[94:0]
// i.e. it paid for a full 119-bit barrel shifter *and* a 95-bit OR tree.
//
// Algebraically, for X = sum_magnitude:
//     final_mantissa = X[118-shamt : 95-shamt]   (bits below index 0 read as 0)
//     sticky_bits_or = |X[94-shamt : 0]
// so only a 24-bit *window* of X has to be routed to the output.  This module
// therefore shifts coarse-to-fine and NARROWS the surviving word at every
// stage, keeping only the bits that can still reach the 24-bit window:
//     119 -> 87 -> 55 -> 39 -> 31 -> 27 -> 25 -> 24
// which is 288 2:1 muxes instead of 7*119 = 833.
//
// The bits a stage drops off the bottom of the window are exactly the bits that
// have fallen below index 95 of the shifted result, i.e. exactly the bits the
// original 95-bit OR tree consumed.  So the sticky OR is collected *inside* the
// narrowing (one small OR per stage, total 32+32+16+8+4+2+1 = 95 terms - the
// same 95 bits, but ORed at seven shallow points instead of one deep tree).
// In the d=2^k branch of a stage nothing is dropped, because the bits leaving
// the bottom of the window there are the zeros shifted in from below.
//
// Invariant maintained across the pipeline of stages: `v` (W bits) equals
// (X << p)[118 : 119-W], and `sticky` is the OR of all bits of (X << p) below
// index 119-W.  Stage with shift d maps
//     v' = v[W-1-d : W-W'-d]      (missing low indices are zeros)
//     sticky' = sticky | (d ? 1'b0 : |v[W-W'-1 : 0])
// Shift amounts >= LZC_SUM_WIDTH shift everything out in the original code (the shift
// is evaluated in a 119-bit container), so they are detected up front and force
// window and sticky to zero, which is what lets the seven low shift bits drive
// the stages.
module fpnew_mxdotp_norm_window
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS,
  // Shift amount width: $clog2(DST_BIAS - ANCHOR + (scale_a+scale_b) + FIXED_SUM_WIDTH - 1)
  localparam int unsigned SHIFT_AMOUNT_WIDTH = $clog2(fpnew_pkg::bias(fpnew_pkg::FP32) - ANCHOR + 2**(SCALE_WIDTH) - 1 + FIXED_SUM_WIDTH - 1)
) (
  input  logic [LZC_SUM_WIDTH-1:0]       sum_magnitude,
  input  logic [SHIFT_AMOUNT_WIDTH-1:0]  norm_shamt,
  output logic [DST_PRECISION_BITS-1:0]  final_mantissa,
  output logic                           sticky_bits_or
);
  // Same narrowing invariant as before -- "v (W bits) == (X << p)[118 :
  // 119-W], missing low indices zero" -- but the FOUR fine stages are replaced
  // by ONE 16-way select, and the sticky those stages produced is kept by
  // carrying only the handful of bits its ORs actually read.
  //
  //   coarse : 119 -> 87 -> 55 -> 39   (binary, shamt[6:4], unchanged)
  //   fine   : v3[38-r : 15-r]         (one select on r = shamt[3:0])
  //
  // The original stages 4..7 are four multiplexer levels on the LATEST signal
  // in the design (the shift amount comes straight out of the leading-zero
  // count); a single 16-way select is one decoder plus one AND-OR level.
  localparam int unsigned W0 = LZC_SUM_WIDTH;                     // 119
  localparam int unsigned W1 = DST_PRECISION_BITS + 63;           //  87
  localparam int unsigned W2 = DST_PRECISION_BITS + 31;           //  55
  localparam int unsigned W3 = DST_PRECISION_BITS + 15;           //  39

  if (W0 <= 64 || W0 > 128) begin
    $fatal(1, "fpnew_mxdotp_norm_window: LZC_SUM_WIDTH=%0d outside the supported (64,128] range", W0);
  end

  // Only shift amounts >= 2**7 need explicit forcing: for W0 <= p <= 127 the
  // window indices (W0-1-p .. W0-24-p) are already all negative and the sticky
  // range X[W0-25-p:0] is already empty, so the chain returns the same zero
  // by itself (requires 64 < W0 <= 128, which holds for VectorSize <= 4096).
  // Catching only p >= 128 makes this one OR of two bits and lets
  // the forcing sit at the FIRST stage instead of on the outputs at the end.
  logic shift_out_all;
  assign shift_out_all = (| norm_shamt[SHIFT_AMOUNT_WIDTH-1:7]);

  logic [W1-1:0] v1; logic [W2-1:0] v2; logic [W3-1:0] v3;
  logic s1, s2, s3, s4, s5, s6, s7;

  // Stage 1 (shift by 64): the top W1 bits of (X << 64).  Written as a
  // constant shift so the window stays correct for every LZC_SUM_WIDTH
  // (119 at VectorSize=8, 121 at VectorSize=32, ...); a hand-built
  // {X[W0-65:0], 32'b0} is only right for W0 == 119.
  logic [W0-1:0] sum_magnitude_shl64;
  assign sum_magnitude_shl64 = sum_magnitude << 64;

  assign v1 = shift_out_all ? '0
                            : (norm_shamt[6] ? sum_magnitude_shl64[W0-1 -: W1]
                                             : sum_magnitude[W0-1 -: W1]);
  assign s1 = (shift_out_all | norm_shamt[6]) ? 1'b0 : |sum_magnitude[W0-W1-1:0];
  assign v2 = norm_shamt[5] ? v1[W2-1:0] : v1[W1-1 -: W2];
  assign s2 = norm_shamt[5] ? 1'b0      : |v1[W1-W2-1:0];
  assign v3 = norm_shamt[4] ? v2[W3-1:0] : v2[W2-1 -: W3];
  assign s3 = norm_shamt[4] ? 1'b0      : |v2[W2-W3-1:0];

  // Fine extraction: final_mantissa == (X << p3+r)[118:95] == v3[38-r : 15-r]
  always_comb begin : gen_fine
    unique case (norm_shamt[3:0])
      4'd0 : final_mantissa = v3[38:15];
      4'd1 : final_mantissa = v3[37:14];
      4'd2 : final_mantissa = v3[36:13];
      4'd3 : final_mantissa = v3[35:12];
      4'd4 : final_mantissa = v3[34:11];
      4'd5 : final_mantissa = v3[33:10];
      4'd6 : final_mantissa = v3[32:9];
      4'd7 : final_mantissa = v3[31:8];
      4'd8 : final_mantissa = v3[30:7];
      4'd9 : final_mantissa = v3[29:6];
      4'd10: final_mantissa = v3[28:5];
      4'd11: final_mantissa = v3[27:4];
      4'd12: final_mantissa = v3[26:3];
      4'd13: final_mantissa = v3[25:2];
      4'd14: final_mantissa = v3[24:1];
      4'd15: final_mantissa = v3[23:0];
    endcase
  end

  // Sticky tail: the fine stages only ever contribute the OR of the bits they
  // drop, so the 31/27/25/24-bit windows of the original stages 4..7 collapse
  // to the 7/3/1 bits those ORs actually read.  s4..s7 are bit-for-bit the
  // original values, hence so is `sticky_bits_or`.
  logic [6:0] t4;   // == v4[6:0]
  logic [2:0] t5;   // == v5[2:0]
  logic       t6;   // == v6[0]
  assign t4 = norm_shamt[3] ? v3[6:0] : v3[14:8];
  assign t5 = norm_shamt[2] ? t4[2:0] : t4[6:4];
  assign t6 = norm_shamt[1] ? t5[0]   : t5[2];
  assign s4 = norm_shamt[3] ? 1'b0 : |v3[7:0];
  assign s5 = norm_shamt[2] ? 1'b0 : |t4[3:0];
  assign s6 = norm_shamt[1] ? 1'b0 : |t5[1:0];
  assign s7 = norm_shamt[0] ? 1'b0 : t6;

  assign sticky_bits_or = s1 | s2 | s3 | s4 | s5 | s6 | s7;
endmodule

// Computes normalization shift amount and biased exponent from sign-magnitude sum via leading-zero
// count. Handles subnormals (normalized_exponent = 0) and zero (lzc_zeroes path).

// Leading-zero counter for the normalisation path (drop-in for common_cells
// `lzc #(.WIDTH(119), .MODE(1))`, bit-identical on EVERY input including the
// all-zero one, where both return cnt_o = 0).
//
// common_cells builds a BINARY reduction tree in which the index has to travel
// through $clog2(WIDTH)=7 multiplexers whose selects are themselves OR trees;
// which is deep, and it is the largest single block of the pre-normalisation
// stage.  The tree below is RADIX-4: 128 padded
// bits -> 32 -> 8 -> 2 -> 1, so the index crosses three 4:1 selects and one
// 2:1 select while the `any` OR tree that drives those selects is only three
// OR4 levels deep.  Each node emits the position of its FIRST set input, or
// zero when it has none, which is what makes the all-zero result 0 without a
// masking gate on the output.
module fpnew_mxdotp_lzc119 #(
  parameter int unsigned WIDTH     = 119,
  parameter int unsigned CNT_WIDTH = 7
) (
  input  logic [WIDTH-1:0]     in_i,
  output logic [CNT_WIDTH-1:0] cnt_o,
  output logic                 empty_o
);
  localparam int unsigned PAD = 2**CNT_WIDTH;   // 128

  // Flip so index 0 is the MSB of in_i (leading-zero mode), zero-pad to 4**k.
  logic [PAD-1:0] f;
  for (genvar i = 0; i < PAD; i++) begin : gen_flip
    if (i < WIDTH) begin : g_real
      assign f[i] = in_i[WIDTH-1-i];
    end else begin : g_pad
      assign f[i] = 1'b0;
    end
  end

  // ---- level A: PAD/4 groups of four raw bits --------------------------
  logic [PAD/4-1:0]      any_a;
  logic [PAD/4-1:0][1:0] code_a;
  for (genvar j = 0; j < PAD/4; j++) begin : gen_a
    assign any_a[j]     = f[4*j] | f[4*j+1] | f[4*j+2] | f[4*j+3];
    assign code_a[j][1] = ~f[4*j] & ~f[4*j+1] & (f[4*j+2] | f[4*j+3]);
    assign code_a[j][0] = (~f[4*j] & f[4*j+1])
                        | (~f[4*j] & ~f[4*j+1] & ~f[4*j+2] & f[4*j+3]);
  end

  // ---- level B: PAD/16 groups of four A-nodes --------------------------
  logic [PAD/16-1:0]      any_b;
  logic [PAD/16-1:0][3:0] code_b;
  for (genvar j = 0; j < PAD/16; j++) begin : gen_b
    logic [1:0] sel;
    logic [1:0] pick;
    assign any_b[j] = any_a[4*j] | any_a[4*j+1] | any_a[4*j+2] | any_a[4*j+3];
    assign sel[1]   = ~any_a[4*j] & ~any_a[4*j+1] & (any_a[4*j+2] | any_a[4*j+3]);
    assign sel[0]   = (~any_a[4*j] & any_a[4*j+1])
                    | (~any_a[4*j] & ~any_a[4*j+1] & ~any_a[4*j+2] & any_a[4*j+3]);
    assign pick     = (sel == 2'd0) ? code_a[4*j+0]
                    : (sel == 2'd1) ? code_a[4*j+1]
                    : (sel == 2'd2) ? code_a[4*j+2]
                                    : code_a[4*j+3];
    assign code_b[j] = {sel, pick};
  end

  // ---- level C: PAD/64 groups of four B-nodes --------------------------
  logic [PAD/64-1:0]      any_c;
  logic [PAD/64-1:0][5:0] code_c;
  for (genvar j = 0; j < PAD/64; j++) begin : gen_c
    logic [1:0] sel;
    logic [3:0] pick;
    assign any_c[j] = any_b[4*j] | any_b[4*j+1] | any_b[4*j+2] | any_b[4*j+3];
    assign sel[1]   = ~any_b[4*j] & ~any_b[4*j+1] & (any_b[4*j+2] | any_b[4*j+3]);
    assign sel[0]   = (~any_b[4*j] & any_b[4*j+1])
                    | (~any_b[4*j] & ~any_b[4*j+1] & ~any_b[4*j+2] & any_b[4*j+3]);
    assign pick     = (sel == 2'd0) ? code_b[4*j+0]
                    : (sel == 2'd1) ? code_b[4*j+1]
                    : (sel == 2'd2) ? code_b[4*j+2]
                                    : code_b[4*j+3];
    assign code_c[j] = {sel, pick};
  end

  // ---- level D: the two remaining C-nodes ------------------------------
  logic sel_d;
  assign sel_d   = ~any_c[0] & any_c[1];
  assign empty_o = ~(any_c[0] | any_c[1]);
  assign cnt_o   = {sel_d, (sel_d ? code_c[1] : code_c[0])};
endmodule

module fpnew_mxdotp_norm_lzc
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS,
  localparam int unsigned LZC_RESULT_WIDTH = $clog2(LZC_SUM_WIDTH)
) (
  // ONE'S complement magnitude (the +1 lives in norm_finalize)
  input  logic [LZC_SUM_WIDTH-1:0] sum_magnitude_ones,
  // 1 when the true magnitude is sum_magnitude_ones + 1
  input  logic                     mag_inc,
  output logic signed [LZC_RESULT_WIDTH:0] leading_zero_count_sgn,
  output logic lzc_zeroes
);
  logic [LZC_RESULT_WIDTH-1:0] leading_zero_count;
  logic [LZC_SUM_WIDTH-1:0]    lzc_in;

  // The counted word is the one's complement with the pending +1 OR'ed into
  // bit 0.  Setting bit 0 cannot move the leading one of a non-zero word, so
  // for every non-zero `sum_magnitude_ones` this is the plain one's-complement
  // count.  It exists for the single case sum_magnitude_ones == 0 && mag_inc:
  // the true magnitude is then 1, and the leading-zero counter reports 0
  // (not 119) for an all-zero input, which would otherwise be used verbatim.
  // With the OR the counter sees 1 and returns 118, the true count.
  // It also makes `empty_o` exactly "true magnitude == 0": lzc_in == 0 iff
  // sum_magnitude_ones == 0 and mag_inc == 0 (ones == '1 with mag_inc = 1
  // would need x == 0, which forces final_sign = 0 and hence mag_inc = 0).
  assign lzc_in = sum_magnitude_ones | {{(LZC_SUM_WIDTH-1){1'b0}}, mag_inc};

  fpnew_mxdotp_lzc119 #(
    .WIDTH     ( LZC_SUM_WIDTH    ),
    .CNT_WIDTH ( LZC_RESULT_WIDTH ) // radix-4 drop-in, see above
  ) i_lzc (
    .in_i    ( lzc_in             ),
    .cnt_o   ( leading_zero_count ),
    .empty_o ( lzc_zeroes         )
  );

  assign leading_zero_count_sgn = signed'({1'b0, leading_zero_count});
endmodule

// Computes norm_shamt and normalized_exponent from LZC outputs and scale, then shifts
// the sign-magnitude sum, extracts mantissa and sticky bits.
// accumulator_sticky is OR'd into sticky_after_norm.
module fpnew_mxdotp_norm_finalize
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS,
  localparam int unsigned LZC_RESULT_WIDTH = $clog2(LZC_SUM_WIDTH),
  // Shift amount width: $clog2(DST_BIAS - ANCHOR + (scale_a+scale_b) + FIXED_SUM_WIDTH - 1)
  localparam int unsigned SHIFT_AMOUNT_WIDTH = $clog2(fpnew_pkg::bias(fpnew_pkg::FP32) - ANCHOR + 2**(SCALE_WIDTH) - 1 + FIXED_SUM_WIDTH - 1)
) (
  // ONE'S complement magnitude straight out of fpnew_mxdotp_twos_compl
  input  logic [LZC_SUM_WIDTH-1:0]          sum_magnitude_ones,
  // RAW count/empty of sum_magnitude_ones (corrected below)
  input  logic signed [LZC_RESULT_WIDTH:0]  leading_zero_count_sgn,
  input  logic                              lzc_zeroes,
  // The LZC-independent part of the exponent, already assembled in stage 1
  // (fpnew_mxdotp_scale_adder) and carried by the banks in place of `scale`.
  input  logic signed [DST_EXP_WIDTH-1:0]   exponent_major,
  input  logic                              final_sign,
  input  logic                              accumulator_sticky,
  // Re-materialised true magnitude, so that every consumer of the original
  // `sum_magnitude` still sees the original value (the rounder port).
  output logic [LZC_SUM_WIDTH-1:0]          sum_magnitude_o,
  output logic [DST_PRECISION_BITS-1:0]     final_mantissa,
  output logic signed [DST_EXP_WIDTH-1:0]   final_exponent,
  output logic                              sticky_after_norm
);
  logic signed [DST_EXP_WIDTH-1:0]      final_tentative_exponent;
  logic                                 tentative_exponent_positive;
  logic        [SHIFT_AMOUNT_WIDTH-1:0] norm_shamt;
  logic signed [DST_EXP_WIDTH-1:0]      normalized_exponent;

  logic                                        sticky_bits_or;

  // ----------------------------------------------------------------------
  // Re-apply the +1 of the two's complement, and correct the LZC for it.
  //
  // twos_compl now hands over  y = x ^ {119{final_sign}}  (one's complement
  // when negative).  The true magnitude is  m = y + mag_inc  with
  //     mag_inc = final_sign & !accumulator_sticky
  // (the original code added `!accumulator_sticky` only in the negative branch).
  //
  // Leading zeros:  adding one to y moves the leading one up by exactly one
  // position iff every bit below y's leading one is already 1, i.e. iff
  // y = 0^k 1^m with m >= 1; then lzc(y+1) = lzc(y) - 1.  Otherwise the
  // count is unchanged.  `y = 0^k 1^m, m>=1` is exactly "y[0] set and y
  // contains no 0-followed-by-1 pattern", a flat AND/OR reduction of y that
  // runs in PARALLEL with the LZC tree instead of in front of it.
  //   * m = 0 (y == 0, true magnitude 1) is excluded here by the y[0] term
  //     and is instead handled in fpnew_mxdotp_norm_lzc, which ORs mag_inc
  //     into bit 0 of the counted word so the cell sees 1 and returns the
  //     true count 118 (its all-zero output is 0, not 119).
  //   * y[0] = 0 with y != 0 also needs no correction: the carry stops at
  //     bit 0, and the OR in norm_lzc does not move a leading one either.
  //   * y[118] = 0 whenever final_sign = 1, so lzc(y) >= 1 and the
  //     decrement can never underflow.
  // `lzc_zeroes` needs no correction: norm_lzc's counted word is zero
  // exactly when the true magnitude is zero.
  // ----------------------------------------------------------------------
  logic                             mag_inc;
  logic                             lzc_is_run;
  logic                             lzc_dec;
  logic [LZC_SUM_WIDTH-2:0]         run_break;
  logic [LZC_SUM_WIDTH-1:0]         sum_magnitude;
  logic signed [DST_EXP_WIDTH-1:0]  exponent_major_corr;

  assign mag_inc       = final_sign & ~accumulator_sticky;
  assign sum_magnitude = sum_magnitude_ones
                       + {{(LZC_SUM_WIDTH-1){1'b0}}, mag_inc};

  for (genvar i = 0; i < LZC_SUM_WIDTH-1; i++) begin : gen_run_break
    assign run_break[i] = ~sum_magnitude_ones[i] & sum_magnitude_ones[i+1];
  end
  assign lzc_is_run     = sum_magnitude_ones[0] & ~(|run_break);
  assign lzc_dec        = mag_inc & lzc_is_run;

  // Calculate the biased exponent (excess-127 form)
  // The exponent-major is -scaled_anchor
  // exponent = 127 - scaled_anchor + (94-count-1) + increment_exponent [-195, 315 9b -> 10b signed]
  // `exponent_major` is the whole LZC-independent part: it only depends on the
  // scale, so it is now built by the stage-1 scale adder and arrives as a port.
  // true_lzc = leading_zero_count_sgn - lzc_dec, so every use of true_lzc is
  // rewritten to move the correction onto the EARLY operand exponent_major.
  assign exponent_major_corr      = exponent_major + signed'({1'b0, lzc_dec});
  assign final_tentative_exponent = exponent_major_corr - leading_zero_count_sgn;

  // final_tentative_exponent = exponent_major - lzc never wraps the 10-bit
  // signed container (exponent_major in [-69,442], lzc in [0,118]), so the
  // sign test is a plain magnitude comparison of an early operand against the
  // LZC - a comparator, instead of a full subtract followed by a sign/zero test.
  assign tentative_exponent_positive = signed'(exponent_major_corr) > signed'(leading_zero_count_sgn);

  // Normalization shift amount based on exponents and LZC (unsigned as only left shifts)
  always_comb begin : norm_shift_amount
    if (tentative_exponent_positive && !lzc_zeroes) begin
      // true_lzc + 1 == leading_zero_count_sgn - lzc_dec + 1, but the -lzc_dec
      // is INVISIBLE to fpnew_mxdotp_norm_window: lzc_dec implies the true
      // magnitude is 2**(LZC_SUM_WIDTH-1-leading_zero_count_sgn+1), so both
      // shift amounts push the single set bit out of the LZC_SUM_WIDTH-bit
      // container and the window and its sticky are zero either way.  Only the
      // exponent keeps the correction (exponent_major_corr above).
      norm_shamt          = leading_zero_count_sgn + 1;
      normalized_exponent = final_tentative_exponent;
    end else begin
      // lzc + (exponent_major - lzc) == exponent_major (mod 2**DST_EXP_WIDTH)
      norm_shamt          = exponent_major[SHIFT_AMOUNT_WIDTH-1:0];
      normalized_exponent = '0; // subnormals encoded as 0
    end
  end

  // Extract the 24-bit normalised window directly and collect the sticky OR of
  // the bits that fall below it inside the narrowing shifter.
  fpnew_mxdotp_norm_window #(
    .SoPFixedWidth ( SoPFixedWidth )
  ) i_norm_window (
    .sum_magnitude ( sum_magnitude  ),
    .norm_shamt    ( norm_shamt     ),
    .final_mantissa( final_mantissa ),
    .sticky_bits_or( sticky_bits_or )
  );

  assign sum_magnitude_o                   = sum_magnitude;
  assign final_exponent                    = normalized_exponent;
  assign sticky_after_norm                 = sticky_bits_or | accumulator_sticky;
endmodule

// Rounds normalized result to destination format with IEEE rounding modes (RNE/RTZ/RDN/RUP/RMM).
// Detects overflow/underflow before and after rounding, generates round/sticky bits.
module fpnew_mxdotp_rounder
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter fpnew_pkg::fmt_logic_t FpDstFmtConfig = MxdotpDstFpFmtConfig,
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS
) (
  // Input signals
  input  logic clk_i,
  input  logic rst_ni,
  input  logic final_sign,
  input  logic [DST_EXP_WIDTH-1:0] final_exponent,
  input  logic [DST_PRECISION_BITS-1:0] final_mantissa,
  input  logic [LZC_SUM_WIDTH-1:0] sum_magnitude,
  input  logic sticky_after_norm,
  input fpnew_pkg::fp_format_e dst_fmt,
  input fpnew_pkg::roundmode_e rnd_mode,
  // Output signals
  output logic [NUM_FORMATS-1:0][DST_WIDTH-1:0] fmt_result,
  output logic [1:0] round_sticky_bits,
  output logic of_before_round,
  output logic of_after_round,
  output logic uf_after_round
);

  // ----------------------------
  // Rounding and classification
  // ----------------------------
  logic                                             pre_round_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] pre_round_abs; // absolute value of result before rounding

  logic [NUM_FORMATS-1:0][SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] fmt_pre_round_abs; // per format
  logic [NUM_FORMATS-1:0][1:0]                                       fmt_round_sticky_bits;

  logic [NUM_FORMATS-1:0]                           fmt_of_after_round;
  logic [NUM_FORMATS-1:0]                           fmt_uf_after_round;

  logic                                             rounded_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] rounded_abs; // absolute value of result after rounding
  logic                                             result_zero;

  // ------------------------------------------------------------------
  // of/uf AFTER ROUNDING, COMPUTED FROM THE PRE-ROUND OPERANDS.
  //
  // rounded_abs = pre_round_abs + round_up, and pre_round_abs is the
  // zero-extension of {pre_round_exponent, pre_round_mantissa}, so the only
  // way the rounding increment can reach the exponent field is a carry out
  // of the mantissa field:
  //     carry_into_exponent = round_up & (pre_round_mantissa == '1)
  // `pre_round_exponent` is at most 2**EXP_BITS-2 (the of_before_round branch
  // clamps it to exactly that, and otherwise final_exponent < 2**EXP_BITS-1),
  // hence  pre_round_exponent + carry  can neither wrap to 0 nor reach all
  // ones without the carry, which gives
  //     uf_after_round = (pre_round_exponent == 0)         & ~carry
  //     of_after_round = (pre_round_exponent == 2**E - 2)  &  carry
  // Both are bit-identical to the old `rounded_abs[E+M-1:M] == 0 / '1`, but
  // they no longer sit behind the carry-propagate rounding incrementer: the
  // status cone now leaves `final_mantissa` through one AND reduction.
  // ------------------------------------------------------------------
  logic [NUM_FORMATS-1:0] fmt_exp_is_zero;   // pre_round_exponent == 0
  logic [NUM_FORMATS-1:0] fmt_exp_is_max1;   // pre_round_exponent == 2**EXP_BITS-2
  logic [NUM_FORMATS-1:0] fmt_man_all_ones;  // &pre_round_mantissa
  logic                   round_up_pre;      // replica of fpnew_rounding's decision

  // Classification before round. RISC-V mandates checking underflow AFTER rounding
  assign of_before_round = final_exponent >= 2**(fpnew_pkg::exp_bits(dst_fmt))-1; // infinity exponent is all ones

  // Pack exponent and mantissa into proper rounding form
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_res_assemble
    // Set up some constants
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ALL_EXTRA_BITS = fpnew_pkg::maximum(SUPER_DST_MAN_BITS-MAN_BITS+1+DST_PRECISION_BITS+PRECISION_BITS+2+1, 1);

    logic [EXP_BITS-1:0] pre_round_exponent;
    logic [MAN_BITS-1:0] pre_round_mantissa;

    if (FpDstFmtConfig[fmt]) begin : active_dst_format

      assign pre_round_exponent = (of_before_round) ? 2**EXP_BITS-2 : final_exponent[EXP_BITS-1:0];
      assign pre_round_mantissa = (of_before_round) ? '1 : final_mantissa[SUPER_DST_MAN_BITS-:MAN_BITS];
      // Assemble result before rounding. In case of overflow, the largest normal value is set.
      assign fmt_pre_round_abs[fmt] = {pre_round_exponent, pre_round_mantissa}; // 0-extend

      // Pre-round predicates for the of/uf classification below
      assign fmt_exp_is_zero[fmt]   = ~(| pre_round_exponent);
      assign fmt_exp_is_max1[fmt]   = (pre_round_exponent == EXP_BITS'(2**EXP_BITS-2));
      assign fmt_man_all_ones[fmt]  = (& pre_round_mantissa);

      // Round bit is after mantissa (1 in case of overflow for rounding)
      assign fmt_round_sticky_bits[fmt][1] = final_mantissa[SUPER_DST_MAN_BITS-MAN_BITS] |
                                             of_before_round;

      // remaining bits in mantissa to sticky (1 in case of overflow for rounding)
      if (MAN_BITS < SUPER_DST_MAN_BITS) begin : narrow_sticky
        assign fmt_round_sticky_bits[fmt][0] = (| final_mantissa[SUPER_DST_MAN_BITS-MAN_BITS-1:0]) |
                                               sticky_after_norm | of_before_round;
      end else begin : normal_sticky
        assign fmt_round_sticky_bits[fmt][0] = sticky_after_norm | of_before_round;
      end
    end else begin : inactive_format
      assign fmt_pre_round_abs[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_round_sticky_bits[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_exp_is_zero[fmt]   = 1'b0;
      assign fmt_exp_is_max1[fmt]   = 1'b0;
      assign fmt_man_all_ones[fmt]  = 1'b0;
    end
  end

  // Assemble result before rounding. In case of overflow, the largest normal value is set.
  assign pre_round_abs      = fmt_pre_round_abs[dst_fmt];

  // In case of overflow, the round and sticky bits are set for proper rounding
  assign round_sticky_bits  = fmt_round_sticky_bits[dst_fmt];
  assign pre_round_sign     = final_sign;

  // Bit-identical copy of fpnew_rounding's `rounding_decision` always_comb
  // (EnableRSR = 0 as instantiated below, so RSR is the DONT_CARE branch).
  // It reads exactly the signals that block reads, so round_up_pre is the
  // same function of the same inputs as the round_up inside the instance.
  always_comb begin : rounding_decision_replica
    unique case (rnd_mode)
      fpnew_pkg::RNE:
        unique case (round_sticky_bits)
          2'b00,
          2'b01:   round_up_pre = 1'b0;
          2'b10:   round_up_pre = pre_round_abs[0];
          2'b11:   round_up_pre = 1'b1;
          default: round_up_pre = fpnew_pkg::DONT_CARE;
        endcase
      fpnew_pkg::RTZ: round_up_pre = 1'b0;
      fpnew_pkg::RDN: round_up_pre = (| round_sticky_bits) ? pre_round_sign  : 1'b0;
      fpnew_pkg::RUP: round_up_pre = (| round_sticky_bits) ? ~pre_round_sign : 1'b0;
      fpnew_pkg::RMM: round_up_pre = round_sticky_bits[1];
      fpnew_pkg::ROD: round_up_pre = ~pre_round_abs[0] & (| round_sticky_bits);
      fpnew_pkg::RSR: round_up_pre = fpnew_pkg::DONT_CARE;
      default:        round_up_pre = fpnew_pkg::DONT_CARE;
    endcase
  end

  // Perform the rounding
  fpnew_rounding #(
    .AbsWidth     ( SUPER_DST_EXP_BITS + SUPER_DST_MAN_BITS )
  ) i_fpnew_rounding (
    .clk_i                      ( clk_i                    ),
    .rst_ni                     ( rst_ni                   ),
    .id_i                       ( '0                       ),
    .abs_value_i                ( pre_round_abs            ),
    .en_rsr_i                   ( 1'b0                     ),
    .sign_i                     ( pre_round_sign           ),
    .round_sticky_bits_i        ( round_sticky_bits        ),
    .stochastic_rounding_bits_i ( '0                       ),
    .rnd_mode_i                 ( rnd_mode                 ),
    .effective_subtraction_i    ( 1'b0 ), // Effective subtraction is not implemented as RNE is used
    .abs_rounded_o              ( rounded_abs              ),
    .sign_o                     ( rounded_sign             ),
    .exact_zero_o               ( result_zero              )
  );


  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_sign_inject
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpDstFmtConfig[fmt]) begin : active_dst_format
      logic carry_into_exponent;
      assign carry_into_exponent = round_up_pre & fmt_man_all_ones[fmt];
      always_comb begin : post_process
        // detect of / uf -- from the PRE-round operands, see the comment above
        fmt_uf_after_round[fmt] = fmt_exp_is_zero[fmt] & ~carry_into_exponent; // denormal
        fmt_of_after_round[fmt] = fmt_exp_is_max1[fmt] &  carry_into_exponent; // inf exp.

        // Assemble regular result, nan box short ones.
        fmt_result[fmt]               = '1;
        fmt_result[fmt][FP_WIDTH-1:0] = {rounded_sign, rounded_abs[EXP_BITS+MAN_BITS-1:0]};
      end
    end else begin : inactive_format
      assign fmt_uf_after_round[fmt] = fpnew_pkg::DONT_CARE;
      assign fmt_of_after_round[fmt] = fpnew_pkg::DONT_CARE;
      assign fmt_result[fmt]         = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Classification after rounding select by destination format
  assign uf_after_round = fmt_uf_after_round[dst_fmt];
  assign of_after_round = fmt_of_after_round[dst_fmt];
endmodule
