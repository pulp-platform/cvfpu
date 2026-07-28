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
      logic [2*VectorSize-1:0][FP_WIDTH-1:0] trimmed_ops;

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
        assign trimmed_ops[op]       = operands_post_inp_pipe[op][FP_WIDTH-1:0];
        assign fmt_sign[fmt][op]     = operands_post_inp_pipe[op][FP_WIDTH-1];
        assign fmt_exponent[fmt][op] = signed'({1'b0, operands_post_inp_pipe[op][MAN_BITS+:EXP_BITS]});
        assign fmt_mantissa[fmt][op] = operands_post_inp_pipe[op][MAN_BITS-1:0] <<
                                       (SUPER_MAN_BITS - MAN_BITS); // move to left of mantissa
      end
    end else begin : inactive_src_format
      assign info_q[fmt][2*VectorSize-1:0]  = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_sign[fmt]                  = fpnew_pkg::DONT_CARE;             // format disabled
      assign fmt_exponent[fmt]              = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_mantissa[fmt]              = '{default: fpnew_pkg::DONT_CARE}; // format disabled
    end
  end

  if (FP6VectorSize != 0) begin : fp6_classifier
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

  if (FP4VectorSize != 0) begin : fp4_classifier
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
  parameter fpnew_pkg::fmt_logic_t FpDstFmtConfig = MxdotpDstFpFmtConfig,
  parameter int unsigned           VectorSize     = 8
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
  input  fpnew_pkg::fp_format_e                dst_fmt,
  // Output signals: special_result, special_status, result_is_special
  output logic [DST_WIDTH-1:0]                 special_result,
  output fpnew_pkg::status_t                   special_status,
  output logic                                 result_is_special
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
  // Special case handling
  // ----------------------
  logic               [NUM_FORMATS-1:0][DST_WIDTH-1:0] fmt_special_result;
  fpnew_pkg::status_t [NUM_FORMATS-1:0]                fmt_special_status;
  logic               [NUM_FORMATS-1:0]                fmt_result_is_special;

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_special_results
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    localparam logic [EXP_BITS-1:0] QNAN_EXPONENT = '1;
    localparam logic [MAN_BITS-1:0] QNAN_MANTISSA = 2**(MAN_BITS-1);
    localparam logic [MAN_BITS-1:0] ZERO_MANTISSA = '0;

    if (FpDstFmtConfig[fmt]) begin : active_format
      always_comb begin : special_cases
        logic [FP_WIDTH-1:0] special_res;

        // Default assignment
        special_res                = {1'b0, QNAN_EXPONENT, QNAN_MANTISSA}; // qNaN
        fmt_special_status[fmt]    = '0;
        fmt_result_is_special[fmt] = 1'b0;

        // Handle potentially mixed nan & infinity input => important for the case where infinity and
        // zero are multiplied and added to a qNaN.
        // RISC-V mandates raising the NV exception in these cases:
        // (inf * 0) + c or (0 * inf) + c INVALID, no matter c (even quiet NaNs)
        if (any_produced_nan) begin
          fmt_result_is_special[fmt] = 1'b1; // bypass OP, output is the canonical qNaN
          fmt_special_status[fmt].NV = 1'b1; // invalid operation
        // NaN Inputs cause canonical quiet NaN at the output and maybe invalid OP
        end else if (any_operand_nan) begin
          fmt_result_is_special[fmt] = 1'b1;           // bypass OP, output is the canonical qNaN
          fmt_special_status[fmt].NV = signalling_nan; // raise the invalid operation flag if signalling
        // Special cases involving infinity
        end else if (any_operand_inf) begin
          fmt_result_is_special[fmt] = 1'b1; // bypass OP
          // Effective addition of opposite infinities (±inf - ±inf) is invalid!
          if (any_pos_inf && any_neg_inf) begin
            fmt_special_status[fmt].NV = 1'b1; // invalid operation
          // Handle cases where output will be inf because of inf product input
          end else if (any_pos_inf) begin
            // Result is infinity with the positive sign
            special_res = {1'b0, QNAN_EXPONENT, ZERO_MANTISSA};
          // Handle cases where the second product is inf
          end else if (any_neg_inf) begin
            // Result is infinity with the negative sign
            special_res = {1'b1, QNAN_EXPONENT, ZERO_MANTISSA};
          end
        end
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

  // Detect special case from source format
  assign result_is_special = fmt_result_is_special[dst_fmt];
  // Signalling input NaNs raise invalid flag, otherwise no flags set
  assign special_status = fmt_special_status[dst_fmt];
  // Assemble result according to destination format
  assign special_result = fmt_special_result[dst_fmt];
endmodule

// Adds two signed 8-bit scale values to produce a 9-bit combined scale.
module fpnew_mxdotp_scale_adder
  import fpnew_mxdotp_multi_pkg::*;
(
  // Input signals
  input  logic signed [1:0][SCALE_WIDTH-1:0] operands_c,
  output logic signed [SCALE_WIDTH:0] scale // +1 for addition
);
  // ------------------
  // Scale data path
  // ------------------
  assign scale = signed'(operands_c[0]) + signed'(operands_c[1]);
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

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_mantissa_fp8
    always_comb begin
      if (src_is_int && int_fmt == fpnew_pkg::INT8) begin : int8
        // For INT8, we use the full 8-bit mantissa
        mantissa_a[i] = operands_a[i][7:0];
        mantissa_b[i] = operands_b[i][7:0];
      end else begin : fp8
        // Add implicit bits to mantissae and pad with zeros
        mantissa_a[i] = {4'b0, info_a[i].is_normal, operands_a[i].mantissa};
        mantissa_b[i] = {4'b0, info_b[i].is_normal, operands_b[i].mantissa};
        if (operands_a[i].sign ^ operands_b[i].sign) begin
          // If the signs are different, we need to negate one mantissa
          mantissa_a[i] = -signed'(mantissa_a[i]);
        end
      end
    end
  end

  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_mantissa
    assign product_signed[i] = signed'(mantissa_a[i]) * signed'(mantissa_b[i]);
  end
endmodule

// Shifts products left by (exp_a + exp_b - 2×bias + SOP_SHIFT) to align to fixed-point anchor.
// Handles FP8/FP6/FP4 with format-specific offsets; INT8 shifts directly to anchor position.
module fpnew_mxdotp_product_shifter
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter type         SrcType          = logic,
  parameter int unsigned LocalVectorSize  = 8,
  parameter fpnew_pkg::fp_format_e SrcFmt = fpnew_pkg::FP8,
  parameter int unsigned ProductBits      = 4,
  parameter int unsigned ExpWidth         = 8,
  parameter int unsigned OutputWidth      = 70
) (
  // Input signals
  input  SrcType [LocalVectorSize-1:0] operands_a,
  input  SrcType [LocalVectorSize-1:0] operands_b,
  input  logic [LocalVectorSize-1:0][ProductBits-1:0] product_signed,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_a,
  input  fpnew_pkg::fp_info_t [LocalVectorSize-1:0] info_b,
  input  fpnew_pkg::fp_format_e src_fmt,
  input  fpnew_pkg::int_format_e int_fmt,
  input  logic src_is_int,
  output logic signed [LocalVectorSize-1:0][OutputWidth-1:0] shifted_product
);
  // ------------------
  // Shift data path
  // ------------------
  logic signed [LocalVectorSize-1:0][ExpWidth-1:0] exponent_product;

  // Calculate the non-biased exponent of the product
  for (genvar i = 0; i < LocalVectorSize; i++) begin : gen_exponent_adjustment
    assign exponent_product[i] = operands_a[i].exponent + info_a[i].is_subnormal
                                + operands_b[i].exponent + info_b[i].is_subnormal
                                - 2*signed'(bias_constant(src_fmt));
    if (SrcFmt == fpnew_pkg::FP8) begin
      always_comb begin // TODO: Generate only for INT8 vs FP8
        if (src_is_int && int_fmt == fpnew_pkg::INT8) begin
          // INT8: shift to integer position
          shifted_product[i] = signed'(product_signed[i]) << ANCHOR;
        end else begin
          // Right shift the significand by anchor point - exponent
          // sum of four 9-bit numbers can be at most 11 bits, for 69 bits output we need to shift by 69 - 11 = 58
          // 58-30=28 plus inherit 6 fractional bits from the multiplication -> point moves to 28+6=34
          // max shift can be 58 (28 + exp-max(30)), min shift is 0 (28 + exp-min(-28))
          shifted_product[i] = signed'(product_signed[i]) << (signed'(SOP_SHIFT) + signed'(exponent_product[i]));
        end
      end
    end else if (SrcFmt == fpnew_pkg::FP6) begin
      // E3 exponent_product is in range [-4, 8], requires 5b for signed representation
      // To make shift positive, we scale by 4
      assign shifted_product[i] = signed'(product_signed[i]) << (signed'(4) + signed'(exponent_product[i]));
    end else begin
      // exponent_product is negative only for zero inputs for FP4
      assign shifted_product[i] = signed'(product_signed[i]) << exponent_product[i];
    end
  end
endmodule

// Sums all shifted products in the vector.
module fpnew_mxdotp_adder_tree
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned LocalVectorSize = 8,
  parameter int unsigned InputWidth      = 4,
  parameter int unsigned OutputWidth     = 70
) (
  // Input signals
  input  logic signed [LocalVectorSize-1:0][InputWidth-1:0] shifted_product,
  output logic signed [OutputWidth-1:0] sum_product
);
  // ------------------
  // Adder data path
  // ------------------
  // Sum the products
  always_comb begin : sum_products
    sum_product = '0;
    for (int i = 0; i < LocalVectorSize; i++) begin : gen_sum_products
      sum_product += signed'(shifted_product[i]);
    end
  end
endmodule

// Adds FP8, FP6, and FP4 sum-of-products; shifts FP6 and FP4 sums to align before adding.
// When FP6 is disabled, sum_product_fp6 is zero and optimized away by synthesis.
module fpnew_mxdotp_format_adder
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  parameter int unsigned Fp6SumWidth = FP6_PROD_SHIFT_WIDTH,
  parameter int unsigned Fp4SumWidth = FP4_PROD_SHIFT_WIDTH,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1) // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
) (
  input  logic signed [SoPFixedWidth-1:0] sum_product_fp8,
  input  logic signed [Fp6SumWidth-1:0]     sum_product_fp6,
  input  logic signed [Fp4SumWidth-1:0]     sum_product_fp4,
  output logic signed [FIXED_SUM_WIDTH-1:0] sum_product
);
  // ------------------
  // Adder data path
  // ------------------
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_fp4_shifted;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_fp6_shifted;

  assign sum_product_fp4_shifted = signed'(sum_product_fp4) << (SOP_SHIFT+2*(SUPER_MAN_BITS-FP4_MAN_BITS));
  assign sum_product_fp6_shifted = signed'(sum_product_fp6) << (SOP_SHIFT-4+2*(SUPER_MAN_BITS-FP6_MAN_BITS)); // 4 is subtracted to account for the 4-bit shift in the product shifter
  assign sum_product = sum_product_fp8 + sum_product_fp4_shifted + sum_product_fp6_shifted;
endmodule

// Shifts accumulator right to align with sum-of-products based on scale and accumulator exponent.
// Computes shift amount, handles sticky bits, and detects if accumulator dominates the result.
module fpnew_mxdotp_accumulator_shift
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int signed MAX_ACC_SHIFT_AMOUNT = FIXED_SUM_WIDTH - DST_PRECISION_BITS - 1
) (
  // Input signals
  input  logic signed [FIXED_SUM_WIDTH-1:0] sum_product,
  input  logic [SCALE_WIDTH:0] scale,
  input  fp_dst_t operand_d,
  input  fpnew_pkg::fp_info_t info_d,
  input  fpnew_pkg::fp_format_e dst_fmt,
  output logic result_is_accumulator,
  output logic accumulator_is_right_shifted,
  output logic signed [9:0] accumulator_right_shift_amount,
  output logic signed [DST_PRECISION_BITS-1:0] accumulator_remaining,
  output logic accumulator_sticky,
  output logic signed [DST_PRECISION_BITS :0] signed_mantissa_d,
  output logic signed [FIXED_SUM_WIDTH-1:0] accumulator_shifted
);

  // -----------------------------
  // Accumulator shift data path
  // -----------------------------
  logic signed [9:0] accumulator_shift_amount;
  logic signed [DST_EXP_WIDTH-1:0] exponent_d;
  logic [DST_PRECISION_BITS-1:0] mantissa_d;

  // Zero-extend exponents into signed container - implicit width extension
  assign exponent_d = {1'b0, operand_d.exponent};
  assign mantissa_d = {info_d.is_normal, operand_d.mantissa};
  assign signed_mantissa_d = operand_d.sign ? -mantissa_d : mantissa_d;

  // Calculate the shift amount for the accumulator, range=[-370,394-9b -> signed 10b]
  assign accumulator_shift_amount = signed'(ANCHOR - SUPER_DST_MAN_BITS) - signed'(scale)
                                     + signed'(exponent_d + info_d.is_subnormal)
                                     - signed'(bias_constant(dst_fmt));

  always_comb begin : accumulator_shift
    result_is_accumulator = 1'b0;
    accumulator_is_right_shifted = 1'b0;
    accumulator_right_shift_amount = '0;
    accumulator_remaining = '0;
    accumulator_sticky = 1'b0;
    if (accumulator_shift_amount > MAX_ACC_SHIFT_AMOUNT) begin
      // SoP is too small to change the accumulator, result is the accumulator
      accumulator_shifted = '0;
      result_is_accumulator = 1'b1;
    end else if (accumulator_shift_amount >= 0) begin
      accumulator_shifted = signed'(signed_mantissa_d) <<< accumulator_shift_amount;
    end else begin
      accumulator_is_right_shifted = 1'b1;
      accumulator_right_shift_amount = -accumulator_shift_amount;
      accumulator_shifted = signed'(signed_mantissa_d) >>> accumulator_right_shift_amount;
      if (accumulator_right_shift_amount > DST_PRECISION_BITS) begin
        result_is_accumulator = (sum_product == '0) ? 1'b1 : 1'b0;
        accumulator_remaining = signed'(signed_mantissa_d) >>> (accumulator_right_shift_amount - DST_PRECISION_BITS);
        accumulator_sticky = |(signed'(signed_mantissa_d) & ((1 << (accumulator_right_shift_amount - DST_PRECISION_BITS)) - 1));
      end else begin
        accumulator_remaining = signed'(signed_mantissa_d) << (DST_PRECISION_BITS - accumulator_right_shift_amount);
        accumulator_sticky = 1'b0;
      end
    end
  end
endmodule

// Adds aligned accumulator to sum-of-products, extending with accumulator remainder bits.
module fpnew_mxdotp_add_accumulator_sop
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS
) (
  // Input signals
  input  logic signed [FIXED_SUM_WIDTH-1:0] sum_product,
  input  logic signed [FIXED_SUM_WIDTH-1:0] accumulator_shifted,
  input  logic signed [DST_PRECISION_BITS-1:0] accumulator_remaining,
  output logic signed [LZC_SUM_WIDTH-1:0] sum_product_accumulator_extended
);

  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_accumulator;

  assign sum_product_accumulator = sum_product + accumulator_shifted;
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
  input  logic signed [DST_PRECISION_BITS :0] signed_mantissa_d,
  input  logic accumulator_is_right_shifted,
  input  logic signed [9:0] accumulator_right_shift_amount,
  input  logic accumulator_sticky,
  // Output signals
  output logic final_sign,
  output logic [LZC_SUM_WIDTH-1:0] sum_magnitude
);
  // If sum is negative, complement to feed into leading zero counter
  assign final_sign = sum_product_accumulator_extended[LZC_SUM_WIDTH-1];

  always_comb begin : get_twos_complement
    if (final_sign) begin
      sum_magnitude = ~sum_product_accumulator_extended + 1;
      if (accumulator_is_right_shifted && accumulator_right_shift_amount > DST_PRECISION_BITS && signed_mantissa_d != 0 && accumulator_sticky) begin
        sum_magnitude = ~sum_product_accumulator_extended;
      end
    end else begin
      sum_magnitude = sum_product_accumulator_extended;
    end
  end
endmodule

// Shifts magnitude left by normalization amount to align leading 1 to implicit bit position.
module fpnew_mxdotp_norm_shift
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS,
  // Shift amount width: $clog2(DST_BIAS - ANCHOR + (scale_a+scale_b) + FIXED_SUM_WIDTH - 1)
  localparam int unsigned SHIFT_AMOUNT_WIDTH = $clog2(fpnew_pkg::bias(fpnew_pkg::FP32) - ANCHOR + 2**(SCALE_WIDTH) - 1 + FIXED_SUM_WIDTH - 1)
) (
  // Input signals
  input  logic [LZC_SUM_WIDTH-1:0] sum_magnitude,
  input  logic [SHIFT_AMOUNT_WIDTH-1:0] norm_shamt,
  // Output signals
  output logic [LZC_SUM_WIDTH-1:0] sum_shifted
);
  // ------------------
  // Normalization shift
  // ------------------

  // Shift the sum to normalize it
  assign sum_shifted = sum_magnitude << norm_shamt;
endmodule

// Computes normalization shift amount and biased exponent from sign-magnitude sum via leading-zero
// count. Handles subnormals (normalized_exponent = 0) and zero (lzc_zeroes path).
module fpnew_mxdotp_norm_lzc
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned SoPFixedWidth = 70,
  // Do not change the following parameters
  localparam int unsigned FIXED_SUM_WIDTH = 1 + DST_PRECISION_BITS + 1 + (SoPFixedWidth - 1), // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH   = FIXED_SUM_WIDTH + DST_PRECISION_BITS,
  localparam int unsigned LZC_RESULT_WIDTH = $clog2(LZC_SUM_WIDTH)
) (
  input  logic [LZC_SUM_WIDTH-1:0] sum_magnitude,
  output logic signed [LZC_RESULT_WIDTH:0] leading_zero_count_sgn,
  output logic lzc_zeroes
);
  logic [LZC_RESULT_WIDTH-1:0] leading_zero_count;

  lzc #(
    .WIDTH ( LZC_SUM_WIDTH ),
    .MODE  ( 1             ) // MODE = 1 counts leading zeroes
  ) i_lzc (
    .in_i    ( sum_magnitude      ),
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
  input  logic [LZC_SUM_WIDTH-1:0]          sum_magnitude,
  input  logic signed [LZC_RESULT_WIDTH:0]  leading_zero_count_sgn,
  input  logic                              lzc_zeroes,
  input  logic [SCALE_WIDTH:0]              scale,
  input  logic                              accumulator_sticky,
  output logic [DST_PRECISION_BITS-1:0]     final_mantissa,
  output logic signed [DST_EXP_WIDTH-1:0]   final_exponent,
  output logic                              sticky_after_norm
);
  logic signed [DST_EXP_WIDTH-1:0]      final_tentative_exponent;
  logic        [SHIFT_AMOUNT_WIDTH-1:0] norm_shamt;
  logic signed [DST_EXP_WIDTH-1:0]      normalized_exponent;

  logic [LZC_SUM_WIDTH-1:0]                    sum_shifted;
  logic [LZC_SUM_WIDTH-DST_PRECISION_BITS-1:0] sum_sticky_bits;

  // Calculate the biased exponent (excess-127 form)
  // The exponent-major is -scaled_anchor
  // exponent = 127 - scaled_anchor + (94-count-1) + increment_exponent [-195, 315 9b -> 10b signed]
  assign final_tentative_exponent = 127 - (signed'(ANCHOR) - signed'(scale))
                                    + (signed'(FIXED_SUM_WIDTH) - leading_zero_count_sgn - 1); // 127 is bias of dst format

  // Normalization shift amount based on exponents and LZC (unsigned as only left shifts)
  always_comb begin : norm_shift_amount
    if (final_tentative_exponent > 0 && !lzc_zeroes) begin
      norm_shamt          = leading_zero_count_sgn + 1;
      normalized_exponent = final_tentative_exponent;
    end else begin
      norm_shamt          = leading_zero_count_sgn + final_tentative_exponent;
      normalized_exponent = '0; // subnormals encoded as 0
    end
  end

  fpnew_mxdotp_norm_shift #(
    .SoPFixedWidth  ( SoPFixedWidth )
  ) i_norm_shift (
    .sum_shifted  ( sum_shifted  ),
    .sum_magnitude( sum_magnitude),
    .norm_shamt   ( norm_shamt   )
  );

  // LSB of final mantissa is the rounding bit
  assign {final_mantissa, sum_sticky_bits} = sum_shifted;
  assign final_exponent                    = normalized_exponent;
  assign sticky_after_norm                 = (|sum_sticky_bits) | accumulator_sticky;
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
    end
  end

  // Assemble result before rounding. In case of overflow, the largest normal value is set.
  assign pre_round_abs      = fmt_pre_round_abs[dst_fmt];

  // In case of overflow, the round and sticky bits are set for proper rounding
  assign round_sticky_bits  = fmt_round_sticky_bits[dst_fmt];
  assign pre_round_sign     = final_sign;

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
      always_comb begin : post_process
        // detect of / uf
        fmt_uf_after_round[fmt] = rounded_abs[EXP_BITS+MAN_BITS-1:MAN_BITS] == '0; // denormal
        fmt_of_after_round[fmt] = rounded_abs[EXP_BITS+MAN_BITS-1:MAN_BITS] == '1; // inf exp.

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
