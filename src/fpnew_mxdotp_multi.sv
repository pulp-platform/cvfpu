// Copyright 2024-2025 ETH Zurich and University of Bologna.
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

`include "common_cells/registers.svh"

module fpnew_mxdotp_multi #(
  // One-hot config string: | FP32 | FP64 | FP16 | FP8 | FP16ALT | FP8ALT |
  parameter fpnew_pkg::fmt_logic_t   SrcDotpFpFmtConfig = 6'b000101, // Supported source formats (FP8, FP8ALT)
  parameter fpnew_pkg::fmt_logic_t   DstDotpFpFmtConfig = 6'b100000, // Supported destination formats (FP32)
  parameter int unsigned             VectorSize  = 8,
  parameter int unsigned             NumPipeRegs = 0,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::BEFORE,
  parameter type                     TagType     = logic,
  parameter type                     AuxType     = logic,
  // Do not change
  localparam int unsigned SRC_WIDTH = fpnew_pkg::max_fp_width(SrcDotpFpFmtConfig),
  localparam int unsigned DST_WIDTH = fpnew_pkg::max_fp_width(DstDotpFpFmtConfig),
  localparam int unsigned SCALE_WIDTH = 8,
  localparam int unsigned NUM_OPERANDS = 2*VectorSize+1, // scale is not included
  localparam int unsigned NUM_FORMATS = fpnew_pkg::NUM_FP_FORMATS
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Input signals
  input  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_a_i,
  input  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_b_i,
  input  logic [1:0][SCALE_WIDTH-1:0] operands_c_i, // 2 operands
  input  logic [DST_WIDTH-1:0]        operand_d_i, // 1 operand, accumulator
  input  logic [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] is_boxed_i,
  input  fpnew_pkg::roundmode_e       rnd_mode_i,
  input  fpnew_pkg::operation_e       op_i,
  input  logic                        op_mod_i,
  input  fpnew_pkg::fp_format_e       src_fmt_i, // format of the multiplicands
  input  fpnew_pkg::fp_format_e       dst_fmt_i, // format of the addend and result
  input  TagType                      tag_i,
  input  logic                        mask_i,
  input  AuxType                      aux_i,
  // Input Handshake
  input  logic                        in_valid_i,
  output logic                        in_ready_o,
  input  logic                        flush_i,
  // Output signals
  output logic [DST_WIDTH-1:0]        result_o,
  output fpnew_pkg::status_t          status_o,
  output logic                        extension_bit_o,
  output TagType                      tag_o,
  output logic                        mask_o,
  output AuxType                      aux_o,
  // Output handshake
  output logic                        out_valid_o,
  input  logic                        out_ready_i,
  // Indication of valid data in flight
  output logic                        busy_o
);

  // ----------
  // Constants
  // ----------
  // The super-format that can hold all formats
  localparam fpnew_pkg::fp_encoding_t SUPER_FORMAT = fpnew_pkg::super_format(SrcDotpFpFmtConfig);
  localparam fpnew_pkg::fp_encoding_t SUPER_DST_FORMAT = fpnew_pkg::super_format(DstDotpFpFmtConfig);

  localparam int unsigned SUPER_EXP_BITS = SUPER_FORMAT.exp_bits;
  localparam int unsigned SUPER_MAN_BITS = SUPER_FORMAT.man_bits;
  localparam int unsigned SUPER_DST_EXP_BITS = SUPER_DST_FORMAT.exp_bits;
  localparam int unsigned SUPER_DST_MAN_BITS = SUPER_DST_FORMAT.man_bits;

  // Precision bits 'p' include the implicit bit
  localparam int unsigned PRECISION_BITS = SUPER_MAN_BITS + 1;
  // Destination precision bits 'p_dst' include the implicit bit
  localparam int unsigned DST_PRECISION_BITS = SUPER_DST_MAN_BITS + 1;

  // Algorithm constants
  localparam int unsigned ANCHOR = 34; // Fractional point position
  localparam int unsigned INT_BITS = 32;
  localparam int unsigned VECTOR_BITS = $clog2(VectorSize);
  localparam int unsigned SOP_FIXED_WIDTH = 1 + VECTOR_BITS + INT_BITS + ANCHOR;
  localparam int unsigned FIXED_SUM_WIDTH  = 1 + DST_PRECISION_BITS + 1 + (SOP_FIXED_WIDTH - 1); // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH    = FIXED_SUM_WIDTH + DST_PRECISION_BITS;
  localparam int unsigned LZC_RESULT_WIDTH = $clog2(LZC_SUM_WIDTH);
  localparam int signed MAX_ACC_SHIFT_AMOUNT = FIXED_SUM_WIDTH - DST_PRECISION_BITS - 1; // Maximum allowable shift, -1 for the sign bit
  localparam int unsigned SOP_SHIFT = ANCHOR - 2*SUPER_MAN_BITS; // Constant left shift amount for the SOP to align the fractional point

  localparam int unsigned EXP_WIDTH = SUPER_EXP_BITS + 1;
  localparam int unsigned DST_EXP_WIDTH = SUPER_DST_EXP_BITS + 2; // +2 for overflow handling
  // Shift amount width: $clog2(DST_BIAS - ANCHOR + (scale_a+scale_b) + FIXED_SUM_WIDTH - 1)
  localparam int unsigned SHIFT_AMOUNT_WIDTH = $clog2(fpnew_pkg::bias(fpnew_pkg::FP32) - ANCHOR + 2**(SCALE_WIDTH) - 1 + FIXED_SUM_WIDTH - 1);

  // Pipelines
  localparam NUM_INP_REGS = PipeConfig == fpnew_pkg::BEFORE
                            ? NumPipeRegs
                            : (PipeConfig == fpnew_pkg::DISTRIBUTED
                               ? ((NumPipeRegs + 1) / 3) // Second to get distributed regs
                               : 0); // no regs here otherwise
  localparam NUM_MID_REGS = PipeConfig == fpnew_pkg::INSIDE
                          ? NumPipeRegs
                          : (PipeConfig == fpnew_pkg::DISTRIBUTED
                             ? ((NumPipeRegs + 2) / 3) // First to get distributed regs
                             : 0); // no regs here otherwise
  localparam NUM_OUT_REGS = PipeConfig == fpnew_pkg::AFTER
                            ? NumPipeRegs
                            : (PipeConfig == fpnew_pkg::DISTRIBUTED
                               ? (NumPipeRegs / 3) // Last to get distributed regs
                               : 0); // no regs here otherwise

  // ----------------
  // Type definition
  // ----------------
  typedef struct packed {
    logic                      sign;
    logic [SUPER_EXP_BITS-1:0] exponent;
    logic [SUPER_MAN_BITS-1:0] mantissa;
  } fp_src_t;
  typedef struct packed {
    logic                          sign;
    logic [SUPER_DST_EXP_BITS-1:0] exponent;
    logic [SUPER_DST_MAN_BITS-1:0] mantissa;
  } fp_dst_t;

  // ---------------
  // Input pipeline
  // ---------------
  // Selected pipeline output signals as non-arrays
  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_a_q;
  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_b_q;
  logic [1:0][SCALE_WIDTH-1:0] operands_c_q;
  logic [DST_WIDTH-1:0] operand_d_q;
  fpnew_pkg::fp_format_e src_fmt_q;
  fpnew_pkg::fp_format_e dst_fmt_q;

  // Input pipeline signals, index i holds signal after i register stages
  logic                  [0:NUM_INP_REGS][VectorSize-1:0][SRC_WIDTH-1:0]   inp_pipe_operands_a_q;
  logic                  [0:NUM_INP_REGS][VectorSize-1:0][SRC_WIDTH-1:0]   inp_pipe_operands_b_q;
  logic                  [0:NUM_INP_REGS][1:0][SCALE_WIDTH-1:0] inp_pipe_operands_c_q;
  logic                  [0:NUM_INP_REGS][DST_WIDTH-1:0]        inp_pipe_operand_d_q;
  logic                  [0:NUM_INP_REGS][NUM_FORMATS-1:0][NUM_OPERANDS-1:0] inp_pipe_is_boxed_q;
  fpnew_pkg::roundmode_e [0:NUM_INP_REGS]                       inp_pipe_rnd_mode_q;
  fpnew_pkg::operation_e [0:NUM_INP_REGS]                       inp_pipe_op_q;
  logic                  [0:NUM_INP_REGS]                       inp_pipe_op_mod_q;
  fpnew_pkg::fp_format_e [0:NUM_INP_REGS]                       inp_pipe_src_fmt_q;
  fpnew_pkg::fp_format_e [0:NUM_INP_REGS]                       inp_pipe_dst_fmt_q;
  TagType                [0:NUM_INP_REGS]                       inp_pipe_tag_q;
  logic                  [0:NUM_INP_REGS]                       inp_pipe_mask_q;
  AuxType                [0:NUM_INP_REGS]                       inp_pipe_aux_q;
  logic                  [0:NUM_INP_REGS]                       inp_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_INP_REGS] inp_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign inp_pipe_operands_a_q[0]   = operands_a_i;
  assign inp_pipe_operands_b_q[0]   = operands_b_i;
  assign inp_pipe_operands_c_q[0]   = operands_c_i;
  assign inp_pipe_operand_d_q[0]    = operand_d_i;
  assign inp_pipe_is_boxed_q[0]     = is_boxed_i;
  assign inp_pipe_rnd_mode_q[0]     = rnd_mode_i;
  assign inp_pipe_op_q[0]           = op_i;
  assign inp_pipe_op_mod_q[0]       = op_mod_i;
  assign inp_pipe_src_fmt_q[0]      = src_fmt_i;
  assign inp_pipe_dst_fmt_q[0]      = dst_fmt_i;
  assign inp_pipe_tag_q[0]          = tag_i;
  assign inp_pipe_mask_q[0]         = mask_i;
  assign inp_pipe_aux_q[0]          = aux_i;
  assign inp_pipe_valid_q[0]        = in_valid_i;
  // Input stage: Propagate pipeline ready signal to updtream circuitry
  assign in_ready_o = inp_pipe_ready[0];
  // Generate the register stages
  for (genvar i = 0; i < NUM_INP_REGS; i++) begin : gen_input_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign inp_pipe_ready[i] = inp_pipe_ready[i+1] | ~inp_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(inp_pipe_valid_q[i+1], inp_pipe_valid_q[i], inp_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = inp_pipe_ready[i] & inp_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(inp_pipe_operands_a_q[i+1],   inp_pipe_operands_a_q[i],   reg_ena, '0)
    `FFL(inp_pipe_operands_b_q[i+1],   inp_pipe_operands_b_q[i],   reg_ena, '0)
    `FFL(inp_pipe_operands_c_q[i+1],   inp_pipe_operands_c_q[i],   reg_ena, '0)
    `FFL(inp_pipe_operand_d_q[i+1],    inp_pipe_operand_d_q[i],    reg_ena, '0)
    `FFL(inp_pipe_is_boxed_q[i+1],     inp_pipe_is_boxed_q[i],     reg_ena, '0)
    `FFL(inp_pipe_rnd_mode_q[i+1],     inp_pipe_rnd_mode_q[i],     reg_ena, fpnew_pkg::RNE)
    `FFL(inp_pipe_op_q[i+1],           inp_pipe_op_q[i],           reg_ena, fpnew_pkg::SDOTP)
    `FFL(inp_pipe_op_mod_q[i+1],       inp_pipe_op_mod_q[i],       reg_ena, '0)
    `FFL(inp_pipe_src_fmt_q[i+1],      inp_pipe_src_fmt_q[i],      reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_dst_fmt_q[i+1],      inp_pipe_dst_fmt_q[i],      reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_tag_q[i+1],          inp_pipe_tag_q[i],          reg_ena, TagType'('0))
    `FFL(inp_pipe_mask_q[i+1],         inp_pipe_mask_q[i],         reg_ena, '0)
    `FFL(inp_pipe_aux_q[i+1],          inp_pipe_aux_q[i],          reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign operands_a_q   = inp_pipe_operands_a_q[NUM_INP_REGS];
  assign operands_b_q   = inp_pipe_operands_b_q[NUM_INP_REGS];
  assign operands_c_q   = inp_pipe_operands_c_q[NUM_INP_REGS];
  assign operand_d_q    = inp_pipe_operand_d_q[NUM_INP_REGS];
  assign src_fmt_q      = inp_pipe_src_fmt_q[NUM_INP_REGS];
  assign dst_fmt_q      = inp_pipe_dst_fmt_q[NUM_INP_REGS];

  logic [2*VectorSize-1:0][SRC_WIDTH-1:0] operands_post_inp_pipe;
  assign operands_post_inp_pipe = {operands_b_q, operands_a_q};

  // -----------------
  // Input processing
  // -----------------

  // -----------------
  // Source operands
  // -----------------
  logic        [NUM_FORMATS-1:0][2*VectorSize-1:0]                     fmt_sign;
  logic signed [NUM_FORMATS-1:0][2*VectorSize-1:0][SUPER_EXP_BITS-1:0] fmt_exponent;
  logic        [NUM_FORMATS-1:0][2*VectorSize-1:0][SUPER_MAN_BITS-1:0] fmt_mantissa;

  fpnew_pkg::fp_info_t [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] info_q;

  // FP Input initialization (Src)
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : fmt_src_init_inputs
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (SrcDotpFpFmtConfig[fmt]) begin : active_src_format
      logic [2*VectorSize-1:0][FP_WIDTH-1:0] trimmed_ops;

      // Classify input
      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 2*VectorSize                 ),
        .MX          ( 1                            ) // E4M3 special case
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_ops                                              ),
        .is_boxed_i  ( inp_pipe_is_boxed_q[NUM_INP_REGS][fmt][2*VectorSize-1:0] ),
        .info_o      ( info_q[fmt][2*VectorSize-1:0]                            )
      );
      for (genvar op = 0; op < 2*VectorSize; op++) begin : gen_operands
        assign trimmed_ops[op]       = operands_post_inp_pipe[op][FP_WIDTH-1:0];
        assign fmt_sign[fmt][op]     = operands_post_inp_pipe[op][FP_WIDTH-1];
        assign fmt_exponent[fmt][op] = signed'({1'b0, operands_post_inp_pipe[op][MAN_BITS+:EXP_BITS]});
        assign fmt_mantissa[fmt][op] = {info_q[fmt][op].is_normal, operands_post_inp_pipe[op][MAN_BITS-1:0]} <<
                                       (SUPER_MAN_BITS - MAN_BITS); // move to left of mantissa
      end
    end else begin : inactive_src_format
      assign info_q[fmt][2*VectorSize-1:0]  = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_sign[fmt]     = fpnew_pkg::DONT_CARE;             // format disabled
      assign fmt_exponent[fmt] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_mantissa[fmt] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
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

    if (DstDotpFpFmtConfig[fmt]) begin : active_dst_format
      logic [FP_WIDTH-1:0] trimmed_dst_ops;
      logic                dst_ops_is_boxed;

      assign dst_ops_is_boxed = inp_pipe_is_boxed_q[NUM_INP_REGS][fmt][NUM_OPERANDS-1];

      // Classify input
      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_dst_ops  ),
        .is_boxed_i  ( dst_ops_is_boxed ),
        .info_o      ( info_q[fmt][NUM_OPERANDS-1] )
      );
      assign trimmed_dst_ops          = operand_d_q[FP_WIDTH-1:0];
      assign fmt_dst_sign[fmt]        = operand_d_q[FP_WIDTH-1];
      assign fmt_dst_exponent[fmt]    = signed'({1'b0, operand_d_q[MAN_BITS+:EXP_BITS]});
      assign fmt_dst_mantissa[fmt]    = {info_q[fmt][NUM_OPERANDS-1].is_normal, operand_d_q[MAN_BITS-1:0]}
                                         << (SUPER_DST_MAN_BITS - MAN_BITS);
    end else begin : inactive_dst_format
      assign info_q[fmt][NUM_OPERANDS-1] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_dst_sign[fmt]     = fpnew_pkg::DONT_CARE;             // format disabled
      assign fmt_dst_exponent[fmt] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_dst_mantissa[fmt] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
    end
  end

  // -------------------------------------------
  // Operation selection and operand adjustment
  // -------------------------------------------
  fp_src_t [VectorSize-1:0] operands_a, operands_b;
  logic signed [1:0][SCALE_WIDTH-1:0] operands_c;
  fp_dst_t             operand_d;
  fpnew_pkg::fp_info_t [VectorSize-1:0] info_a, info_b;
  fpnew_pkg::fp_info_t [1:0] info_c;
  fpnew_pkg::fp_info_t info_d;

  always_comb begin : op_select
    // Default assignments - packing-order-agnostic
    for (int i = 0; i < VectorSize; i++) begin : gen_default_assignments
      operands_a[i] = {fmt_sign[src_fmt_q][i], fmt_exponent[src_fmt_q][i], fmt_mantissa[src_fmt_q][i]};
      operands_b[i] = {fmt_sign[src_fmt_q][i+VectorSize], fmt_exponent[src_fmt_q][i+VectorSize], fmt_mantissa[src_fmt_q][i+VectorSize]};
      info_a[i]     = info_q[src_fmt_q][i];
      info_b[i]     = info_q[src_fmt_q][i+VectorSize];
    end
    for (int i = 0; i < 2; i++) begin : gen_default_assignments_c
      operands_c[i] = signed'(operands_c_q[i]) - signed'(2**(SCALE_WIDTH-1)-1); // signed scale
      info_c[i] = '{is_normal: 1'b1, is_nan: operands_c_q[i] == 2**SCALE_WIDTH-1, is_boxed: 1'b1, default: 1'b0}; //normal, boxed value, scale can be NaN
    end
    operand_d = {fmt_dst_sign[dst_fmt_q], fmt_dst_exponent[dst_fmt_q], fmt_dst_mantissa[dst_fmt_q]};
    info_d    = info_q[dst_fmt_q][NUM_OPERANDS-1];

    // op_mod_q inverts sign of operand A, thus inverting the sign of the dot product
    for (int i = 0; i < VectorSize; i++) begin : gen_op_mod_q
      operands_a[i].sign = operands_a[i].sign ^ inp_pipe_op_mod_q[NUM_INP_REGS];
    end
  end

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
  logic [DST_WIDTH-1:0] special_result;
  fpnew_pkg::status_t   special_status;
  logic                 result_is_special;

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

    if (DstDotpFpFmtConfig[fmt]) begin : active_format
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
  assign result_is_special = fmt_result_is_special[dst_fmt_q];
  // Signalling input NaNs raise invalid flag, otherwise no flags set
  assign special_status = fmt_special_status[dst_fmt_q];
  // Assemble result according to destination format
  assign special_result = fmt_special_result[dst_fmt_q];

  // ------------------
  // Scale data path
  // ------------------
  logic signed [SCALE_WIDTH:0] scale; // +1 for addition

  assign scale = signed'(operands_c[0]) + signed'(operands_c[1]);

  // ------------------
  // Product data path
  // ------------------
  logic [VectorSize-1:0][  PRECISION_BITS-1:0] mantissa_a, mantissa_b;
  logic [VectorSize-1:0][2*PRECISION_BITS-1:0] product;  // the p*p product is 2p-bit wide
  logic signed [VectorSize-1:0][2*PRECISION_BITS  :0] product_signed;  // two's complement product

  // Add implicit bits to mantissae
  for (genvar i = 0; i < VectorSize; i++) begin : gen_mantissa
    assign mantissa_a[i] = {info_a[i].is_normal, operands_a[i].mantissa};
    assign mantissa_b[i] = {info_b[i].is_normal, operands_b[i].mantissa};
    assign product[i]    = mantissa_a[i] * mantissa_b[i];
    assign product_signed[i] = (operands_a[i].sign ^ operands_b[i].sign) ? -product[i] : product[i];
  end

  // ------------------
  // Shift data path
  // ------------------
  logic signed [VectorSize-1:0][EXP_WIDTH-1:0] exponent_product;
  logic signed [VectorSize-1:0][SOP_FIXED_WIDTH-1:0] shifted_product;
  logic [VectorSize-1:0][  5:0] shift_amount; // max shift can be 58 (28 + exp-max(30)), min shift is 0 (28 + exp-min(-28))

  // Calculate the non-biased exponent of the product
  for (genvar i = 0; i < VectorSize; i++) begin : gen_exponent_adjustment
    assign exponent_product[i] = operands_a[i].exponent + info_a[i].is_subnormal
                                + operands_b[i].exponent + info_b[i].is_subnormal 
                                - 2*signed'(fpnew_pkg::bias(src_fmt_q));
    // Right shift the significand by anchor point - exponent
    // sum of four 9-bit numbers can be at most 11 bits, for 69 bits output we need to shift by 69 - 11 = 58
    // 58-30=28 plus inherit 6 fractional bits from the multiplication -> point moves to 28+6=34
    assign shift_amount[i] = signed'(SOP_SHIFT) + signed'(exponent_product[i]);
    assign shifted_product[i] = signed'(product_signed[i]) << shift_amount[i];
  end

  // ------------------
  // Adder data path
  // ------------------
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product;

  // Sum the products
  always_comb begin : sum_products
    sum_product = '0;
    for (int i = 0; i < VectorSize; i++) begin : gen_sum_products
      sum_product += signed'(shifted_product[i]);
    end
  end

  // ---------------
  // Internal pipeline
  // ---------------
  // Pipeline output signals as non-arrays
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_q;
  logic [SCALE_WIDTH:0]              scale_q2;
  fp_dst_t                           operand_d_q2;
  fpnew_pkg::fp_info_t               info_d_q;
  fpnew_pkg::fp_format_e             dst_fmt_q2;
  fpnew_pkg::roundmode_e             rnd_mode_q;
  logic                              result_is_special_q;
  logic [DST_WIDTH-1:0]              special_result_q;
  fpnew_pkg::status_t                special_status_q;
  // Internal pipeline signals, index i holds signal after i register stages
  logic signed           [0:NUM_MID_REGS][FIXED_SUM_WIDTH-1:0]    mid_pipe_sum_product_q;
  logic                  [0:NUM_MID_REGS][SCALE_WIDTH:0]          mid_pipe_scale_q;
  fp_dst_t               [0:NUM_MID_REGS]                         mid_pipe_operand_d_q;
  fpnew_pkg::fp_info_t   [0:NUM_MID_REGS]                         mid_pipe_info_d_q;
  fpnew_pkg::fp_format_e [0:NUM_MID_REGS]                         mid_pipe_dst_fmt_q;
  fpnew_pkg::roundmode_e [0:NUM_MID_REGS]                         mid_pipe_rnd_mode_q;
  logic                  [0:NUM_MID_REGS]                         mid_pipe_res_is_spec_q;
  logic                  [0:NUM_MID_REGS][DST_WIDTH-1:0]          mid_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_MID_REGS]                         mid_pipe_spec_stat_q;
  TagType                [0:NUM_MID_REGS]                         mid_pipe_tag_q;
  logic                  [0:NUM_MID_REGS]                         mid_pipe_mask_q;
  AuxType                [0:NUM_MID_REGS]                         mid_pipe_aux_q;
  logic                  [0:NUM_MID_REGS]                         mid_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_MID_REGS] mid_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign mid_pipe_sum_product_q[0] = sum_product;
  assign mid_pipe_scale_q[0]       = scale;
  assign mid_pipe_operand_d_q[0]   = operand_d;
  assign mid_pipe_info_d_q[0]      = info_d;
  assign mid_pipe_dst_fmt_q[0]     = dst_fmt_q;
  assign mid_pipe_rnd_mode_q[0]    = inp_pipe_rnd_mode_q[NUM_INP_REGS];
  assign mid_pipe_res_is_spec_q[0] = result_is_special;
  assign mid_pipe_spec_res_q[0]    = special_result;
  assign mid_pipe_spec_stat_q[0]   = special_status;
  assign mid_pipe_tag_q[0]         = inp_pipe_tag_q[NUM_INP_REGS];
  assign mid_pipe_mask_q[0]        = inp_pipe_mask_q[NUM_INP_REGS];
  assign mid_pipe_aux_q[0]         = inp_pipe_aux_q[NUM_INP_REGS];
  assign mid_pipe_valid_q[0]       = inp_pipe_valid_q[NUM_INP_REGS];
  // Input stage: Propagate pipeline ready signal to input pipe
  assign inp_pipe_ready[NUM_INP_REGS] = mid_pipe_ready[0];

  // Generate the register stages
  for (genvar i = 0; i < NUM_MID_REGS; i++) begin : gen_inside_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign mid_pipe_ready[i] = mid_pipe_ready[i+1] | ~mid_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(mid_pipe_valid_q[i+1], mid_pipe_valid_q[i], mid_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = mid_pipe_ready[i] & mid_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(mid_pipe_sum_product_q[i+1], mid_pipe_sum_product_q[i], reg_ena, '0)
    `FFL(mid_pipe_scale_q[i+1],       mid_pipe_scale_q[i],       reg_ena, '0)
    `FFL(mid_pipe_operand_d_q[i+1],   mid_pipe_operand_d_q[i],   reg_ena, '0)
    `FFL(mid_pipe_info_d_q[i+1],      mid_pipe_info_d_q[i],      reg_ena, '0)
    `FFL(mid_pipe_dst_fmt_q[i+1],     mid_pipe_dst_fmt_q[i],     reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(mid_pipe_rnd_mode_q[i+1],    mid_pipe_rnd_mode_q[i],    reg_ena, fpnew_pkg::RNE)
    `FFL(mid_pipe_res_is_spec_q[i+1], mid_pipe_res_is_spec_q[i], reg_ena, '0)
    `FFL(mid_pipe_spec_res_q[i+1],    mid_pipe_spec_res_q[i],    reg_ena, '0)
    `FFL(mid_pipe_spec_stat_q[i+1],   mid_pipe_spec_stat_q[i],   reg_ena, '0)
    `FFL(mid_pipe_tag_q[i+1],         mid_pipe_tag_q[i],         reg_ena, TagType'('0))
    `FFL(mid_pipe_mask_q[i+1],        mid_pipe_mask_q[i],        reg_ena, '0)
    `FFL(mid_pipe_aux_q[i+1],         mid_pipe_aux_q[i],         reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign sum_product_q           = mid_pipe_sum_product_q[NUM_MID_REGS];
  assign scale_q2                = mid_pipe_scale_q[NUM_MID_REGS];
  assign operand_d_q2            = mid_pipe_operand_d_q[NUM_MID_REGS];
  assign info_d_q                = mid_pipe_info_d_q[NUM_MID_REGS];
  assign dst_fmt_q2              = mid_pipe_dst_fmt_q[NUM_MID_REGS];
  assign rnd_mode_q              = mid_pipe_rnd_mode_q[NUM_MID_REGS];
  assign result_is_special_q     = mid_pipe_res_is_spec_q[NUM_MID_REGS];
  assign special_result_q        = mid_pipe_spec_res_q[NUM_MID_REGS];
  assign special_status_q        = mid_pipe_spec_stat_q[NUM_MID_REGS];

  // -----------------------------
  // Accumulator shift data path
  // -----------------------------
  logic result_is_accumulator;
  logic accumulator_is_right_shifted;

  logic signed [9:0] accumulator_shift_amount, accumulator_right_shift_amount;
  logic signed [DST_EXP_WIDTH-1:0] exponent_d;
  logic [DST_PRECISION_BITS-1:0] mantissa_d;
  logic signed [DST_PRECISION_BITS :0] signed_mantissa_d;
  logic signed [DST_PRECISION_BITS-1:0] accumulator_remaining;
  logic signed [FIXED_SUM_WIDTH-1:0] accumulator_shifted, sum_product_accumulator;
  logic accumulator_sticky;
  logic signed [LZC_SUM_WIDTH-1:0] sum_product_accumulator_extended;

  // Zero-extend exponents into signed container - implicit width extension
  assign exponent_d = {1'b0, operand_d_q2.exponent};
  assign mantissa_d = {info_d_q.is_normal, operand_d_q2.mantissa};
  assign signed_mantissa_d = operand_d_q2.sign ? -mantissa_d : mantissa_d;

  // Calculate the shift amount for the accumulator, range=[-370,394-9b -> signed 10b]
  assign accumulator_shift_amount = signed'(ANCHOR - SUPER_DST_MAN_BITS) - signed'(scale_q2)
                                     + signed'(exponent_d + info_d_q.is_subnormal)
                                     - signed'(fpnew_pkg::bias(dst_fmt_q2));

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
        result_is_accumulator = (sum_product_q == '0) ? 1'b1 : 1'b0;
        accumulator_remaining = signed'(signed_mantissa_d) >>> (accumulator_right_shift_amount - DST_PRECISION_BITS);
        accumulator_sticky = |(signed'(signed_mantissa_d) & ((1 << (accumulator_right_shift_amount - DST_PRECISION_BITS)) - 1));
      end else begin
        accumulator_remaining = signed'(signed_mantissa_d) << (DST_PRECISION_BITS - accumulator_right_shift_amount);
        accumulator_sticky = 1'b0;
      end
    end
  end

  assign sum_product_accumulator = sum_product_q + accumulator_shifted;
  assign sum_product_accumulator_extended = {sum_product_accumulator, accumulator_remaining};

  // --------------
  // Normalization
  // --------------
  logic        [LZC_SUM_WIDTH-1:0]    sum_magnitude, sum_shifted;
  logic        [LZC_RESULT_WIDTH-1:0] leading_zero_count;     // the number of leading zeroes
  logic signed [LZC_RESULT_WIDTH:0]   leading_zero_count_sgn; // signed leading-zero count
  logic                               lzc_zeroes;             // in case only zeroes found

  logic signed [DST_EXP_WIDTH-1:0]      final_tentative_exponent;

  logic        [SHIFT_AMOUNT_WIDTH-1:0] norm_shamt; // Normalization shift amount
  logic signed [DST_EXP_WIDTH-1:0]      normalized_exponent;

  logic                                 final_sign;
  logic        [DST_PRECISION_BITS-1:0] final_mantissa;
  logic        [LZC_SUM_WIDTH-DST_PRECISION_BITS-1:0] sum_sticky_bits;
  logic                                 sticky_after_norm;
  logic signed [DST_EXP_WIDTH-1:0]      final_exponent;

  // Leading sign counter
  // If sum is negative, complement to feed into leading zero counter
  assign final_sign    = sum_product_accumulator_extended[LZC_SUM_WIDTH-1];

  always_comb begin : get_twos_complement
    if (final_sign) begin
      sum_magnitude = ~sum_product_accumulator_extended + 1;
      if (accumulator_is_right_shifted && accumulator_right_shift_amount > DST_PRECISION_BITS && signed_mantissa_d != 0) begin
        sum_magnitude = ~sum_product_accumulator_extended;
      end
    end else begin
      sum_magnitude = sum_product_accumulator_extended;
    end
  end

  // Leading sign counter
  lzc #(
    .WIDTH ( LZC_SUM_WIDTH ),
    .MODE  ( 1             ) // MODE = 1 counts leading zeroes
  ) i_lzc (
    .in_i    ( sum_magnitude      ),
    .cnt_o   ( leading_zero_count ),
    .empty_o ( lzc_zeroes         )
  );

  assign leading_zero_count_sgn = signed'({1'b0, leading_zero_count});

  // Calculate the biased exponent (excess-127 form)
  // The exponent-major is -scaled_anchor
  // exponent = 127 - scaled_anchor + (94-count-1) + increment_exponent [-195, 315 9b -> 10b signed]
  assign final_tentative_exponent = signed'(fpnew_pkg::bias(dst_fmt_q2)) - (signed'(ANCHOR)-signed'(scale_q2)) + (signed'(FIXED_SUM_WIDTH) - leading_zero_count_sgn - 1);

  // Normalization shift amount based on exponents and LZC (unsigned as only left shifts)
  always_comb begin : norm_shift_amount
    // Subnormals
    if (final_tentative_exponent > 0 && !lzc_zeroes) begin
      norm_shamt          = leading_zero_count_sgn + 1;
      normalized_exponent = final_tentative_exponent;
    end else begin // Subnormals and zero
      norm_shamt          = leading_zero_count_sgn + final_tentative_exponent;
      normalized_exponent = '0; // subnormals encoded as 0
    end
  end

  // Shift the sum to normalize it
  assign sum_shifted = sum_magnitude << norm_shamt;

  // LSB of final mantissa is the rounding bit
  assign {final_mantissa, sum_sticky_bits} = sum_shifted;
  assign final_exponent                    = normalized_exponent;
  assign sticky_after_norm                 = (|sum_sticky_bits) | accumulator_sticky;

  // ----------------------------
  // Rounding and classification
  // ----------------------------
  logic                                             pre_round_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] pre_round_abs; // absolute value of result before rounding
  logic [1:0]                                       round_sticky_bits;

  logic of_before_round, of_after_round; // overflow
  logic uf_before_round, uf_after_round; // underflow

  logic [NUM_FORMATS-1:0][SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] fmt_pre_round_abs; // per format
  logic [NUM_FORMATS-1:0][1:0]                                       fmt_round_sticky_bits;

  logic [NUM_FORMATS-1:0]                           fmt_of_after_round;
  logic [NUM_FORMATS-1:0]                           fmt_uf_after_round;

  logic                                             rounded_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] rounded_abs; // absolute value of result after rounding
  logic                                             result_zero;

  // Classification before round. RISC-V mandates checking underflow AFTER rounding
  assign of_before_round = final_exponent >= 2**(fpnew_pkg::exp_bits(dst_fmt_q2))-1; // infinity exponent is all ones
  assign uf_before_round = final_exponent == 0;               // exponent for subnormals capped to 0

  // Pack exponent and mantissa into proper rounding form
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_res_assemble
    // Set up some constants
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ALL_EXTRA_BITS = fpnew_pkg::maximum(SUPER_DST_MAN_BITS-MAN_BITS+1+DST_PRECISION_BITS+PRECISION_BITS+2+1, 1);

    logic [EXP_BITS-1:0] pre_round_exponent;
    logic [MAN_BITS-1:0] pre_round_mantissa;

    if (DstDotpFpFmtConfig[fmt]) begin : active_dst_format

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
  assign pre_round_abs      = fmt_pre_round_abs[dst_fmt_q2];

  // In case of overflow, the round and sticky bits are set for proper rounding
  assign round_sticky_bits  = fmt_round_sticky_bits[dst_fmt_q2];
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
    .rnd_mode_i                 ( rnd_mode_q               ),
    .effective_subtraction_i    ( 1'b0 ), // Effective subtraction is not implemented as RNE is used
    .abs_rounded_o              ( rounded_abs              ),
    .sign_o                     ( rounded_sign             ),
    .exact_zero_o               ( result_zero              )
  );

  logic [NUM_FORMATS-1:0][DST_WIDTH-1:0] fmt_result;

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_sign_inject
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (DstDotpFpFmtConfig[fmt]) begin : active_dst_format
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
  assign uf_after_round = fmt_uf_after_round[dst_fmt_q2];
  assign of_after_round = fmt_of_after_round[dst_fmt_q2];

  // -----------------
  // Result selection
  // -----------------
  logic [DST_WIDTH-1:0] regular_result;
  fpnew_pkg::status_t   regular_status;

  // Assemble regular result
  assign regular_result    = fmt_result[dst_fmt_q2];
  assign regular_status.NV = 1'b0; // only valid cases are handled in regular path
  assign regular_status.DZ = 1'b0; // no divisions
  assign regular_status.OF = of_before_round | of_after_round;   // rounding can introduce overflow
  assign regular_status.UF = uf_after_round & regular_status.NX; // only inexact results raise UF
  assign regular_status.NX = (| round_sticky_bits) | of_before_round | of_after_round;

  // Final results for output pipeline
  logic [DST_WIDTH-1:0] result_d;
  fpnew_pkg::status_t   status_d;

  // Select output depending on special case detection
  assign result_d = result_is_special_q ? special_result_q : (result_is_accumulator ? operand_d_q2 : regular_result);
  assign status_d = result_is_special_q ? special_status_q : (result_is_accumulator ? fpnew_pkg::status_t'(0) : regular_status);

  // ----------------
  // Output Pipeline
  // ----------------
  // Output pipeline signals, index i holds signal after i register stages
  logic               [0:NUM_OUT_REGS][DST_WIDTH-1:0] out_pipe_result_q;
  fpnew_pkg::status_t [0:NUM_OUT_REGS]                out_pipe_status_q;
  TagType             [0:NUM_OUT_REGS]                out_pipe_tag_q;
  logic               [0:NUM_OUT_REGS]                out_pipe_mask_q;
  AuxType             [0:NUM_OUT_REGS]                out_pipe_aux_q;
  logic               [0:NUM_OUT_REGS]                out_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_OUT_REGS] out_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign out_pipe_result_q[0] = result_d;
  assign out_pipe_status_q[0] = status_d;
  assign out_pipe_tag_q[0]    = mid_pipe_tag_q[NUM_MID_REGS];
  assign out_pipe_mask_q[0]   = mid_pipe_mask_q[NUM_MID_REGS];
  assign out_pipe_aux_q[0]    = mid_pipe_aux_q[NUM_MID_REGS];
  assign out_pipe_valid_q[0]  = mid_pipe_valid_q[NUM_MID_REGS];
  // Input stage: Propagate pipeline ready signal to inside pipe
  assign mid_pipe_ready[NUM_MID_REGS] = out_pipe_ready[0];
  // Generate the register stages
  for (genvar i = 0; i < NUM_OUT_REGS; i++) begin : gen_output_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign out_pipe_ready[i] = out_pipe_ready[i+1] | ~out_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(out_pipe_valid_q[i+1], out_pipe_valid_q[i], out_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = out_pipe_ready[i] & out_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(out_pipe_result_q[i+1], out_pipe_result_q[i], reg_ena, '0)
    `FFL(out_pipe_status_q[i+1], out_pipe_status_q[i], reg_ena, '0)
    `FFL(out_pipe_tag_q[i+1],    out_pipe_tag_q[i],    reg_ena, TagType'('0))
    `FFL(out_pipe_mask_q[i+1],   out_pipe_mask_q[i],   reg_ena, '0)
    `FFL(out_pipe_aux_q[i+1],    out_pipe_aux_q[i],    reg_ena, AuxType'('0))
  end
  // Output stage: Ready travels backwards from output side, driven by downstream circuitry
  assign out_pipe_ready[NUM_OUT_REGS] = out_ready_i;
  // Output stage: assign module outputs
  assign result_o        = out_pipe_result_q[NUM_OUT_REGS];
  assign status_o        = out_pipe_status_q[NUM_OUT_REGS];
  assign extension_bit_o = 1'b1; // always NaN-Box result
  assign tag_o           = out_pipe_tag_q[NUM_OUT_REGS];
  assign mask_o          = out_pipe_mask_q[NUM_OUT_REGS];
  assign aux_o           = out_pipe_aux_q[NUM_OUT_REGS];
  assign out_valid_o     = out_pipe_valid_q[NUM_OUT_REGS];
  assign busy_o          = (| {inp_pipe_valid_q, mid_pipe_valid_q, out_pipe_valid_q});
endmodule
