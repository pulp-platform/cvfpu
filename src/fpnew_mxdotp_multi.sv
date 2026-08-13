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

`include "common_cells/registers.svh"

module fpnew_mxdotp_multi
  import fpnew_mxdotp_multi_pkg::*;
#(
  // By default, all MX formats are enabled for the source and FP32 and FP16ALT are enabled for the destination.
  parameter fpnew_pkg::fmt_logic_t   FpSrcFmtConfig  = MxdotpSrcFpFmtConfig,
  parameter fpnew_pkg::ifmt_logic_t  IntSrcFmtConfig = MxdotpSrcIntFmtConfig,
  parameter fpnew_pkg::fmt_logic_t   FpDstFmtConfig  = MxdotpDstFpFmtConfig,
  parameter int unsigned             LaneWidth   = 64,
  parameter int unsigned             VectorSize  = 8,
  parameter int unsigned             NumPipeRegs = 4,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::BEFORE,
  parameter type                     TagType     = logic,
  parameter type                     AuxType     = logic,
  // Do not change the following parameters
  localparam int unsigned            NUM_OPERANDS = 2*VectorSize+1
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Input signals
  input  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_a_i,
  input  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_b_i,
  input  logic [1:0] operands_a_fp6_rem_i,
  input  logic [1:0] operands_b_fp6_rem_i,
  input  logic [1:0][SCALE_WIDTH-1:0] operands_c_i, // 2 operands
  input  logic [DST_WIDTH-1:0]        operand_d_i, // 1 operand, accumulator
  input  logic [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] is_boxed_i,
  input  fpnew_pkg::roundmode_e       rnd_mode_i,
  input  fpnew_pkg::operation_e       op_i,
  input  logic                        op_mod_i,
  input  fpnew_pkg::fp_format_e       src_fmt_i, // format of the multiplicands
  input  fpnew_pkg::int_format_e      int_fmt_i, // format of the multiplicands if they are integers
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

  if (LaneWidth != VectorSize*SRC_WIDTH) begin
    $fatal(1, "MXDOTP requires LaneWidth to be VectorSize*SRC_WIDTH, got LaneWidth=%0d and VectorSize=%0d", LaneWidth, VectorSize);
  end

  // ----------------
  // Pipeline stages
  // ----------------
  // Pipelines
  localparam int unsigned NUM_INP_REGS =
    (PipeConfig == fpnew_pkg::BEFORE)      ? NumPipeRegs :
    (PipeConfig == fpnew_pkg::DISTRIBUTED) ? ((NumPipeRegs + 1) / 3) : // Second to get distributed regs
    (PipeConfig == fpnew_pkg::INSIDE)      ? (NumPipeRegs > 3) :
                                            0;

  localparam int unsigned NUM_IM_REGS =
    (PipeConfig == fpnew_pkg::INSIDE)      ? (NumPipeRegs > 1) :
                                            0;

  localparam int unsigned NUM_MID_REGS =
    (PipeConfig == fpnew_pkg::DISTRIBUTED) ? ((NumPipeRegs + 2) / 3) : // First to get distributed regs
    (PipeConfig == fpnew_pkg::INSIDE)      ? ((NumPipeRegs > 4) ? (NumPipeRegs - 4) : ((NumPipeRegs == 1) || (NumPipeRegs == 3))) : // absorbs overflow beyond 4 stages
                                            0;

  localparam int unsigned NUM_MO_EARLY_REGS =
    (PipeConfig == fpnew_pkg::INSIDE)      ? ((NumPipeRegs == 2) || (NumPipeRegs == 4)) :
                                            0;

  localparam int unsigned NUM_MO_LATE_REGS =
    (PipeConfig == fpnew_pkg::INSIDE)      ? ((NumPipeRegs == 3) || (NumPipeRegs > 4)) :
                                            0;

  localparam int unsigned NUM_OUT_REGS =
    (PipeConfig == fpnew_pkg::AFTER)       ? NumPipeRegs :
    (PipeConfig == fpnew_pkg::DISTRIBUTED) ? (NumPipeRegs / 3) : // Last to get distributed regs
    (PipeConfig == fpnew_pkg::INSIDE)      ? (NumPipeRegs > 3) :
                                            0;

  // -----------------------------------------
  // Config-dependent derived localparams
  // -----------------------------------------
  // Computed from module parameters instead of package constants
  localparam int unsigned FP6_VECTOR_SIZE = ((FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) == 1) ?
                                            (((FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) == 1) ? cf_math_pkg::ceil_div(LaneWidth, 6) - VectorSize : cf_math_pkg::ceil_div(LaneWidth, 6)) : 0;
  localparam int unsigned FP4_VECTOR_SIZE = (FpSrcFmtConfig[fpnew_pkg::FP4] == 1) ?
                                            (((FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) == 1) ?
                                            (((FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) == 1) ? (VectorSize - FP6_VECTOR_SIZE) : VectorSize) : 2*VectorSize) : 0;

  localparam int unsigned INT_SUPER_BITS = fpnew_pkg::max_int_width(IntSrcFmtConfig);

  // FP8/INT8 Lane configuration
  localparam int unsigned PROD_BITS = fpnew_pkg::maximum(2*INT_SUPER_BITS, 2*PRECISION_BITS+1); // +1 for the sign bit in FP8 product

  localparam int unsigned FP6_SUM_WIDTH = $clog2(FP6_VECTOR_SIZE) + FP6_PROD_SHIFT_WIDTH;
  localparam int unsigned FP4_SUM_WIDTH = $clog2(FP4_VECTOR_SIZE) + FP4_PROD_SHIFT_WIDTH;

  // Accumulator Constants
  localparam int unsigned VECTOR_BITS          = $clog2(VectorSize);
  localparam int unsigned SOP_FIXED_WIDTH      = VECTOR_BITS + PROD_SHIFT_WIDTH;
  localparam int unsigned FIXED_SUM_WIDTH      = 1 + DST_PRECISION_BITS + 1 + (SOP_FIXED_WIDTH - 1); // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH        = FIXED_SUM_WIDTH + DST_PRECISION_BITS;
  localparam int unsigned LZC_RESULT_WIDTH     = $clog2(LZC_SUM_WIDTH);

  // ---------------
  // Input pipeline
  // ---------------
  // Selected pipeline output signals as non-arrays
  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_a_q;
  logic [VectorSize-1:0][SRC_WIDTH-1:0] operands_b_q;
  logic [1:0]                           operands_a_fp6_rem_q;
  logic [1:0]                           operands_b_fp6_rem_q;
  logic [1:0][SCALE_WIDTH-1:0]          operands_c_q;
  logic [DST_WIDTH-1:0]                 operand_d_q;
  fpnew_pkg::fp_format_e                src_fmt_q;
  fpnew_pkg::int_format_e               int_fmt_q;
  fpnew_pkg::fp_format_e                dst_fmt_q;

  // Input pipeline signals, index i holds signal after i register stages
  logic                   [0:NUM_INP_REGS][VectorSize-1:0][SRC_WIDTH-1:0]     inp_pipe_operands_a_q;
  logic                   [0:NUM_INP_REGS][VectorSize-1:0][SRC_WIDTH-1:0]     inp_pipe_operands_b_q;
  logic                   [0:NUM_INP_REGS][1:0]                               inp_pipe_operands_a_fp6_rem_q;
  logic                   [0:NUM_INP_REGS][1:0]                               inp_pipe_operands_b_fp6_rem_q;
  logic                   [0:NUM_INP_REGS][1:0][SCALE_WIDTH-1:0]              inp_pipe_operands_c_q;
  logic                   [0:NUM_INP_REGS][DST_WIDTH-1:0]                     inp_pipe_operand_d_q;
  logic                   [0:NUM_INP_REGS][NUM_FORMATS-1:0][NUM_OPERANDS-1:0] inp_pipe_is_boxed_q;
  fpnew_pkg::roundmode_e  [0:NUM_INP_REGS]                                    inp_pipe_rnd_mode_q;
  fpnew_pkg::operation_e  [0:NUM_INP_REGS]                                    inp_pipe_op_q;
  logic                   [0:NUM_INP_REGS]                                    inp_pipe_op_mod_q;
  fpnew_pkg::fp_format_e  [0:NUM_INP_REGS]                                    inp_pipe_src_fmt_q;
  fpnew_pkg::int_format_e [0:NUM_INP_REGS]                                    inp_pipe_int_fmt_q;
  fpnew_pkg::fp_format_e  [0:NUM_INP_REGS]                                    inp_pipe_dst_fmt_q;
  TagType                 [0:NUM_INP_REGS]                                    inp_pipe_tag_q;
  logic                   [0:NUM_INP_REGS]                                    inp_pipe_mask_q;
  AuxType                 [0:NUM_INP_REGS]                                    inp_pipe_aux_q;
  logic                   [0:NUM_INP_REGS]                                    inp_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_INP_REGS]                                                      inp_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign inp_pipe_operands_a_q[0]         = operands_a_i;
  assign inp_pipe_operands_b_q[0]         = operands_b_i;
  assign inp_pipe_operands_a_fp6_rem_q[0] = operands_a_fp6_rem_i;
  assign inp_pipe_operands_b_fp6_rem_q[0] = operands_b_fp6_rem_i;
  assign inp_pipe_operands_c_q[0]         = operands_c_i;
  assign inp_pipe_operand_d_q[0]          = operand_d_i;
  assign inp_pipe_is_boxed_q[0]           = is_boxed_i;
  assign inp_pipe_rnd_mode_q[0]           = rnd_mode_i;
  assign inp_pipe_op_q[0]                 = op_i;
  assign inp_pipe_op_mod_q[0]             = op_mod_i;
  assign inp_pipe_src_fmt_q[0]            = src_fmt_i;
  assign inp_pipe_int_fmt_q[0]            = int_fmt_i;
  assign inp_pipe_dst_fmt_q[0]            = dst_fmt_i;
  assign inp_pipe_tag_q[0]                = tag_i;
  assign inp_pipe_mask_q[0]               = mask_i;
  assign inp_pipe_aux_q[0]                = aux_i;
  assign inp_pipe_valid_q[0]              = in_valid_i;
  // Input stage: Propagate pipeline ready signal to upstream circuitry
  assign in_ready_o                       = inp_pipe_ready[0];

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
    // Enable register if pipeline ready and a valid data item is present
    assign reg_ena = inp_pipe_ready[i] & inp_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(inp_pipe_operands_a_q[i+1],         inp_pipe_operands_a_q[i],         reg_ena, '0)
    `FFL(inp_pipe_operands_b_q[i+1],         inp_pipe_operands_b_q[i],         reg_ena, '0)
    `FFL(inp_pipe_operands_a_fp6_rem_q[i+1], inp_pipe_operands_a_fp6_rem_q[i], reg_ena, '0)
    `FFL(inp_pipe_operands_b_fp6_rem_q[i+1], inp_pipe_operands_b_fp6_rem_q[i], reg_ena, '0)
    `FFL(inp_pipe_operands_c_q[i+1],         inp_pipe_operands_c_q[i],         reg_ena, '0)
    `FFL(inp_pipe_operand_d_q[i+1],          inp_pipe_operand_d_q[i],          reg_ena, '0)
    `FFL(inp_pipe_is_boxed_q[i+1],           inp_pipe_is_boxed_q[i],           reg_ena, '0)
    `FFL(inp_pipe_rnd_mode_q[i+1],           inp_pipe_rnd_mode_q[i],           reg_ena, fpnew_pkg::RNE)
    `FFL(inp_pipe_op_q[i+1],                 inp_pipe_op_q[i],                 reg_ena, fpnew_pkg::MXDOTPF)
    `FFL(inp_pipe_op_mod_q[i+1],             inp_pipe_op_mod_q[i],             reg_ena, '0)
    `FFL(inp_pipe_src_fmt_q[i+1],            inp_pipe_src_fmt_q[i],            reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_int_fmt_q[i+1],            inp_pipe_int_fmt_q[i],            reg_ena, fpnew_pkg::int_format_e'(0))
    `FFL(inp_pipe_dst_fmt_q[i+1],            inp_pipe_dst_fmt_q[i],            reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_tag_q[i+1],                inp_pipe_tag_q[i],                reg_ena, TagType'('0))
    `FFL(inp_pipe_mask_q[i+1],               inp_pipe_mask_q[i],               reg_ena, '0)
    `FFL(inp_pipe_aux_q[i+1],                inp_pipe_aux_q[i],                reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign operands_a_q         = inp_pipe_operands_a_q[NUM_INP_REGS];
  assign operands_b_q         = inp_pipe_operands_b_q[NUM_INP_REGS];
  assign operands_a_fp6_rem_q = inp_pipe_operands_a_fp6_rem_q[NUM_INP_REGS];
  assign operands_b_fp6_rem_q = inp_pipe_operands_b_fp6_rem_q[NUM_INP_REGS];
  assign operands_c_q         = inp_pipe_operands_c_q[NUM_INP_REGS];
  assign operand_d_q          = inp_pipe_operand_d_q[NUM_INP_REGS];
  assign src_fmt_q            = inp_pipe_src_fmt_q[NUM_INP_REGS];
  assign int_fmt_q            = inp_pipe_int_fmt_q[NUM_INP_REGS];
  assign dst_fmt_q            = inp_pipe_dst_fmt_q[NUM_INP_REGS];

  // ------------------
  // Operand unpacking
  // ------------------
  logic [2*VectorSize-1:0][SRC_WIDTH-1:0] operands_post_inp_pipe;
  logic [2*FP6_VECTOR_SIZE-1:0][SRC_WIDTH-1:0] fp6_operands_post_inp_pipe;
  logic [2*FP4_VECTOR_SIZE-1:0][SRC_WIDTH-1:0] fp4_operands_post_inp_pipe;

  logic [VectorSize*SRC_WIDTH-1:0] flat_operands_a_q;
  logic [VectorSize*SRC_WIDTH-1:0] flat_operands_b_q;

  always_comb begin
    fp6_operands_post_inp_pipe = '0;
    fp4_operands_post_inp_pipe = '0;
    operands_post_inp_pipe = {operands_b_q, operands_a_q};
    flat_operands_a_q = operands_a_q;
    flat_operands_b_q = operands_b_q;
    // TODO: FP6 and FP4 without FP8
    if (src_fmt_q == fpnew_pkg::FP6 || src_fmt_q == fpnew_pkg::FP6ALT) begin
      for (int i = 0; i < FP6_VECTOR_SIZE; i++) begin // Last 3 elements use FP6 datapath
        fp6_operands_post_inp_pipe[i] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_a_q[(48+i*6) +: 6]};
        fp6_operands_post_inp_pipe[i+FP6_VECTOR_SIZE] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_b_q[(48+i*6) +: 6]};
        if (i == FP6_VECTOR_SIZE-1) begin // Last element of the FP6 remainder extends to 66 bits
          fp6_operands_post_inp_pipe[i][5:4] = operands_a_fp6_rem_q;
          fp6_operands_post_inp_pipe[i+FP6_VECTOR_SIZE][5:4] = operands_b_fp6_rem_q;
        end
      end
      for (int i = 0; i < VectorSize; i++) begin // Top 8 elements use FP8 datapath
        operands_post_inp_pipe[i] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_a_q[(i*6) +: 6]};
        operands_post_inp_pipe[i+VectorSize] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_b_q[(i*6) +: 6]};
      end
    end else if (src_fmt_q == fpnew_pkg::FP4) begin
      for (int i = 0; i < VectorSize; i++) begin
        if (i < FP6_VECTOR_SIZE) begin // First 3 elements use FP6 datapath
          fp6_operands_post_inp_pipe[i] = {{(SRC_WIDTH-4){1'b0}}, operands_a_q[i][7:4]};
          fp6_operands_post_inp_pipe[i+FP6_VECTOR_SIZE] = {{(SRC_WIDTH-4){1'b0}}, operands_b_q[i][7:4]};
        end else begin // Last 5 elements use FP4 datapath, remaining elements already use FP8 datapath via operands_post_inp_pipe
          fp4_operands_post_inp_pipe[i-FP6_VECTOR_SIZE] = {{(SRC_WIDTH-4){1'b0}}, operands_a_q[i][7:4]};
          fp4_operands_post_inp_pipe[i-FP6_VECTOR_SIZE+FP4_VECTOR_SIZE] = {{(SRC_WIDTH-4){1'b0}}, operands_b_q[i][7:4]};
        end
      end
    end
  end

  // -----------------
  // Input processing
  // -----------------
  logic src_is_int; // if 0, it's a float

  assign src_is_int = (inp_pipe_op_q[NUM_INP_REGS] == fpnew_pkg::MXDOTPI);

  fp_src_t [VectorSize-1:0] operands_a, operands_b;
  logic signed [1:0][SCALE_WIDTH-1:0] operands_c;
  fp_dst_t             operand_d;
  fpnew_pkg::fp_info_t [VectorSize-1:0] info_a, info_b;
  fpnew_pkg::fp_info_t [1:0] info_c;
  fpnew_pkg::fp_info_t info_d;

  fp6_src_t [FP6_VECTOR_SIZE-1:0] fp6_operands_a, fp6_operands_b;
  fpnew_pkg::fp_info_t [FP6_VECTOR_SIZE-1:0] fp6_info_a, fp6_info_b;

  fp4_src_t [FP4_VECTOR_SIZE-1:0] fp4_operands_a, fp4_operands_b;
  fpnew_pkg::fp_info_t [FP4_VECTOR_SIZE-1:0] fp4_info_a, fp4_info_b;

  fpnew_mxdotp_classifier #(
    .FpSrcFmtConfig ( FpSrcFmtConfig  ),
    .FpDstFmtConfig ( FpDstFmtConfig  ),
    .VectorSize     ( VectorSize      ),
    .FP6VectorSize  ( FP6_VECTOR_SIZE ),
    .FP4VectorSize  ( FP4_VECTOR_SIZE ),
    .NumInpRegs     ( NUM_INP_REGS    )
  ) i_classifier (
    .operands_post_inp_pipe(operands_post_inp_pipe),
    .fp6_operands_post_inp_pipe(fp6_operands_post_inp_pipe),
    .fp4_operands_post_inp_pipe(fp4_operands_post_inp_pipe),
    .operands_c_in(operands_c_q),
    .operand_d_in(operand_d_q),
    .inp_pipe_is_boxed(inp_pipe_is_boxed_q),
    .src_fmt(src_fmt_q),
    .src_is_int(src_is_int),
    .dst_fmt(dst_fmt_q),
    .inp_pipe_op_mod(inp_pipe_op_mod_q),
    .info_a(info_a),
    .fp6_info_a(fp6_info_a),
    .fp4_info_a(fp4_info_a),
    .info_b(info_b),
    .fp6_info_b(fp6_info_b),
    .fp4_info_b(fp4_info_b),
    .info_c(info_c),
    .info_d(info_d),
    .operands_a(operands_a),
    .fp6_operands_a(fp6_operands_a),
    .fp4_operands_a(fp4_operands_a),
    .operands_b(operands_b),
    .fp6_operands_b(fp6_operands_b),
    .fp4_operands_b(fp4_operands_b),
    .operands_c(operands_c),
    .operand_d(operand_d)
  );

  // ---------------------
  // Special case handling
  // ---------------------
  logic [DST_WIDTH-1:0] special_result;
  fpnew_pkg::status_t   special_status;
  logic                 result_is_special;

  // Inf and NaN do not exists in FP6 and FP4 formats
  if (FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) begin : special_case_handling
    fpnew_mxdotp_special_cases #(
      .FpDstFmtConfig ( FpDstFmtConfig ),
      .VectorSize     ( VectorSize     )
    ) i_special_cases (
      .operands_a(operands_a),
      .operands_b(operands_b),
      .operands_c(operands_c),
      .operand_d(operand_d),
      .info_a(info_a),
      .info_b(info_b),
      .info_c(info_c),
      .info_d(info_d),
      .dst_fmt(dst_fmt_q),
      .special_result(special_result),
      .special_status(special_status),
      .result_is_special(result_is_special)
    );
  end else begin : no_special_case_handling
    assign special_result = '0;
    assign special_status = fpnew_pkg::status_t'(0);
    assign result_is_special = 1'b0;
  end

  // ------------------
  // Scale data path
  // ------------------
  logic signed [SCALE_WIDTH:0] scale; // +1 for addition

  fpnew_mxdotp_scale_adder #(
  ) i_scale_adder (
    .operands_c(operands_c),
    .scale(scale)
  );

  // ------------------
  // Product data path
  // ------------------
  logic signed [VectorSize-1:0][PROD_BITS-1:0] product_signed;  // two's complement product, already signed
  logic signed [FP6_VECTOR_SIZE-1:0][2*FP6_PREC_BITS:0] fp6_product_signed;  // two's complement product, +1 for sign bit
  logic signed [FP4_VECTOR_SIZE-1:0][2*FP4_PREC_BITS:0] fp4_product_signed;  // two's complement product, +1 for sign bit

  if (IntSrcFmtConfig[fpnew_pkg::INT8]) begin : int8_multiplier
    fpnew_mxdotp_signed_vector_multiplier #(
      .SrcType(fp_src_t),
      .LocalVectorSize(VectorSize),
      .PrecisionBits(INT_SUPER_BITS)
    ) i_vector_multiplier_int8 (
      .operands_a(operands_a),
      .operands_b(operands_b),
      .src_fmt(src_fmt_q),
      .int_fmt(int_fmt_q),
      .src_is_int(src_is_int),
      .info_a(info_a),
      .info_b(info_b),
      .product_signed(product_signed)
    );
  end else if (FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) begin : fp8_multiplier
    fpnew_mxdotp_vector_multiplier #(
      .SrcType(fp_src_t),
      .LocalVectorSize(VectorSize),
      .PrecisionBits(PRECISION_BITS)
    ) i_vector_multiplier_fp8 (
      .operands_a(operands_a),
      .operands_b(operands_b),
      .info_a(info_a),
      .info_b(info_b),
      .product_signed(product_signed)
    );
  end else begin : no_fp8_multiplier
    assign product_signed = '0;
  end

  if (FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) begin : fp6_multiplier
    fpnew_mxdotp_vector_multiplier #(
      .SrcType(fp6_src_t),
      .LocalVectorSize(FP6_VECTOR_SIZE),
      .PrecisionBits(FP6_PREC_BITS)
    ) i_vector_multiplier_fp6 (
      .operands_a(fp6_operands_a),
      .operands_b(fp6_operands_b),
      .info_a(fp6_info_a),
      .info_b(fp6_info_b),
      .product_signed(fp6_product_signed)
    );
  end else begin : no_fp6_multiplier
    assign fp6_product_signed = '0;
  end
  if (FpSrcFmtConfig[fpnew_pkg::FP4]) begin : fp4_multiplier
    fpnew_mxdotp_vector_multiplier #(
      .SrcType(fp4_src_t),
      .LocalVectorSize(FP4_VECTOR_SIZE),
      .PrecisionBits(FP4_PREC_BITS)
    ) i_vector_multiplier_fp4 (
      .operands_a(fp4_operands_a),
      .operands_b(fp4_operands_b),
      .info_a(fp4_info_a),
      .info_b(fp4_info_b),
      .product_signed(fp4_product_signed)
    );
  end else begin : no_fp4_multiplier
    assign fp4_product_signed = '0;
  end

  // ------------------
  // Shift data path
  // ------------------
  logic signed [VectorSize-1:0][PROD_SHIFT_WIDTH-1:0] shifted_product;
  logic signed [FP6_VECTOR_SIZE-1:0][FP6_PROD_SHIFT_WIDTH-1:0] fp6_shifted_product;
  logic signed [FP4_VECTOR_SIZE-1:0][FP4_PROD_SHIFT_WIDTH-1:0] fp4_shifted_product;

  if (FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) begin : fp8_product_shifter
    fpnew_mxdotp_product_shifter #(
      .SrcType(fp_src_t),
      .LocalVectorSize(VectorSize),
      .SrcFmt(fpnew_pkg::FP8), // TODO: For now, we assume that FP8 and FP8ALT are always enabled together
      .ProductBits(PROD_BITS),
      .ExpWidth(EXP_WIDTH),
      .OutputWidth(PROD_SHIFT_WIDTH)
    ) i_product_shifter_fp8 (
      .operands_a(operands_a),
      .operands_b(operands_b),
      .info_a(info_a),
      .info_b(info_b),
      .product_signed(product_signed),
      .src_fmt(src_fmt_q),
      .int_fmt(int_fmt_q),
      .src_is_int(src_is_int),
      .shifted_product(shifted_product)
    );
  end else begin : no_fp8_product_shifter
    assign shifted_product = '0;
  end

  if (FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) begin : fp6_product_shifter
    fpnew_mxdotp_product_shifter #(
      .SrcType(fp6_src_t),
      .LocalVectorSize(FP6_VECTOR_SIZE),
      .SrcFmt(fpnew_pkg::FP6), // TODO: For now, we assume that FP6 and FP6ALT are always enabled together
      .ProductBits(2*FP6_PREC_BITS+1),
      .ExpWidth(5),
      .OutputWidth(FP6_PROD_SHIFT_WIDTH)
    ) i_product_shifter_fp6 (
      .operands_a(fp6_operands_a),
      .operands_b(fp6_operands_b),
      .info_a(fp6_info_a),
      .info_b(fp6_info_b),
      .product_signed(fp6_product_signed),
      .src_fmt(src_fmt_q),
      .int_fmt(int_fmt_q),
      .src_is_int(src_is_int),
      .shifted_product(fp6_shifted_product)
    );
  end else begin : no_fp6_product_shifter
    assign fp6_shifted_product = '0;
  end
  if (FpSrcFmtConfig[fpnew_pkg::FP4]) begin : fp4_product_shifter
    fpnew_mxdotp_product_shifter #(
      .SrcType(fp4_src_t),
      .LocalVectorSize(FP4_VECTOR_SIZE),
      .SrcFmt(fpnew_pkg::FP4),
      .ProductBits(2*FP4_PREC_BITS+1),
      .ExpWidth(3),
      .OutputWidth(FP4_PROD_SHIFT_WIDTH)
    ) i_product_shifter_fp4 (
      .operands_a(fp4_operands_a),
      .operands_b(fp4_operands_b),
      .info_a(fp4_info_a),
      .info_b(fp4_info_b),
      .product_signed(fp4_product_signed),
      .src_fmt(src_fmt_q),
      .int_fmt(int_fmt_q),
      .src_is_int(src_is_int),
      .shifted_product(fp4_shifted_product)
    );
  end else begin : no_fp4_product_shifter
    assign fp4_shifted_product = '0;
  end

  // --------------------
  // INP to MID pipeline
  // --------------------
  // Selected pipeline output signals as non-arrays
  logic signed [VectorSize-1:0][PROD_SHIFT_WIDTH-1:0]          shifted_product_q;
  logic signed [FP6_VECTOR_SIZE-1:0][FP6_PROD_SHIFT_WIDTH-1:0] fp6_shifted_product_q;
  logic signed [FP4_VECTOR_SIZE-1:0][FP4_PROD_SHIFT_WIDTH-1:0] fp4_shifted_product_q;

  // Inp-mid pipeline signals, index i holds signal after i register stages
  logic signed           [0:NUM_IM_REGS][VectorSize-1:0][PROD_SHIFT_WIDTH-1:0]          inp_mid_pipe_shifted_product_q;
  logic signed           [0:NUM_IM_REGS][FP6_VECTOR_SIZE-1:0][FP6_PROD_SHIFT_WIDTH-1:0] inp_mid_pipe_fp6_shifted_product_q;
  logic signed           [0:NUM_IM_REGS][FP4_VECTOR_SIZE-1:0][FP4_PROD_SHIFT_WIDTH-1:0] inp_mid_pipe_fp4_shifted_product_q;
  fpnew_pkg::fp_format_e [0:NUM_IM_REGS]                                                inp_mid_pipe_dst_fmt_q;
  logic                  [0:NUM_IM_REGS][SCALE_WIDTH:0]                                 inp_mid_pipe_scale_q;
  fp_dst_t               [0:NUM_IM_REGS]                                                inp_mid_pipe_operand_d_q;
  fpnew_pkg::fp_info_t   [0:NUM_IM_REGS]                                                inp_mid_pipe_info_d_q;
  fpnew_pkg::roundmode_e [0:NUM_IM_REGS]                                                inp_mid_pipe_rnd_mode_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_res_is_spec_q;
  logic                  [0:NUM_IM_REGS][DST_WIDTH-1:0]                                 inp_mid_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_IM_REGS]                                                inp_mid_pipe_spec_stat_q;
  TagType                [0:NUM_IM_REGS]                                                inp_mid_pipe_tag_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_mask_q;
  AuxType                [0:NUM_IM_REGS]                                                inp_mid_pipe_aux_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_IM_REGS]                                                                 inp_mid_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign inp_mid_pipe_shifted_product_q[0]     = shifted_product;
  assign inp_mid_pipe_fp6_shifted_product_q[0] = fp6_shifted_product;
  assign inp_mid_pipe_fp4_shifted_product_q[0] = fp4_shifted_product;
  assign inp_mid_pipe_dst_fmt_q[0]             = inp_pipe_dst_fmt_q[NUM_INP_REGS];
  assign inp_mid_pipe_scale_q[0]               = scale;
  assign inp_mid_pipe_operand_d_q[0]           = operand_d;
  assign inp_mid_pipe_info_d_q[0]              = info_d;
  assign inp_mid_pipe_rnd_mode_q[0]            = inp_pipe_rnd_mode_q[NUM_INP_REGS];
  assign inp_mid_pipe_res_is_spec_q[0]         = result_is_special;
  assign inp_mid_pipe_spec_res_q[0]            = special_result;
  assign inp_mid_pipe_spec_stat_q[0]           = special_status;
  assign inp_mid_pipe_tag_q[0]                 = inp_pipe_tag_q[NUM_INP_REGS];
  assign inp_mid_pipe_mask_q[0]                = inp_pipe_mask_q[NUM_INP_REGS];
  assign inp_mid_pipe_aux_q[0]                 = inp_pipe_aux_q[NUM_INP_REGS];
  assign inp_mid_pipe_valid_q[0]               = inp_pipe_valid_q[NUM_INP_REGS];
  // Input stage: Propagate pipeline ready signal to input pipe
  assign inp_pipe_ready[NUM_INP_REGS]          = inp_mid_pipe_ready[0];

  // Generate the register stages
  for (genvar i = 0; i < NUM_IM_REGS; i++) begin : gen_inp_mid_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign inp_mid_pipe_ready[i] = inp_mid_pipe_ready[i+1] | ~inp_mid_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(inp_mid_pipe_valid_q[i+1], inp_mid_pipe_valid_q[i], inp_mid_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipeline ready and a valid data item is present
    assign reg_ena = inp_mid_pipe_ready[i] & inp_mid_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(inp_mid_pipe_shifted_product_q[i+1],     inp_mid_pipe_shifted_product_q[i],     reg_ena, '0)
    `FFL(inp_mid_pipe_fp6_shifted_product_q[i+1], inp_mid_pipe_fp6_shifted_product_q[i], reg_ena, '0)
    `FFL(inp_mid_pipe_fp4_shifted_product_q[i+1], inp_mid_pipe_fp4_shifted_product_q[i], reg_ena, '0)
    `FFL(inp_mid_pipe_dst_fmt_q[i+1],             inp_mid_pipe_dst_fmt_q[i],             reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_mid_pipe_scale_q[i+1],               inp_mid_pipe_scale_q[i],               reg_ena, '0)
    `FFL(inp_mid_pipe_operand_d_q[i+1],           inp_mid_pipe_operand_d_q[i],           reg_ena, '0)
    `FFL(inp_mid_pipe_info_d_q[i+1],              inp_mid_pipe_info_d_q[i],              reg_ena, '0)
    `FFL(inp_mid_pipe_rnd_mode_q[i+1],            inp_mid_pipe_rnd_mode_q[i],            reg_ena, fpnew_pkg::RNE)
    `FFL(inp_mid_pipe_res_is_spec_q[i+1],         inp_mid_pipe_res_is_spec_q[i],         reg_ena, '0)
    `FFL(inp_mid_pipe_spec_res_q[i+1],            inp_mid_pipe_spec_res_q[i],            reg_ena, '0)
    `FFL(inp_mid_pipe_spec_stat_q[i+1],           inp_mid_pipe_spec_stat_q[i],           reg_ena, '0)
    `FFL(inp_mid_pipe_tag_q[i+1],                 inp_mid_pipe_tag_q[i],                 reg_ena, TagType'('0))
    `FFL(inp_mid_pipe_mask_q[i+1],                inp_mid_pipe_mask_q[i],                reg_ena, '0)
    `FFL(inp_mid_pipe_aux_q[i+1],                 inp_mid_pipe_aux_q[i],                 reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign shifted_product_q     = inp_mid_pipe_shifted_product_q[NUM_IM_REGS];
  assign fp6_shifted_product_q = inp_mid_pipe_fp6_shifted_product_q[NUM_IM_REGS];
  assign fp4_shifted_product_q = inp_mid_pipe_fp4_shifted_product_q[NUM_IM_REGS];

  // ------------------
  // Adder data path
  // ------------------
  logic signed [SOP_FIXED_WIDTH-1:0] sum_product_fp8;
  logic signed [FP6_SUM_WIDTH-1:0]   sum_product_fp6;
  logic signed [FP4_SUM_WIDTH-1:0]   sum_product_fp4;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product;

  if (FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT] || IntSrcFmtConfig[fpnew_pkg::INT8]) begin : fp8_adder_tree
    fpnew_mxdotp_adder_tree #(
      .LocalVectorSize(VectorSize),
      .InputWidth(PROD_SHIFT_WIDTH),
      .OutputWidth(SOP_FIXED_WIDTH)
    ) i_adder_tree_fp8 (
      .shifted_product(shifted_product_q),
      .sum_product(sum_product_fp8)
    );
  end else begin : no_fp8_adder_tree
    assign sum_product_fp8 = '0;
  end

  if (FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) begin : fp6_adder_tree
    fpnew_mxdotp_adder_tree #(
      .LocalVectorSize(FP6_VECTOR_SIZE),
      .InputWidth(FP6_PROD_SHIFT_WIDTH),
      .OutputWidth(FP6_SUM_WIDTH)
    ) i_adder_tree_fp6 (
      .shifted_product(fp6_shifted_product_q),
      .sum_product(sum_product_fp6)
    );
  end else begin : no_fp6_adder_tree
    assign sum_product_fp6 = '0;
  end
  if (FpSrcFmtConfig[fpnew_pkg::FP4]) begin : fp4_adder_tree
    fpnew_mxdotp_adder_tree #(
      .LocalVectorSize(FP4_VECTOR_SIZE),
      .InputWidth(FP4_PROD_SHIFT_WIDTH),
      .OutputWidth(FP4_SUM_WIDTH)
    ) i_adder_tree_fp4 (
      .shifted_product(fp4_shifted_product_q),
      .sum_product(sum_product_fp4)
    );
  end else begin : no_fp4_adder_tree
    assign sum_product_fp4 = '0;
  end

  // Unified format adder: handles FP8 + FP6 + FP4 (FP6/FP4 are zero when disabled)
  fpnew_mxdotp_format_adder #(
    .SoPFixedWidth ( SOP_FIXED_WIDTH ),
    .Fp6SumWidth ( FP6_SUM_WIDTH ),
    .Fp4SumWidth ( FP4_SUM_WIDTH )
  ) i_format_adder (
    .sum_product_fp8(sum_product_fp8),
    .sum_product_fp6(sum_product_fp6),
    .sum_product_fp4(sum_product_fp4),
    .sum_product(sum_product)
  );

  // ---------------
  // Internal pipeline
  // ---------------
  // Pipeline output signals as non-arrays
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_q;
  logic [SCALE_WIDTH:0]              scale_q;
  fp_dst_t                           operand_d_q2;
  fpnew_pkg::fp_info_t               info_d_q;
  fpnew_pkg::fp_format_e             dst_fmt_q2;

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
  assign mid_pipe_sum_product_q[0]       = sum_product;
  assign mid_pipe_scale_q[0]             = inp_mid_pipe_scale_q[NUM_IM_REGS];
  assign mid_pipe_operand_d_q[0]         = inp_mid_pipe_operand_d_q[NUM_IM_REGS];
  assign mid_pipe_info_d_q[0]            = inp_mid_pipe_info_d_q[NUM_IM_REGS];
  assign mid_pipe_dst_fmt_q[0]           = inp_mid_pipe_dst_fmt_q[NUM_IM_REGS];
  assign mid_pipe_rnd_mode_q[0]          = inp_mid_pipe_rnd_mode_q[NUM_IM_REGS];
  assign mid_pipe_res_is_spec_q[0]       = inp_mid_pipe_res_is_spec_q[NUM_IM_REGS];
  assign mid_pipe_spec_res_q[0]          = inp_mid_pipe_spec_res_q[NUM_IM_REGS];
  assign mid_pipe_spec_stat_q[0]         = inp_mid_pipe_spec_stat_q[NUM_IM_REGS];
  assign mid_pipe_tag_q[0]               = inp_mid_pipe_tag_q[NUM_IM_REGS];
  assign mid_pipe_mask_q[0]              = inp_mid_pipe_mask_q[NUM_IM_REGS];
  assign mid_pipe_aux_q[0]               = inp_mid_pipe_aux_q[NUM_IM_REGS];
  assign mid_pipe_valid_q[0]             = inp_mid_pipe_valid_q[NUM_IM_REGS];
  // Input stage: Propagate pipeline ready signal to inp-mid pipe
  assign inp_mid_pipe_ready[NUM_IM_REGS] = mid_pipe_ready[0];

  // Generate the register stages
  for (genvar i = 0; i < NUM_MID_REGS; i++) begin : gen_mid_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign mid_pipe_ready[i] = mid_pipe_ready[i+1] | ~mid_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(mid_pipe_valid_q[i+1], mid_pipe_valid_q[i], mid_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipeline ready and a valid data item is present
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
  assign sum_product_q       = mid_pipe_sum_product_q[NUM_MID_REGS];
  assign scale_q             = mid_pipe_scale_q[NUM_MID_REGS];
  assign operand_d_q2        = mid_pipe_operand_d_q[NUM_MID_REGS];
  assign info_d_q            = mid_pipe_info_d_q[NUM_MID_REGS];
  assign dst_fmt_q2          = mid_pipe_dst_fmt_q[NUM_MID_REGS];

  // -----------------------------
  // Accumulator shift data path
  // -----------------------------
  logic result_is_accumulator;
  logic accumulator_is_right_shifted;

  logic signed [9:0] accumulator_right_shift_amount;
  logic signed [FIXED_SUM_WIDTH-1:0] accumulator_shifted;
  logic signed [DST_PRECISION_BITS :0] signed_mantissa_d;
  logic accumulator_sticky;
  logic signed [DST_PRECISION_BITS-1:0] accumulator_remaining;

  fpnew_mxdotp_accumulator_shift #(
    .SoPFixedWidth  ( SOP_FIXED_WIDTH )
  ) i_accumulator_shift (
    .sum_product(sum_product_q),
    .scale(scale_q),
    .operand_d(operand_d_q2),
    .info_d(info_d_q),
    .dst_fmt(dst_fmt_q2),
    .accumulator_is_right_shifted(accumulator_is_right_shifted),
    .accumulator_right_shift_amount(accumulator_right_shift_amount),
    .accumulator_shifted(accumulator_shifted),
    .result_is_accumulator(result_is_accumulator),
    .accumulator_sticky(accumulator_sticky),
    .signed_mantissa_d(signed_mantissa_d),
    .accumulator_remaining(accumulator_remaining)
  );

  // -----------------
  // Accumulator + SoP
  // -----------------
  logic signed [LZC_SUM_WIDTH-1:0] sum_product_accumulator_extended;

  fpnew_mxdotp_add_accumulator_sop #(
    .SoPFixedWidth  ( SOP_FIXED_WIDTH )
  ) i_add_accumulator_sop (
    .sum_product(sum_product_q),
    .accumulator_shifted(accumulator_shifted),
    .accumulator_remaining(accumulator_remaining),
    .sum_product_accumulator_extended(sum_product_accumulator_extended)
  );

  // ----------------------------------
  // Normalization 1: Two's complement
  // ----------------------------------
  logic final_sign;
  logic [LZC_SUM_WIDTH-1:0] sum_magnitude;

  fpnew_mxdotp_twos_compl #(
    .SoPFixedWidth  ( SOP_FIXED_WIDTH )
  ) i_twos_compl (
    .sum_product_accumulator_extended ( sum_product_accumulator_extended ),
    .signed_mantissa_d                ( signed_mantissa_d                ),
    .accumulator_is_right_shifted     ( accumulator_is_right_shifted     ),
    .accumulator_right_shift_amount   ( accumulator_right_shift_amount   ),
    .accumulator_sticky               ( accumulator_sticky               ),
    .final_sign                       ( final_sign                       ),
    .sum_magnitude                    ( sum_magnitude                    )
  );

  // -------------------------
  // MID to OUT EARLY pipeline
  // -------------------------
  // Pipeline output signals as non-arrays
  logic [LZC_SUM_WIDTH-1:0] sum_magnitude_q;
  logic [SCALE_WIDTH:0]     scale_q2;

  // MO-early pipeline signals, index i holds signal after i register stages
  logic                  [0:NUM_MO_EARLY_REGS][LZC_SUM_WIDTH-1:0]   mo_early_pipe_sum_magnitude_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_final_sign_q;
  logic                  [0:NUM_MO_EARLY_REGS][SCALE_WIDTH:0]       mo_early_pipe_scale_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_acc_sticky_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_res_is_acc_q;
  logic                  [0:NUM_MO_EARLY_REGS][FIXED_SUM_WIDTH-1:0] mo_early_pipe_sum_product_q;
  fp_dst_t               [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_operand_d_q;
  fpnew_pkg::fp_format_e [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_dst_fmt_q;
  fpnew_pkg::roundmode_e [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_rnd_mode_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_res_is_spec_q;
  logic                  [0:NUM_MO_EARLY_REGS][DST_WIDTH-1:0]       mo_early_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_spec_stat_q;
  TagType                [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_tag_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_mask_q;
  AuxType                [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_aux_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_MO_EARLY_REGS]                                       mo_early_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign mo_early_pipe_sum_magnitude_q[0] = sum_magnitude;
  assign mo_early_pipe_final_sign_q[0]    = final_sign;
  assign mo_early_pipe_scale_q[0]         = scale_q;
  assign mo_early_pipe_acc_sticky_q[0]    = accumulator_sticky;
  assign mo_early_pipe_res_is_acc_q[0]    = result_is_accumulator;
  assign mo_early_pipe_sum_product_q[0]   = sum_product_q;
  assign mo_early_pipe_operand_d_q[0]     = operand_d_q2;
  assign mo_early_pipe_dst_fmt_q[0]       = dst_fmt_q2;
  assign mo_early_pipe_rnd_mode_q[0]      = mid_pipe_rnd_mode_q[NUM_MID_REGS];
  assign mo_early_pipe_res_is_spec_q[0]   = mid_pipe_res_is_spec_q[NUM_MID_REGS];
  assign mo_early_pipe_spec_res_q[0]      = mid_pipe_spec_res_q[NUM_MID_REGS];
  assign mo_early_pipe_spec_stat_q[0]     = mid_pipe_spec_stat_q[NUM_MID_REGS];
  assign mo_early_pipe_tag_q[0]           = mid_pipe_tag_q[NUM_MID_REGS];
  assign mo_early_pipe_mask_q[0]          = mid_pipe_mask_q[NUM_MID_REGS];
  assign mo_early_pipe_aux_q[0]           = mid_pipe_aux_q[NUM_MID_REGS];
  assign mo_early_pipe_valid_q[0]         = mid_pipe_valid_q[NUM_MID_REGS];
  // Input stage: Propagate pipeline ready signal to mid pipe
  assign mid_pipe_ready[NUM_MID_REGS]     = mo_early_pipe_ready[0];

  // Generate the register stages
  for (genvar i = 0; i < NUM_MO_EARLY_REGS; i++) begin : gen_mid_out_early_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign mo_early_pipe_ready[i] = mo_early_pipe_ready[i+1] | ~mo_early_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(mo_early_pipe_valid_q[i+1], mo_early_pipe_valid_q[i], mo_early_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipeline ready and a valid data item is present
    assign reg_ena = mo_early_pipe_ready[i] & mo_early_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(mo_early_pipe_sum_magnitude_q[i+1], mo_early_pipe_sum_magnitude_q[i], reg_ena, '0)
    `FFL(mo_early_pipe_final_sign_q[i+1],    mo_early_pipe_final_sign_q[i],    reg_ena, '0)
    `FFL(mo_early_pipe_scale_q[i+1],         mo_early_pipe_scale_q[i],         reg_ena, '0)
    `FFL(mo_early_pipe_acc_sticky_q[i+1],    mo_early_pipe_acc_sticky_q[i],    reg_ena, '0)
    `FFL(mo_early_pipe_res_is_acc_q[i+1],    mo_early_pipe_res_is_acc_q[i],    reg_ena, '0)
    `FFL(mo_early_pipe_sum_product_q[i+1],   mo_early_pipe_sum_product_q[i],   reg_ena, '0)
    `FFL(mo_early_pipe_operand_d_q[i+1],     mo_early_pipe_operand_d_q[i],     reg_ena, '0)
    `FFL(mo_early_pipe_dst_fmt_q[i+1],       mo_early_pipe_dst_fmt_q[i],       reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(mo_early_pipe_rnd_mode_q[i+1],      mo_early_pipe_rnd_mode_q[i],      reg_ena, fpnew_pkg::RNE)
    `FFL(mo_early_pipe_res_is_spec_q[i+1],   mo_early_pipe_res_is_spec_q[i],   reg_ena, '0)
    `FFL(mo_early_pipe_spec_res_q[i+1],      mo_early_pipe_spec_res_q[i],      reg_ena, '0)
    `FFL(mo_early_pipe_spec_stat_q[i+1],     mo_early_pipe_spec_stat_q[i],     reg_ena, '0)
    `FFL(mo_early_pipe_tag_q[i+1],           mo_early_pipe_tag_q[i],           reg_ena, TagType'('0))
    `FFL(mo_early_pipe_mask_q[i+1],          mo_early_pipe_mask_q[i],          reg_ena, '0)
    `FFL(mo_early_pipe_aux_q[i+1],           mo_early_pipe_aux_q[i],           reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign sum_magnitude_q = mo_early_pipe_sum_magnitude_q[NUM_MO_EARLY_REGS];
  assign scale_q2        = mo_early_pipe_scale_q[NUM_MO_EARLY_REGS];

  // ---------------------
  // Normalization 2: LZC
  // ---------------------
  logic signed [LZC_RESULT_WIDTH:0] leading_zero_count_sgn;
  logic                             lzc_zeroes;

  fpnew_mxdotp_norm_lzc #(
    .SoPFixedWidth  ( SOP_FIXED_WIDTH )
  ) i_norm_lzc (
    .sum_magnitude         ( sum_magnitude_q        ),
    .leading_zero_count_sgn( leading_zero_count_sgn ),
    .lzc_zeroes            ( lzc_zeroes             )
  );

  // -------------------------
  // MID to OUT LATE pipeline
  // -------------------------
  // Pipeline output signals as non-arrays
  logic [LZC_SUM_WIDTH-1:0]         sum_magnitude_q2;
  logic signed [LZC_RESULT_WIDTH:0] leading_zero_count_sgn_q;
  logic                             lzc_zeroes_q;
  logic [SCALE_WIDTH:0]             scale_q3;
  logic                             final_sign_q;
  logic                             accumulator_sticky_q;
  logic                             result_is_accumulator_q;
  logic [FIXED_SUM_WIDTH-1:0]       sum_product_q2;
  fp_dst_t                          operand_d_q3;
  fpnew_pkg::fp_format_e            dst_fmt_q3;
  fpnew_pkg::roundmode_e            rnd_mode_q;
  logic                             result_is_special_q;
  logic [DST_WIDTH-1:0]             special_result_q;
  fpnew_pkg::status_t               special_status_q;

  // MO-late pipeline signals, index i holds signal after i register stages
  logic                  [0:NUM_MO_LATE_REGS][LZC_SUM_WIDTH-1:0]      mo_late_pipe_sum_magnitude_q;
  logic signed           [0:NUM_MO_LATE_REGS][LZC_RESULT_WIDTH:0]     mo_late_pipe_lzc_count_sgn_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_lzc_zeroes_q;
  logic                  [0:NUM_MO_LATE_REGS][SCALE_WIDTH:0]          mo_late_pipe_scale_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_final_sign_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_acc_sticky_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_res_is_acc_q;
  logic                  [0:NUM_MO_LATE_REGS][FIXED_SUM_WIDTH-1:0]    mo_late_pipe_sum_product_q;
  fp_dst_t               [0:NUM_MO_LATE_REGS]                         mo_late_pipe_operand_d_q;
  fpnew_pkg::fp_format_e [0:NUM_MO_LATE_REGS]                         mo_late_pipe_dst_fmt_q;
  fpnew_pkg::roundmode_e [0:NUM_MO_LATE_REGS]                         mo_late_pipe_rnd_mode_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_res_is_spec_q;
  logic                  [0:NUM_MO_LATE_REGS][DST_WIDTH-1:0]          mo_late_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_MO_LATE_REGS]                         mo_late_pipe_spec_stat_q;
  TagType                [0:NUM_MO_LATE_REGS]                         mo_late_pipe_tag_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_mask_q;
  AuxType                [0:NUM_MO_LATE_REGS]                         mo_late_pipe_aux_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_MO_LATE_REGS]                                          mo_late_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign mo_late_pipe_sum_magnitude_q[0]        = sum_magnitude_q;
  assign mo_late_pipe_lzc_count_sgn_q[0]        = leading_zero_count_sgn;
  assign mo_late_pipe_lzc_zeroes_q[0]           = lzc_zeroes;
  assign mo_late_pipe_scale_q[0]                = scale_q2;
  assign mo_late_pipe_final_sign_q[0]           = mo_early_pipe_final_sign_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_acc_sticky_q[0]           = mo_early_pipe_acc_sticky_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_res_is_acc_q[0]           = mo_early_pipe_res_is_acc_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_sum_product_q[0]          = mo_early_pipe_sum_product_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_operand_d_q[0]            = mo_early_pipe_operand_d_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_dst_fmt_q[0]              = mo_early_pipe_dst_fmt_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_rnd_mode_q[0]             = mo_early_pipe_rnd_mode_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_res_is_spec_q[0]          = mo_early_pipe_res_is_spec_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_spec_res_q[0]             = mo_early_pipe_spec_res_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_spec_stat_q[0]            = mo_early_pipe_spec_stat_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_tag_q[0]                  = mo_early_pipe_tag_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_mask_q[0]                 = mo_early_pipe_mask_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_aux_q[0]                  = mo_early_pipe_aux_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_valid_q[0]                = mo_early_pipe_valid_q[NUM_MO_EARLY_REGS];
  // Input stage: Propagate pipeline ready signal to MO-early pipe
  assign mo_early_pipe_ready[NUM_MO_EARLY_REGS] = mo_late_pipe_ready[0];

  // Generate the register stages
  for (genvar i = 0; i < NUM_MO_LATE_REGS; i++) begin : gen_mid_out_late_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign mo_late_pipe_ready[i] = mo_late_pipe_ready[i+1] | ~mo_late_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(mo_late_pipe_valid_q[i+1], mo_late_pipe_valid_q[i], mo_late_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipeline ready and a valid data item is present
    assign reg_ena = mo_late_pipe_ready[i] & mo_late_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(mo_late_pipe_sum_magnitude_q[i+1], mo_late_pipe_sum_magnitude_q[i], reg_ena, '0)
    `FFL(mo_late_pipe_lzc_count_sgn_q[i+1], mo_late_pipe_lzc_count_sgn_q[i], reg_ena, '0)
    `FFL(mo_late_pipe_lzc_zeroes_q[i+1],    mo_late_pipe_lzc_zeroes_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_scale_q[i+1],         mo_late_pipe_scale_q[i],         reg_ena, '0)
    `FFL(mo_late_pipe_final_sign_q[i+1],    mo_late_pipe_final_sign_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_acc_sticky_q[i+1],    mo_late_pipe_acc_sticky_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_res_is_acc_q[i+1],    mo_late_pipe_res_is_acc_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_sum_product_q[i+1],   mo_late_pipe_sum_product_q[i],   reg_ena, '0)
    `FFL(mo_late_pipe_operand_d_q[i+1],     mo_late_pipe_operand_d_q[i],     reg_ena, '0)
    `FFL(mo_late_pipe_dst_fmt_q[i+1],       mo_late_pipe_dst_fmt_q[i],       reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(mo_late_pipe_rnd_mode_q[i+1],      mo_late_pipe_rnd_mode_q[i],      reg_ena, fpnew_pkg::RNE)
    `FFL(mo_late_pipe_res_is_spec_q[i+1],   mo_late_pipe_res_is_spec_q[i],   reg_ena, '0)
    `FFL(mo_late_pipe_spec_res_q[i+1],      mo_late_pipe_spec_res_q[i],      reg_ena, '0)
    `FFL(mo_late_pipe_spec_stat_q[i+1],     mo_late_pipe_spec_stat_q[i],     reg_ena, '0)
    `FFL(mo_late_pipe_tag_q[i+1],           mo_late_pipe_tag_q[i],           reg_ena, TagType'('0))
    `FFL(mo_late_pipe_mask_q[i+1],          mo_late_pipe_mask_q[i],          reg_ena, '0)
    `FFL(mo_late_pipe_aux_q[i+1],           mo_late_pipe_aux_q[i],           reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign sum_magnitude_q2          = mo_late_pipe_sum_magnitude_q[NUM_MO_LATE_REGS];
  assign leading_zero_count_sgn_q  = mo_late_pipe_lzc_count_sgn_q[NUM_MO_LATE_REGS];
  assign lzc_zeroes_q              = mo_late_pipe_lzc_zeroes_q[NUM_MO_LATE_REGS];
  assign scale_q3                  = mo_late_pipe_scale_q[NUM_MO_LATE_REGS];
  assign final_sign_q              = mo_late_pipe_final_sign_q[NUM_MO_LATE_REGS];
  assign accumulator_sticky_q      = mo_late_pipe_acc_sticky_q[NUM_MO_LATE_REGS];
  assign result_is_accumulator_q   = mo_late_pipe_res_is_acc_q[NUM_MO_LATE_REGS];
  assign sum_product_q2            = mo_late_pipe_sum_product_q[NUM_MO_LATE_REGS];
  assign operand_d_q3              = mo_late_pipe_operand_d_q[NUM_MO_LATE_REGS];
  assign dst_fmt_q3                = mo_late_pipe_dst_fmt_q[NUM_MO_LATE_REGS];
  assign rnd_mode_q                = mo_late_pipe_rnd_mode_q[NUM_MO_LATE_REGS];
  assign result_is_special_q       = mo_late_pipe_res_is_spec_q[NUM_MO_LATE_REGS];
  assign special_result_q          = mo_late_pipe_spec_res_q[NUM_MO_LATE_REGS];
  assign special_status_q          = mo_late_pipe_spec_stat_q[NUM_MO_LATE_REGS];

  // -------------------------------------------
  // Normalization 3: Shift + mantissa assembly
  // -------------------------------------------
  logic [DST_PRECISION_BITS-1:0]   final_mantissa;
  logic signed [DST_EXP_WIDTH-1:0] final_exponent;
  logic                            sticky_after_norm;

  fpnew_mxdotp_norm_finalize #(
    .SoPFixedWidth  ( SOP_FIXED_WIDTH )
  ) i_norm_finalize (
    .sum_magnitude          ( sum_magnitude_q2         ),
    .leading_zero_count_sgn ( leading_zero_count_sgn_q ),
    .lzc_zeroes             ( lzc_zeroes_q             ),
    .scale                  ( scale_q3                 ),
    .accumulator_sticky     ( accumulator_sticky_q     ),
    .final_mantissa         ( final_mantissa           ),
    .final_exponent         ( final_exponent           ),
    .sticky_after_norm      ( sticky_after_norm        )
  );

  // ----------------------------
  // Rounding and classification
  // ----------------------------
  logic [1:0] round_sticky_bits;
  logic [NUM_FORMATS-1:0][DST_WIDTH-1:0] fmt_result;

  logic of_before_round, of_after_round; // overflow
  logic uf_after_round; // underflow

  fpnew_mxdotp_rounder #(
    .FpDstFmtConfig ( FpDstFmtConfig ),
    .SoPFixedWidth  ( SOP_FIXED_WIDTH )
  ) i_rounder (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .final_sign(final_sign_q),
    .final_mantissa(final_mantissa),
    .final_exponent(final_exponent),
    .sticky_after_norm(sticky_after_norm),
    .sum_magnitude(sum_magnitude_q2),
    .dst_fmt(dst_fmt_q3),
    .rnd_mode(rnd_mode_q),
    .round_sticky_bits(round_sticky_bits),
    .fmt_result(fmt_result),
    .of_before_round(of_before_round),
    .of_after_round(of_after_round),
    .uf_after_round(uf_after_round)
  );

  // -----------------
  // Result selection
  // -----------------
  logic [DST_WIDTH-1:0] regular_result;
  logic [DST_WIDTH-1:0] accumulator_result;
  fpnew_pkg::status_t   regular_status;
  fpnew_pkg::status_t   accumulator_status;

  // Assemble regular result
  assign regular_result    = fmt_result[dst_fmt_q3];
  assign regular_status.NV = 1'b0; // only valid cases are handled in regular path
  assign regular_status.DZ = 1'b0; // no divisions
  assign regular_status.OF = of_before_round | of_after_round;   // rounding can introduce overflow
  assign regular_status.UF = uf_after_round & regular_status.NX; // only inexact results raise UF
  assign regular_status.NX = (| round_sticky_bits) | of_before_round | of_after_round;

  // Accumulator dominates: NX if SoP was non-zero
  assign accumulator_status.NV = 1'b0;
  assign accumulator_status.DZ = 1'b0;
  assign accumulator_status.OF = 1'b0;
  assign accumulator_status.UF = 1'b0;
  assign accumulator_status.NX = (sum_product_q2 != '0);

  assign accumulator_result = (dst_fmt_q3 == fpnew_pkg::FP16ALT) ?
                              {16'hFFFF, operand_d_q3[31:16]} :
                              operand_d_q3;

  // Final results for output pipeline
  logic [DST_WIDTH-1:0] result_d;
  fpnew_pkg::status_t   status_d;

  // Select output depending on special case detection
  assign result_d = result_is_special_q ? special_result_q :
                    (result_is_accumulator_q ? accumulator_result : regular_result);
  assign status_d = result_is_special_q ? special_status_q :
                    (result_is_accumulator_q ? accumulator_status : regular_status);

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
  assign out_pipe_result_q[0]                 = result_d;
  assign out_pipe_status_q[0]                 = status_d;
  assign out_pipe_tag_q[0]                    = mo_late_pipe_tag_q[NUM_MO_LATE_REGS];
  assign out_pipe_mask_q[0]                   = mo_late_pipe_mask_q[NUM_MO_LATE_REGS];
  assign out_pipe_aux_q[0]                    = mo_late_pipe_aux_q[NUM_MO_LATE_REGS];
  assign out_pipe_valid_q[0]                  = mo_late_pipe_valid_q[NUM_MO_LATE_REGS];
  // Input stage: Propagate pipeline ready signal to MO-late pipe
  assign mo_late_pipe_ready[NUM_MO_LATE_REGS] = out_pipe_ready[0];
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
    // Enable register if pipeline ready and a valid data item is present
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
  assign busy_o          = (| {inp_pipe_valid_q, inp_mid_pipe_valid_q, mid_pipe_valid_q,
                               mo_early_pipe_valid_q, mo_late_pipe_valid_q, out_pipe_valid_q});
endmodule
