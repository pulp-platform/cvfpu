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

module fpnew_mxdotp_32 (
  input  logic                                        clk_i,
  input  logic                                        rst_ni,
  // Input signals
  input  logic [31:0][7:0]                            operands_a_i,
  input  logic [31:0][7:0]                            operands_b_i,
  input  logic [1:0]                                  operands_a_fp6_rem_i,
  input  logic [1:0]                                  operands_b_fp6_rem_i,
  input  logic [1:0][7:0]                             operands_c_i, // 2 operands
  input  logic [31:0]                                 operand_d_i, // 1 operand, accumulator
  input  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][64:0]  is_boxed_i,
  input  fpnew_pkg::roundmode_e                       rnd_mode_i,
  input  fpnew_pkg::operation_e                       op_i,
  input  logic                                        op_mod_i,
  input  fpnew_pkg::fp_format_e                       src_fmt_i, // format of the multiplicands
  input  fpnew_pkg::int_format_e                      int_fmt_i, // format of the multiplicands if they are integers
  input  fpnew_pkg::fp_format_e                       dst_fmt_i, // format of the addend and result
  input  logic                                        tag_i,
  input  logic                                        mask_i,
  input  logic                                        aux_i,
  // Input Handshake
  input  logic                                        in_valid_i,
  output logic                                        in_ready_o,
  input  logic                                        flush_i,
  // Output signals
  output logic [31:0]                                 result_o,
  output fpnew_pkg::status_t                          status_o,
  output logic                                        extension_bit_o,
  output logic                                        tag_o,
  output logic                                        mask_o,
  output logic                                        aux_o,
  // Output handshake
  output logic                                        out_valid_o,
  input  logic                                        out_ready_i,
  // Indication of valid data in flight
  output logic                                        busy_o
);

  localparam int unsigned VECTOR_SIZE = 32;
  localparam int unsigned SRC_WIDTH   = 8;
  localparam int unsigned DST_WIDTH   = 32;
  localparam int unsigned SCALE_WIDTH = 8;
  localparam int unsigned NUM_OPERANDS = 2*VECTOR_SIZE+1;

  localparam int unsigned SUPER_EXP_BITS     = 5;
  localparam int unsigned SUPER_MAN_BITS     = 3;
  localparam int unsigned SUPER_DST_EXP_BITS = 8;
  localparam int unsigned SUPER_DST_MAN_BITS = 23;

  localparam int unsigned PRECISION_BITS     = SUPER_MAN_BITS + 1;
  localparam int unsigned DST_PRECISION_BITS = SUPER_DST_MAN_BITS + 1;

  localparam int unsigned ANCHOR           = 34;
  localparam int unsigned INT_BITS         = 32;
  localparam int unsigned PROD_SHIFT_WIDTH = 1 + INT_BITS + ANCHOR;
  localparam int unsigned SOP_SHIFT        = ANCHOR - 2*SUPER_MAN_BITS;
  localparam int unsigned EXP_WIDTH        = SUPER_EXP_BITS + 1;
  localparam int unsigned DST_EXP_WIDTH    = SUPER_DST_EXP_BITS + 2;
  localparam int unsigned PROD_BITS        = 2*PRECISION_BITS+1; // +1 for the sign bit in FP8 product

  localparam int unsigned FP4_EXP_BITS         = 2;
  localparam int unsigned FP4_MAN_BITS         = 1;
  localparam int unsigned FP4_PREC_BITS        = FP4_MAN_BITS + 1;
  localparam int unsigned FP4_PROD_WIDTH       = 2*FP4_PREC_BITS+1;
  localparam int unsigned FP4_PROD_SHIFT_WIDTH = 2*(2**FP4_EXP_BITS-1-1) + FP4_PROD_WIDTH;
  localparam int unsigned FP4_VECTOR_SIZE      = VECTOR_SIZE;

  // Accumulator Constants
  localparam int unsigned VECTOR_BITS      = $clog2(VECTOR_SIZE);
  localparam int unsigned SOP_FIXED_WIDTH  = VECTOR_BITS + PROD_SHIFT_WIDTH;
  localparam int unsigned FIXED_SUM_WIDTH  = 1 + DST_PRECISION_BITS + 1 + (SOP_FIXED_WIDTH - 1); // |s|-Acc:24b-|R|-unsigned SoP:64+log2k-|
  localparam int unsigned LZC_SUM_WIDTH    = FIXED_SUM_WIDTH + DST_PRECISION_BITS;
  localparam int unsigned LZC_RESULT_WIDTH = $clog2(LZC_SUM_WIDTH);
  localparam int unsigned FP4_SUM_WIDTH    = $clog2(FP4_VECTOR_SIZE) + FP4_PROD_SHIFT_WIDTH;

  localparam int unsigned NUM_INP_REGS      = 1;
  localparam int unsigned NUM_IM_REGS       = 1;
  localparam int unsigned NUM_MID_REGS      = 0;
  localparam int unsigned NUM_MO_EARLY_REGS = 1;
  localparam int unsigned NUM_MO_LATE_REGS  = 0;
  localparam int unsigned NUM_OUT_REGS      = 1;

  typedef struct packed {
    logic                      sign;
    logic [SUPER_EXP_BITS-1:0] exponent;
    logic [SUPER_MAN_BITS-1:0] mantissa;
  } fp_src_t;
  typedef struct packed {
    logic                    sign;
    logic [FP4_EXP_BITS-1:0] exponent;
    logic [FP4_MAN_BITS-1:0] mantissa;
  } fp4_src_t;
  typedef struct packed {
    logic                          sign;
    logic [SUPER_DST_EXP_BITS-1:0] exponent;
    logic [SUPER_DST_MAN_BITS-1:0] mantissa;
  } fp_dst_t;

  // ---------------
  // Input pipeline
  // ---------------
  // Selected pipeline output signals as non-arrays
  logic [VECTOR_SIZE-1:0][SRC_WIDTH-1:0] operands_a_q;
  logic [VECTOR_SIZE-1:0][SRC_WIDTH-1:0] operands_b_q;
  logic [1:0][SCALE_WIDTH-1:0]          operands_c_q;
  logic [DST_WIDTH-1:0]                 operand_d_q;
  fpnew_pkg::fp_format_e                src_fmt_q;
  fpnew_pkg::int_format_e               int_fmt_q;
  fpnew_pkg::fp_format_e                dst_fmt_q;

  // Input pipeline signals, index i holds signal after i register stages
  logic                   [0:NUM_INP_REGS][VECTOR_SIZE-1:0][SRC_WIDTH-1:0]                 inp_pipe_operands_a_q;
  logic                   [0:NUM_INP_REGS][VECTOR_SIZE-1:0][SRC_WIDTH-1:0]                 inp_pipe_operands_b_q;
  logic                   [0:NUM_INP_REGS][1:0][SCALE_WIDTH-1:0]                          inp_pipe_operands_c_q;
  logic                   [0:NUM_INP_REGS][DST_WIDTH-1:0]                                 inp_pipe_operand_d_q;
  logic                   [0:NUM_INP_REGS][fpnew_pkg::NUM_FP_FORMATS-1:0][NUM_OPERANDS-1:0] inp_pipe_is_boxed_q;
  fpnew_pkg::roundmode_e  [0:NUM_INP_REGS]                                                inp_pipe_rnd_mode_q;
  fpnew_pkg::operation_e  [0:NUM_INP_REGS]                                                inp_pipe_op_q;
  logic                   [0:NUM_INP_REGS]                                                inp_pipe_op_mod_q;
  fpnew_pkg::fp_format_e  [0:NUM_INP_REGS]                                                inp_pipe_src_fmt_q;
  fpnew_pkg::int_format_e [0:NUM_INP_REGS]                                                inp_pipe_int_fmt_q;
  fpnew_pkg::fp_format_e  [0:NUM_INP_REGS]                                                inp_pipe_dst_fmt_q;
  logic                   [0:NUM_INP_REGS]                                                inp_pipe_tag_q;
  logic                   [0:NUM_INP_REGS]                                                inp_pipe_mask_q;
  logic                   [0:NUM_INP_REGS]                                                inp_pipe_aux_q;
  logic                   [0:NUM_INP_REGS]                                                inp_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_INP_REGS]                                                                  inp_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign inp_pipe_operands_a_q[0]         = operands_a_i;
  assign inp_pipe_operands_b_q[0]         = operands_b_i;
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
    `FFL(inp_pipe_operands_c_q[i+1],         inp_pipe_operands_c_q[i],         reg_ena, '0)
    `FFL(inp_pipe_operand_d_q[i+1],          inp_pipe_operand_d_q[i],          reg_ena, '0)
    `FFL(inp_pipe_is_boxed_q[i+1],           inp_pipe_is_boxed_q[i],           reg_ena, '0)
    `FFL(inp_pipe_rnd_mode_q[i+1],           inp_pipe_rnd_mode_q[i],           reg_ena, fpnew_pkg::RNE)
    `FFL(inp_pipe_op_q[i+1],                 inp_pipe_op_q[i],                 reg_ena, fpnew_pkg::MXDOTPF)
    `FFL(inp_pipe_op_mod_q[i+1],             inp_pipe_op_mod_q[i],             reg_ena, '0)
    `FFL(inp_pipe_src_fmt_q[i+1],            inp_pipe_src_fmt_q[i],            reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_int_fmt_q[i+1],            inp_pipe_int_fmt_q[i],            reg_ena, fpnew_pkg::int_format_e'(0))
    `FFL(inp_pipe_dst_fmt_q[i+1],            inp_pipe_dst_fmt_q[i],            reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_tag_q[i+1],                inp_pipe_tag_q[i],                reg_ena, '0)
    `FFL(inp_pipe_mask_q[i+1],               inp_pipe_mask_q[i],               reg_ena, '0)
    `FFL(inp_pipe_aux_q[i+1],                inp_pipe_aux_q[i],                reg_ena, '0)
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign operands_a_q         = inp_pipe_operands_a_q[NUM_INP_REGS];
  assign operands_b_q         = inp_pipe_operands_b_q[NUM_INP_REGS];
  assign operands_c_q         = inp_pipe_operands_c_q[NUM_INP_REGS];
  assign operand_d_q          = inp_pipe_operand_d_q[NUM_INP_REGS];
  assign src_fmt_q            = inp_pipe_src_fmt_q[NUM_INP_REGS];
  assign int_fmt_q            = inp_pipe_int_fmt_q[NUM_INP_REGS];
  assign dst_fmt_q            = inp_pipe_dst_fmt_q[NUM_INP_REGS];

  logic signed [31:0] src_bias;

  always_comb begin
    unique case (src_fmt_q)
      fpnew_pkg::FP8:    src_bias = 15;  // 2^(5-1) - 1
      fpnew_pkg::FP8ALT: src_bias = 7;   // 2^(4-1) - 1
      fpnew_pkg::FP4:    src_bias = 1;   // 2^(2-1) - 1
      default:           src_bias = 15;
    endcase
  end

  // ------------------
  // Operand unpacking
  // ------------------
  logic [2*VECTOR_SIZE-1:0][SRC_WIDTH-1:0] operands_post_inp_pipe;
  logic [2*FP4_VECTOR_SIZE-1:0][SRC_WIDTH-1:0] fp4_operands_post_inp_pipe;

  logic [VECTOR_SIZE*SRC_WIDTH-1:0] flat_operands_a_q;
  logic [VECTOR_SIZE*SRC_WIDTH-1:0] flat_operands_b_q;

  always_comb begin
    fp4_operands_post_inp_pipe = '0;
    operands_post_inp_pipe = {operands_b_q, operands_a_q};
    flat_operands_a_q = operands_a_q;
    flat_operands_b_q = operands_b_q;
    if (src_fmt_q == fpnew_pkg::FP4) begin
      for (int i = 0; i < VECTOR_SIZE; i++) begin
        fp4_operands_post_inp_pipe[i] = {{(SRC_WIDTH-4){1'b0}}, operands_a_q[i][7:4]};
        fp4_operands_post_inp_pipe[i+FP4_VECTOR_SIZE] = {{(SRC_WIDTH-4){1'b0}}, operands_b_q[i][7:4]};
      end
    end
  end

  // -----------------
  // Input processing
  // -----------------
  logic src_is_int; // if 0, it's a float

  assign src_is_int = 1'b0;

  fp_src_t [VECTOR_SIZE-1:0] operands_a, operands_b;
  logic signed [1:0][SCALE_WIDTH-1:0] operands_c;
  fp_dst_t             operand_d;
  fpnew_pkg::fp_info_t [VECTOR_SIZE-1:0] info_a, info_b;
  fpnew_pkg::fp_info_t [1:0] info_c;
  fpnew_pkg::fp_info_t info_d;

  fp4_src_t [FP4_VECTOR_SIZE-1:0] fp4_operands_a, fp4_operands_b;
  fpnew_pkg::fp_info_t [FP4_VECTOR_SIZE-1:0] fp4_info_a, fp4_info_b;

  // ----------------------------------------------------------------------------
  // Classifier (inlined)
  // ----------------------------------------------------------------------------
  logic        [fpnew_pkg::NUM_FP_FORMATS-1:0][2*VECTOR_SIZE-1:0]                     fmt_sign;
  logic signed [fpnew_pkg::NUM_FP_FORMATS-1:0][2*VECTOR_SIZE-1:0][SUPER_EXP_BITS-1:0] fmt_exponent;
  logic        [fpnew_pkg::NUM_FP_FORMATS-1:0][2*VECTOR_SIZE-1:0][SUPER_MAN_BITS-1:0] fmt_mantissa;

  fpnew_pkg::fp_info_t [fpnew_pkg::NUM_FP_FORMATS-1:0][NUM_OPERANDS-1:0] info_q;

  logic        [fpnew_pkg::NUM_FP_FORMATS-1:0][2*FP4_VECTOR_SIZE-1:0]                   fp4_fmt_sign;
  logic signed [fpnew_pkg::NUM_FP_FORMATS-1:0][2*FP4_VECTOR_SIZE-1:0][FP4_EXP_BITS-1:0] fp4_fmt_exponent;
  logic        [fpnew_pkg::NUM_FP_FORMATS-1:0][2*FP4_VECTOR_SIZE-1:0][FP4_MAN_BITS-1:0] fp4_fmt_mantissa;

  fpnew_pkg::fp_info_t [fpnew_pkg::NUM_FP_FORMATS-1:0][2*FP4_VECTOR_SIZE-1:0] fp4_info_q;

  for (genvar fmt = 0; fmt < int'(fpnew_pkg::NUM_FP_FORMATS); fmt++) begin : fmt_src_init_inputs
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (fmt == int'(fpnew_pkg::FP8) || fmt == int'(fpnew_pkg::FP8ALT) || fmt == int'(fpnew_pkg::FP4)) begin : active_src_format
      logic [2*VECTOR_SIZE-1:0][FP_WIDTH-1:0] trimmed_ops;

      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 2*VECTOR_SIZE                 ),
        .MX          ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_ops                                                  ),
        .is_boxed_i  ( inp_pipe_is_boxed_q[NUM_INP_REGS][fmt][2*VECTOR_SIZE-1:0]     ),
        .info_o      ( info_q[fmt][2*VECTOR_SIZE-1:0]                                )
      );
      for (genvar op = 0; op < 2*VECTOR_SIZE; op++) begin : gen_operands
        assign trimmed_ops[op]       = operands_post_inp_pipe[op][FP_WIDTH-1:0];
        assign fmt_sign[fmt][op]     = operands_post_inp_pipe[op][FP_WIDTH-1];
        assign fmt_exponent[fmt][op] = signed'({1'b0, operands_post_inp_pipe[op][MAN_BITS+:EXP_BITS]});
        assign fmt_mantissa[fmt][op] = operands_post_inp_pipe[op][MAN_BITS-1:0] <<
                                       (SUPER_MAN_BITS - MAN_BITS);
      end
    end else begin : inactive_src_format
      assign info_q[fmt][2*VECTOR_SIZE-1:0]  = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_sign[fmt]                  = fpnew_pkg::DONT_CARE;
      assign fmt_exponent[fmt]              = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_mantissa[fmt]              = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  for (genvar fmt = 0; fmt < int'(fpnew_pkg::NUM_FP_FORMATS); fmt++) begin : fp4_fmt_src_init_inputs
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (fmt == int'(fpnew_pkg::FP8) || fmt == int'(fpnew_pkg::FP8ALT) || fmt == int'(fpnew_pkg::FP4)) begin : active_src_format
      logic [2*FP4_VECTOR_SIZE-1:0][FP_WIDTH-1:0] trimmed_ops;

      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 2*FP4_VECTOR_SIZE    ),
        .MX          ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_ops                                                          ),
        .is_boxed_i  ( inp_pipe_is_boxed_q[NUM_INP_REGS][fmt][2*FP4_VECTOR_SIZE-1:0] ),
        .info_o      ( fp4_info_q[fmt][2*FP4_VECTOR_SIZE-1:0]                       )
      );
      for (genvar op = 0; op < 2*FP4_VECTOR_SIZE; op++) begin : gen_operands
        assign trimmed_ops[op]           = fp4_operands_post_inp_pipe[op][FP_WIDTH-1:0];
        assign fp4_fmt_sign[fmt][op]     = fp4_operands_post_inp_pipe[op][FP_WIDTH-1];
        assign fp4_fmt_exponent[fmt][op] = fp4_operands_post_inp_pipe[op][MAN_BITS+:EXP_BITS];
        assign fp4_fmt_mantissa[fmt][op] = fp4_operands_post_inp_pipe[op][MAN_BITS-1:0];
      end
    end else begin : inactive_src_format
      assign fp4_info_q[fmt][2*FP4_VECTOR_SIZE-1:0] = '{default: fpnew_pkg::DONT_CARE};
      assign fp4_fmt_sign[fmt]                              = fpnew_pkg::DONT_CARE;
      assign fp4_fmt_exponent[fmt]                          = '{default: fpnew_pkg::DONT_CARE};
      assign fp4_fmt_mantissa[fmt]                          = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  logic        [fpnew_pkg::NUM_FP_FORMATS-1:0]                         fmt_dst_sign;
  logic signed [fpnew_pkg::NUM_FP_FORMATS-1:0][SUPER_DST_EXP_BITS-1:0] fmt_dst_exponent;
  logic        [fpnew_pkg::NUM_FP_FORMATS-1:0][SUPER_DST_MAN_BITS-1:0] fmt_dst_mantissa;

  for (genvar fmt = 0; fmt < int'(fpnew_pkg::NUM_FP_FORMATS); fmt++) begin : fmt_dst_init_inputs
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (fmt == int'(fpnew_pkg::FP32)) begin : active_dst_format
      logic [FP_WIDTH-1:0] trimmed_dst_ops;
      logic                dst_ops_is_boxed;

      assign dst_ops_is_boxed = inp_pipe_is_boxed_q[NUM_INP_REGS][fmt][NUM_OPERANDS-1];

      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 1                            )
      ) i_fpnew_classifier (
        .operands_i  ( trimmed_dst_ops             ),
        .is_boxed_i  ( dst_ops_is_boxed            ),
        .info_o      ( info_q[fmt][NUM_OPERANDS-1] )
      );
      assign trimmed_dst_ops       = operand_d_q[FP_WIDTH-1:0];
      assign fmt_dst_sign[fmt]     = operand_d_q[FP_WIDTH-1];
      assign fmt_dst_exponent[fmt] = signed'({1'b0, operand_d_q[MAN_BITS+:EXP_BITS]});
      assign fmt_dst_mantissa[fmt] = {info_q[fmt][NUM_OPERANDS-1].is_normal, operand_d_q[MAN_BITS-1:0]}
                                         << (SUPER_DST_MAN_BITS - MAN_BITS);
    end else begin : inactive_dst_format
      assign info_q[fmt][NUM_OPERANDS-1] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_dst_sign[fmt]           = fpnew_pkg::DONT_CARE;
      assign fmt_dst_exponent[fmt]       = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_dst_mantissa[fmt]       = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  always_comb begin : op_select
    for (int i = 0; i < VECTOR_SIZE; i++) begin : gen_default_assignments_fp
      operands_a[i] = {fmt_sign[src_fmt_q][i], fmt_exponent[src_fmt_q][i], fmt_mantissa[src_fmt_q][i]};
      operands_b[i] = {fmt_sign[src_fmt_q][i+VECTOR_SIZE], fmt_exponent[src_fmt_q][i+VECTOR_SIZE], fmt_mantissa[src_fmt_q][i+VECTOR_SIZE]};
      info_a[i]     = info_q[src_fmt_q][i];
      info_b[i]     = info_q[src_fmt_q][i+VECTOR_SIZE];
    end
    for (int i = 0; i < FP4_VECTOR_SIZE; i++) begin : gen_default_assignments_fp4
      fp4_operands_a[i] = {fp4_fmt_sign[src_fmt_q][i], fp4_fmt_exponent[src_fmt_q][i], fp4_fmt_mantissa[src_fmt_q][i]};
      fp4_operands_b[i] = {fp4_fmt_sign[src_fmt_q][i+FP4_VECTOR_SIZE], fp4_fmt_exponent[src_fmt_q][i+FP4_VECTOR_SIZE], fp4_fmt_mantissa[src_fmt_q][i+FP4_VECTOR_SIZE]};
      fp4_info_a[i]     = fp4_info_q[src_fmt_q][i];
      fp4_info_b[i]     = fp4_info_q[src_fmt_q][i+FP4_VECTOR_SIZE];
    end
    for (int i = 0; i < 2; i++) begin : gen_default_assignments_c
      operands_c[i] = signed'(operands_c_q[i]) - 127; // signed scale, 127 = signed'(2**(SCALE_WIDTH-1)-1)
      info_c[i] = '{is_normal: 1'b1, is_nan: operands_c_q[i] == 2**SCALE_WIDTH-1, is_boxed: 1'b1, default: 1'b0};
    end
    operand_d = {fmt_dst_sign[dst_fmt_q], fmt_dst_exponent[dst_fmt_q], fmt_dst_mantissa[dst_fmt_q]};
    info_d    = info_q[dst_fmt_q][NUM_OPERANDS-1];
  end

  // ---------------------
  // Special case handling
  // ---------------------
  logic [DST_WIDTH-1:0] special_result;
  fpnew_pkg::status_t   special_status;
  logic                 result_is_special;

  logic any_operand_inf;
  logic any_operand_nan;
  logic signalling_nan;
  logic any_produced_nan;
  logic any_pos_inf;
  logic any_neg_inf;

  logic [VECTOR_SIZE-1:0] operand_inf_conditions;
  logic [VECTOR_SIZE-1:0] operand_nan_conditions;
  logic [VECTOR_SIZE-1:0] signalling_nan_conditions;
  logic [VECTOR_SIZE-1:0] nan_conditions;
  logic [VECTOR_SIZE-1:0] pos_inf_conditions;
  logic [VECTOR_SIZE-1:0] neg_inf_conditions;

  for (genvar i = 0; i < VECTOR_SIZE; i = i + 1) begin : gen_conditions
    assign operand_inf_conditions[i] = info_a[i].is_inf || info_b[i].is_inf;

    assign operand_nan_conditions[i] = info_a[i].is_nan || info_b[i].is_nan;

    assign signalling_nan_conditions[i] = info_a[i].is_signalling || info_b[i].is_signalling;

    assign nan_conditions[i] = (info_a[i].is_inf && info_b[i].is_zero) ||
                                (info_b[i].is_inf && info_a[i].is_zero);

    assign pos_inf_conditions[i] = (info_a[i].is_inf && ~(operands_a[i].sign ^ operands_b[i].sign)) ||
                                    (info_b[i].is_inf && ~(operands_a[i].sign ^ operands_b[i].sign));

    assign neg_inf_conditions[i] = (info_a[i].is_inf && (operands_a[i].sign ^ operands_b[i].sign)) ||
                                    (info_b[i].is_inf && (operands_a[i].sign ^ operands_b[i].sign));
  end

  assign any_operand_inf = |operand_inf_conditions || info_d.is_inf;
  assign any_operand_nan = |operand_nan_conditions || info_c[0].is_nan || info_c[1].is_nan || info_d.is_nan;
  assign signalling_nan  = |signalling_nan_conditions || info_c[0].is_signalling || info_c[1].is_signalling || info_d.is_signalling;
  assign any_produced_nan = |nan_conditions;
  assign any_pos_inf = |pos_inf_conditions || (info_d.is_inf && ~operand_d.sign);
  assign any_neg_inf = |neg_inf_conditions || (info_d.is_inf && operand_d.sign);

  logic               [fpnew_pkg::NUM_FP_FORMATS-1:0][DST_WIDTH-1:0] fmt_special_result;
  fpnew_pkg::status_t [fpnew_pkg::NUM_FP_FORMATS-1:0]                fmt_special_status;
  logic               [fpnew_pkg::NUM_FP_FORMATS-1:0]                fmt_result_is_special;

  for (genvar fmt = 0; fmt < int'(fpnew_pkg::NUM_FP_FORMATS); fmt++) begin : gen_special_results
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    localparam logic [EXP_BITS-1:0] QNAN_EXPONENT = '1;
    localparam logic [MAN_BITS-1:0] QNAN_MANTISSA = 2**(MAN_BITS-1);
    localparam logic [MAN_BITS-1:0] ZERO_MANTISSA = '0;

    if (fmt == int'(fpnew_pkg::FP32)) begin : active_format
      always_comb begin : special_cases
        logic [FP_WIDTH-1:0] special_res;

        special_res                = {1'b0, QNAN_EXPONENT, QNAN_MANTISSA};
        fmt_special_status[fmt]    = '0;
        fmt_result_is_special[fmt] = 1'b0;

        if (any_produced_nan) begin
          fmt_result_is_special[fmt] = 1'b1;
          fmt_special_status[fmt].NV = 1'b1;
        end else if (any_operand_nan) begin
          fmt_result_is_special[fmt] = 1'b1;
          fmt_special_status[fmt].NV = signalling_nan;
        end else if (any_operand_inf) begin
          fmt_result_is_special[fmt] = 1'b1;
          if (any_pos_inf && any_neg_inf) begin
            fmt_special_status[fmt].NV = 1'b1;
          end else if (any_pos_inf) begin
            special_res = {1'b0, QNAN_EXPONENT, ZERO_MANTISSA};
          end else if (any_neg_inf) begin
            special_res = {1'b1, QNAN_EXPONENT, ZERO_MANTISSA};
          end
        end
        fmt_special_result[fmt]               = '1;
        fmt_special_result[fmt][FP_WIDTH-1:0] = special_res;
      end
    end else begin : inactive_format
      assign fmt_special_result[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_special_status[fmt] = '0;
      assign fmt_result_is_special[fmt] = 1'b0;
    end
  end

  assign result_is_special = fmt_result_is_special[dst_fmt_q];
  assign special_status = fmt_special_status[dst_fmt_q];
  assign special_result = fmt_special_result[dst_fmt_q];

  // ------------------
  // Scale data path
  // ------------------
  logic signed [SCALE_WIDTH:0] scale; // +1 for addition

  assign scale = signed'(operands_c[0]) + signed'(operands_c[1]);

  // ------------------
  // Product data path
  // ------------------
  logic signed [VECTOR_SIZE-1:0][PROD_BITS-1:0] product_signed;  // two's complement product, already signed
  logic signed [FP4_VECTOR_SIZE-1:0][2*FP4_PREC_BITS:0] fp4_product_signed;  // two's complement product, +1 for sign bit

  logic [VECTOR_SIZE-1:0][  PRECISION_BITS-1:0] mantissa_a, mantissa_b;
  logic [VECTOR_SIZE-1:0][2*PRECISION_BITS-1:0] product;

  for (genvar i = 0; i < VECTOR_SIZE; i++) begin : gen_mantissa
    assign mantissa_a[i] = {info_a[i].is_normal, operands_a[i].mantissa};
    assign mantissa_b[i] = {info_b[i].is_normal, operands_b[i].mantissa};
    assign product[i]    = mantissa_a[i] * mantissa_b[i];
    assign product_signed[i] = (operands_a[i].sign ^ operands_b[i].sign) ? -product[i] : product[i];
  end

  logic [FP4_VECTOR_SIZE-1:0][  FP4_PREC_BITS-1:0] fp4_mantissa_a, fp4_mantissa_b;
  logic [FP4_VECTOR_SIZE-1:0][2*FP4_PREC_BITS-1:0] fp4_product;

  for (genvar i = 0; i < FP4_VECTOR_SIZE; i++) begin : gen_fp4_mantissa
    assign fp4_mantissa_a[i] = {fp4_info_a[i].is_normal, fp4_operands_a[i].mantissa};
    assign fp4_mantissa_b[i] = {fp4_info_b[i].is_normal, fp4_operands_b[i].mantissa};
    assign fp4_product[i]    = fp4_mantissa_a[i] * fp4_mantissa_b[i];
    assign fp4_product_signed[i] = (fp4_operands_a[i].sign ^ fp4_operands_b[i].sign) ? -fp4_product[i] : fp4_product[i];
  end

  // ------------------
  // Shift data path
  // ------------------
  logic signed [VECTOR_SIZE-1:0][PROD_SHIFT_WIDTH-1:0] shifted_product;
  logic signed [FP4_VECTOR_SIZE-1:0][FP4_PROD_SHIFT_WIDTH-1:0] fp4_shifted_product;

  logic signed [VECTOR_SIZE-1:0][EXP_WIDTH-1:0] exponent_product;

  for (genvar i = 0; i < VECTOR_SIZE; i++) begin : gen_exponent_adjustment
    assign exponent_product[i] = operands_a[i].exponent + info_a[i].is_subnormal
                                + operands_b[i].exponent + info_b[i].is_subnormal
                                - 2*src_bias;
    assign shifted_product[i] = signed'(product_signed[i]) << (signed'(SOP_SHIFT) + signed'(exponent_product[i]));
  end

  logic signed [FP4_VECTOR_SIZE-1:0][2:0] fp4_exponent_product;

  for (genvar i = 0; i < FP4_VECTOR_SIZE; i++) begin : gen_fp4_exponent_adjustment
    assign fp4_exponent_product[i] = fp4_operands_a[i].exponent + fp4_info_a[i].is_subnormal
                                + fp4_operands_b[i].exponent + fp4_info_b[i].is_subnormal
                                - 2*src_bias;
    assign fp4_shifted_product[i] = signed'(fp4_product_signed[i]) << fp4_exponent_product[i];
  end

  // --------------------
  // INP to MID pipeline
  // --------------------
  // Selected pipeline output signals as non-arrays
  logic signed [VECTOR_SIZE-1:0][PROD_SHIFT_WIDTH-1:0]          shifted_product_q;
  logic signed [FP4_VECTOR_SIZE-1:0][FP4_PROD_SHIFT_WIDTH-1:0] fp4_shifted_product_q;

  // Inp-mid pipeline signals, index i holds signal after i register stages
  logic signed           [0:NUM_IM_REGS][VECTOR_SIZE-1:0][PROD_SHIFT_WIDTH-1:0]          inp_mid_pipe_shifted_product_q;
  logic signed           [0:NUM_IM_REGS][FP4_VECTOR_SIZE-1:0][FP4_PROD_SHIFT_WIDTH-1:0] inp_mid_pipe_fp4_shifted_product_q;
  fpnew_pkg::fp_format_e [0:NUM_IM_REGS]                                                inp_mid_pipe_dst_fmt_q;
  logic                  [0:NUM_IM_REGS][SCALE_WIDTH:0]                                 inp_mid_pipe_scale_q;
  fp_dst_t               [0:NUM_IM_REGS]                                                inp_mid_pipe_operand_d_q;
  fpnew_pkg::fp_info_t   [0:NUM_IM_REGS]                                                inp_mid_pipe_info_d_q;
  fpnew_pkg::roundmode_e [0:NUM_IM_REGS]                                                inp_mid_pipe_rnd_mode_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_res_is_spec_q;
  logic                  [0:NUM_IM_REGS][DST_WIDTH-1:0]                                 inp_mid_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_IM_REGS]                                                inp_mid_pipe_spec_stat_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_tag_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_mask_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_aux_q;
  logic                  [0:NUM_IM_REGS]                                                inp_mid_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_IM_REGS]                                                                 inp_mid_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign inp_mid_pipe_shifted_product_q[0]     = shifted_product;
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
    `FFL(inp_mid_pipe_fp4_shifted_product_q[i+1], inp_mid_pipe_fp4_shifted_product_q[i], reg_ena, '0)
    `FFL(inp_mid_pipe_dst_fmt_q[i+1],             inp_mid_pipe_dst_fmt_q[i],             reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_mid_pipe_scale_q[i+1],               inp_mid_pipe_scale_q[i],               reg_ena, '0)
    `FFL(inp_mid_pipe_operand_d_q[i+1],           inp_mid_pipe_operand_d_q[i],           reg_ena, '0)
    `FFL(inp_mid_pipe_info_d_q[i+1],              inp_mid_pipe_info_d_q[i],              reg_ena, '0)
    `FFL(inp_mid_pipe_rnd_mode_q[i+1],            inp_mid_pipe_rnd_mode_q[i],            reg_ena, fpnew_pkg::RNE)
    `FFL(inp_mid_pipe_res_is_spec_q[i+1],         inp_mid_pipe_res_is_spec_q[i],         reg_ena, '0)
    `FFL(inp_mid_pipe_spec_res_q[i+1],            inp_mid_pipe_spec_res_q[i],            reg_ena, '0)
    `FFL(inp_mid_pipe_spec_stat_q[i+1],           inp_mid_pipe_spec_stat_q[i],           reg_ena, '0)
    `FFL(inp_mid_pipe_tag_q[i+1],                 inp_mid_pipe_tag_q[i],                 reg_ena, '0)
    `FFL(inp_mid_pipe_mask_q[i+1],                inp_mid_pipe_mask_q[i],                reg_ena, '0)
    `FFL(inp_mid_pipe_aux_q[i+1],                 inp_mid_pipe_aux_q[i],                 reg_ena, '0)
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign shifted_product_q     = inp_mid_pipe_shifted_product_q[NUM_IM_REGS];
  assign fp4_shifted_product_q = inp_mid_pipe_fp4_shifted_product_q[NUM_IM_REGS];

  // ------------------
  // Adder data path
  // ------------------
  logic signed [SOP_FIXED_WIDTH-1:0] sum_product_fp8;
  logic signed [FP4_SUM_WIDTH-1:0]   sum_product_fp4;
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product;

  always_comb begin : sum_products
    sum_product_fp8 = '0;
    for (int i = 0; i < VECTOR_SIZE; i++) begin : gen_sum_products
      sum_product_fp8 += signed'(shifted_product_q[i]);
    end
  end

  always_comb begin : fp4_sum_products
    sum_product_fp4 = '0;
    for (int i = 0; i < FP4_VECTOR_SIZE; i++) begin : gen_fp4_sum_products
      sum_product_fp4 += signed'(fp4_shifted_product_q[i]);
    end
  end

  // Unified format adder: handles FP8 + FP4
  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_fp4_shifted;

  assign sum_product_fp4_shifted = signed'(sum_product_fp4) << (SOP_SHIFT+2*(SUPER_MAN_BITS-FP4_MAN_BITS));
  assign sum_product = sum_product_fp8 + sum_product_fp4_shifted;

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
  logic                  [0:NUM_MID_REGS]                         mid_pipe_tag_q;
  logic                  [0:NUM_MID_REGS]                         mid_pipe_mask_q;
  logic                  [0:NUM_MID_REGS]                         mid_pipe_aux_q;
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
    `FFL(mid_pipe_tag_q[i+1],         mid_pipe_tag_q[i],         reg_ena, '0)
    `FFL(mid_pipe_mask_q[i+1],        mid_pipe_mask_q[i],        reg_ena, '0)
    `FFL(mid_pipe_aux_q[i+1],         mid_pipe_aux_q[i],         reg_ena, '0)
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

  localparam int signed MAX_ACC_SHIFT_AMOUNT = FIXED_SUM_WIDTH - DST_PRECISION_BITS - 1;

  logic signed [9:0]                   acc_shift_amount;
  logic signed [DST_EXP_WIDTH-1:0]     acc_exponent_d;
  logic [DST_PRECISION_BITS-1:0]       acc_mantissa_d;

  assign acc_exponent_d = {1'b0, operand_d_q2.exponent};
  assign acc_mantissa_d = {info_d_q.is_normal, operand_d_q2.mantissa};
  assign signed_mantissa_d = operand_d_q2.sign ? -acc_mantissa_d : acc_mantissa_d;

  assign acc_shift_amount = signed'(ANCHOR - SUPER_DST_MAN_BITS) - signed'(scale_q)
                            + signed'(acc_exponent_d + info_d_q.is_subnormal)
                            - 32'sd127;

  always_comb begin : accumulator_shift
    result_is_accumulator = 1'b0;
    accumulator_is_right_shifted = 1'b0;
    accumulator_right_shift_amount = '0;
    accumulator_remaining = '0;
    accumulator_sticky = 1'b0;
    if (acc_shift_amount > MAX_ACC_SHIFT_AMOUNT) begin
      accumulator_shifted = '0;
      result_is_accumulator = 1'b1;
    end else if (acc_shift_amount >= 0) begin
      accumulator_shifted = signed'(signed_mantissa_d) <<< acc_shift_amount;
    end else begin
      accumulator_is_right_shifted = 1'b1;
      accumulator_right_shift_amount = -acc_shift_amount;
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

  // -----------------
  // Accumulator + SoP
  // -----------------
  logic signed [LZC_SUM_WIDTH-1:0] sum_product_accumulator_extended;

  logic signed [FIXED_SUM_WIDTH-1:0] sum_product_accumulator;

  assign sum_product_accumulator = sum_product_q + accumulator_shifted;
  assign sum_product_accumulator_extended = {sum_product_accumulator, accumulator_remaining};

  // ----------------------------------
  // Normalization 1: Two's complement
  // ----------------------------------
  logic final_sign;
  logic [LZC_SUM_WIDTH-1:0] sum_magnitude;

  logic [LZC_SUM_WIDTH-1:0] twos_compl_in;

  assign twos_compl_in = sum_product_accumulator_extended;
  assign final_sign = twos_compl_in[LZC_SUM_WIDTH-1];

  always_comb begin : get_twos_complement
    if (final_sign) begin
      sum_magnitude = ~twos_compl_in + 1;
      if (accumulator_is_right_shifted && accumulator_right_shift_amount > DST_PRECISION_BITS && signed_mantissa_d != 0 && accumulator_sticky) begin
        sum_magnitude = ~twos_compl_in;
      end
    end else begin
      sum_magnitude = twos_compl_in;
    end
  end

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
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_tag_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_mask_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_aux_q;
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
    `FFL(mo_early_pipe_tag_q[i+1],           mo_early_pipe_tag_q[i],           reg_ena, '0)
    `FFL(mo_early_pipe_mask_q[i+1],          mo_early_pipe_mask_q[i],          reg_ena, '0)
    `FFL(mo_early_pipe_aux_q[i+1],           mo_early_pipe_aux_q[i],           reg_ena, '0)
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign sum_magnitude_q = mo_early_pipe_sum_magnitude_q[NUM_MO_EARLY_REGS];
  assign scale_q2        = mo_early_pipe_scale_q[NUM_MO_EARLY_REGS];

  // ---------------------
  // Normalization 2: LZC
  // ---------------------
  logic signed [LZC_RESULT_WIDTH:0] leading_zero_count_sgn;
  logic                             lzc_zeroes;

  logic [LZC_RESULT_WIDTH-1:0] leading_zero_count;

  cc_lzc #(
    .Width ( LZC_SUM_WIDTH                ),
    .Mode  ( cc_pkg::LZC_LEADING_ZERO_CNT )
  ) i_lzc (
    .in_i    ( sum_magnitude_q    ),
    .cnt_o   ( leading_zero_count ),
    .empty_o ( lzc_zeroes         )
  );

  assign leading_zero_count_sgn = signed'({1'b0, leading_zero_count});

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
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_tag_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_mask_q;
  logic                  [0:NUM_MO_LATE_REGS]                         mo_late_pipe_aux_q;
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
    `FFL(mo_late_pipe_tag_q[i+1],           mo_late_pipe_tag_q[i],           reg_ena, '0)
    `FFL(mo_late_pipe_mask_q[i+1],          mo_late_pipe_mask_q[i],          reg_ena, '0)
    `FFL(mo_late_pipe_aux_q[i+1],           mo_late_pipe_aux_q[i],           reg_ena, '0)
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

  localparam int unsigned SHIFT_AMOUNT_WIDTH = $clog2(fpnew_pkg::bias(fpnew_pkg::FP32) - ANCHOR + 2**(SCALE_WIDTH) - 1 + FIXED_SUM_WIDTH - 1);

  logic signed [DST_EXP_WIDTH-1:0]      final_tentative_exponent;
  logic        [SHIFT_AMOUNT_WIDTH-1:0] norm_shamt;
  logic signed [DST_EXP_WIDTH-1:0]      normalized_exponent;

  logic [LZC_SUM_WIDTH-1:0]                    sum_shifted;
  logic [LZC_SUM_WIDTH-DST_PRECISION_BITS-1:0] sum_sticky_bits;

  assign final_tentative_exponent = 127 - (signed'(ANCHOR) - signed'(scale_q3))
                                    + (signed'(FIXED_SUM_WIDTH) - leading_zero_count_sgn_q - 1);

  always_comb begin : norm_shift_amount
    if (final_tentative_exponent > 0 && !lzc_zeroes_q) begin
      norm_shamt          = leading_zero_count_sgn_q + 1;
      normalized_exponent = final_tentative_exponent;
    end else begin
      norm_shamt          = leading_zero_count_sgn_q + final_tentative_exponent;
      normalized_exponent = '0;
    end
  end

  assign sum_shifted = sum_magnitude_q2 << norm_shamt;

  assign {final_mantissa, sum_sticky_bits} = sum_shifted;
  assign final_exponent                    = normalized_exponent;
  assign sticky_after_norm                 = (|sum_sticky_bits) | accumulator_sticky_q;

  // ----------------------------
  // Rounding and classification
  // ----------------------------
  logic [1:0] round_sticky_bits;
  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][DST_WIDTH-1:0] fmt_result;

  logic of_before_round, of_after_round; // overflow
  logic uf_after_round; // underflow

  logic                                             pre_round_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] pre_round_abs; // absolute value of result before rounding

  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] fmt_pre_round_abs; // per format
  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][1:0]                                       fmt_round_sticky_bits;

  logic [fpnew_pkg::NUM_FP_FORMATS-1:0]                           fmt_of_after_round;
  logic [fpnew_pkg::NUM_FP_FORMATS-1:0]                           fmt_uf_after_round;

  logic                                             rounded_sign;
  logic [SUPER_DST_EXP_BITS+SUPER_DST_MAN_BITS-1:0] rounded_abs; // absolute value of result after rounding
  logic                                             result_zero;

  // Classification before round. RISC-V mandates checking underflow AFTER rounding
  assign of_before_round = final_exponent >= 2**(fpnew_pkg::exp_bits(dst_fmt_q3))-1; // infinity exponent is all ones

  // Pack exponent and mantissa into proper rounding form
  for (genvar fmt = 0; fmt < int'(fpnew_pkg::NUM_FP_FORMATS); fmt++) begin : gen_res_assemble
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    logic [EXP_BITS-1:0] pre_round_exponent;
    logic [MAN_BITS-1:0] pre_round_mantissa;

    if (fmt == int'(fpnew_pkg::FP32)) begin : active_dst_format

      assign pre_round_exponent = (of_before_round) ? 2**EXP_BITS-2 : final_exponent[EXP_BITS-1:0];
      assign pre_round_mantissa = (of_before_round) ? '1 : final_mantissa[SUPER_DST_MAN_BITS-:MAN_BITS];
      // Assemble result before rounding. In case of overflow, the largest normal value is set.
      assign fmt_pre_round_abs[fmt] = {pre_round_exponent, pre_round_mantissa}; // 0-extend

      // Round bit is after mantissa (1 in case of overflow for rounding)
      assign fmt_round_sticky_bits[fmt][1] = final_mantissa[SUPER_DST_MAN_BITS-MAN_BITS] |
                                             of_before_round;

      // remaining bits in mantissa to sticky (1 in case of overflow for rounding)
      assign fmt_round_sticky_bits[fmt][0] = sticky_after_norm | of_before_round;
    end else begin : inactive_format
      assign fmt_pre_round_abs[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_round_sticky_bits[fmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Assemble result before rounding. In case of overflow, the largest normal value is set.
  assign pre_round_abs      = fmt_pre_round_abs[dst_fmt_q3];

  // In case of overflow, the round and sticky bits are set for proper rounding
  assign round_sticky_bits  = fmt_round_sticky_bits[dst_fmt_q3];
  assign pre_round_sign     = final_sign_q;

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


  for (genvar fmt = 0; fmt < int'(fpnew_pkg::NUM_FP_FORMATS); fmt++) begin : gen_sign_inject
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (fmt == int'(fpnew_pkg::FP32)) begin : active_dst_format
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
  assign uf_after_round = fmt_uf_after_round[dst_fmt_q3];
  assign of_after_round = fmt_of_after_round[dst_fmt_q3];

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

  assign accumulator_result = operand_d_q3;

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
  logic               [0:NUM_OUT_REGS]                out_pipe_tag_q;
  logic               [0:NUM_OUT_REGS]                out_pipe_mask_q;
  logic               [0:NUM_OUT_REGS]                out_pipe_aux_q;
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
    `FFL(out_pipe_tag_q[i+1],    out_pipe_tag_q[i],    reg_ena, '0)
    `FFL(out_pipe_mask_q[i+1],   out_pipe_mask_q[i],   reg_ena, '0)
    `FFL(out_pipe_aux_q[i+1],    out_pipe_aux_q[i],    reg_ena, '0)
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
