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

module fpnew_mxdotp_multi_param
  import fpnew_mxdotp_multi_pkg::*;
#(
  // By default, all MX formats (FP8, FP8ALT, FP6, FP6ALT, FP4, INT8) are enabled for the source and FP32 for the destination.
  parameter fpnew_pkg::fmt_logic_t   FpSrcFmtConfig  = MxdotpSrcFpFmtConfig,
  parameter fpnew_pkg::ifmt_logic_t  IntSrcFmtConfig = MxdotpSrcIntFmtConfig,
  parameter fpnew_pkg::fmt_logic_t   FpDstFmtConfig  = 9'b100000000,
  parameter int unsigned             LaneWidth   = 64,
  parameter int unsigned             VectorSize  = LaneWidth/SRC_WIDTH,
  parameter int unsigned             NumPipeRegs = 4,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::BEFORE,
  parameter int unsigned             L1Width     = $clog2(VectorSize) + PROD_SHIFT_WIDTH,
  parameter bit                      L1Wrap      = 1'b0,
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

  if ((FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) && ((LaneWidth + 2) % 6 != 0)) begin : gen_fp6_lane_check
    $fatal(1, "MXDOTP FP6 requires LaneWidth+2 (lane plus 2-bit FP6 remainder) to be a multiple of 6, got LaneWidth=%0d", LaneWidth);
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
                                            (((FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) == 1) ? cc_pkg::ceil_div(LaneWidth, 6) - VectorSize : cc_pkg::ceil_div(LaneWidth, 6)) : 0;
  localparam int unsigned FP6_VECTOR_SIZE_GUARDED = (FP6_VECTOR_SIZE > 0) ? FP6_VECTOR_SIZE : 1;
  localparam int unsigned FP4_VECTOR_SIZE = (FpSrcFmtConfig[fpnew_pkg::FP4] == 1) ?
                                            (((FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT]) == 1) ?
                                            (((FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) == 1) ? (VectorSize - FP6_VECTOR_SIZE) : VectorSize) : 2*VectorSize) : 0;
  localparam int unsigned FP4_VECTOR_SIZE_GUARDED = (FP4_VECTOR_SIZE > 0) ? FP4_VECTOR_SIZE : 1;

  localparam logic FP8_LANES = FpSrcFmtConfig[fpnew_pkg::FP8] || FpSrcFmtConfig[fpnew_pkg::FP8ALT] || IntSrcFmtConfig[fpnew_pkg::INT8];
  localparam logic FP6_LANES = FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT];
  localparam logic FP4_LANES = FpSrcFmtConfig[fpnew_pkg::FP4];
  localparam logic INT8_LANE = IntSrcFmtConfig[fpnew_pkg::INT8];

  // Accumulator Constants
  localparam int unsigned VECTOR_BITS     = $clog2(VectorSize);
  localparam int unsigned SOP_FIXED_WIDTH = VECTOR_BITS + PROD_SHIFT_WIDTH;

  // Shifted-anchor L1 accumulator constants per source format: 0 FP8, 1 FP8ALT, 2 FP6, 3 FP6ALT, 4 FP4, 5 INT8
  `define L1_MAX(a, b) (((a) > (b)) ? (a) : (b))
  `define L1_MIN(a, b) (((a) < (b)) ? (a) : (b))
  localparam int   L1_W        = int'(L1Width) - 1;
  localparam int   FP6_ELEMS   = (FP8_LANES ? int'(VectorSize) : 0) + int'(FP6_VECTOR_SIZE);
  localparam int   FP4_ELEMS   = (FP8_LANES ? int'(VectorSize) : 0) + int'(FP6_VECTOR_SIZE) + int'(FP4_VECTOR_SIZE);
  localparam logic L1_EN   [6] = '{FpSrcFmtConfig[fpnew_pkg::FP8], FpSrcFmtConfig[fpnew_pkg::FP8ALT], FpSrcFmtConfig[fpnew_pkg::FP6],
                                   FpSrcFmtConfig[fpnew_pkg::FP6ALT], FpSrcFmtConfig[fpnew_pkg::FP4], IntSrcFmtConfig[fpnew_pkg::INT8]};
  localparam int   L1_MAN  [6] = '{fpnew_pkg::man_bits(fpnew_pkg::FP8), fpnew_pkg::man_bits(fpnew_pkg::FP8ALT),
                                   fpnew_pkg::man_bits(fpnew_pkg::FP6), fpnew_pkg::man_bits(fpnew_pkg::FP6ALT),
                                   fpnew_pkg::man_bits(fpnew_pkg::FP4), 0};
  localparam int   L1_BIAS [6] = '{fpnew_pkg::bias(fpnew_pkg::FP8), fpnew_pkg::bias(fpnew_pkg::FP8ALT), fpnew_pkg::bias(fpnew_pkg::FP6),
                                   fpnew_pkg::bias(fpnew_pkg::FP6ALT), fpnew_pkg::bias(fpnew_pkg::FP4), 0};
  localparam int   L1_EMAX [6] = '{2**fpnew_pkg::exp_bits(fpnew_pkg::FP8) - 2, 2**fpnew_pkg::exp_bits(fpnew_pkg::FP8ALT) - 1,
                                   2**fpnew_pkg::exp_bits(fpnew_pkg::FP6) - 1, 2**fpnew_pkg::exp_bits(fpnew_pkg::FP6ALT) - 1,
                                   2**fpnew_pkg::exp_bits(fpnew_pkg::FP4) - 1, 0};
  localparam int   L1_SIG  [6] = '{2**(L1_MAN[0]+1) - 1, 2**(L1_MAN[1]+1) - 2, 2**(L1_MAN[2]+1) - 1,
                                   2**(L1_MAN[3]+1) - 1, 2**(L1_MAN[4]+1) - 1, 2**7};
  localparam int   L1_EXP  [6] = '{2*(L1_EMAX[0] - L1_BIAS[0]), 2*(L1_EMAX[1] - L1_BIAS[1]), 2*(L1_EMAX[2] - L1_BIAS[2]),
                                   2*(L1_EMAX[3] - L1_BIAS[3]), 2*(L1_EMAX[4] - L1_BIAS[4]), 0};
  localparam int   L1_P    [6] = '{$clog2(L1_SIG[0]**2 + 1) - 2*L1_MAN[0] + L1_EXP[0], $clog2(L1_SIG[1]**2 + 1) - 2*L1_MAN[1] + L1_EXP[1],
                                   $clog2(L1_SIG[2]**2 + 1) - 2*L1_MAN[2] + L1_EXP[2], $clog2(L1_SIG[3]**2 + 1) - 2*L1_MAN[3] + L1_EXP[3],
                                   $clog2(L1_SIG[4]**2 + 1) - 2*L1_MAN[4] + L1_EXP[4], $clog2(L1_SIG[5]**2 + 1)};
  localparam int   L1_F    [6] = '{2*(L1_BIAS[0] - 1 + L1_MAN[0]), 2*(L1_BIAS[1] - 1 + L1_MAN[1]), 2*(L1_BIAS[2] - 1 + L1_MAN[2]),
                                   2*(L1_BIAS[3] - 1 + L1_MAN[3]), 2*(L1_BIAS[4] - 1 + L1_MAN[4]), 0};
  localparam int   L1_K    [6] = '{L1_P[0] + $clog2(VectorSize), L1_P[1] + $clog2(VectorSize), L1_P[2] + $clog2(FP6_ELEMS),
                                   L1_P[3] + $clog2(FP6_ELEMS), L1_P[4] + $clog2(FP4_ELEMS), L1_P[5] + $clog2(VectorSize)};
  localparam int   L1_I    [6] = '{`L1_MIN(`L1_MAX(L1_W, L1_P[0] + 2), L1_K[0]), `L1_MIN(`L1_MAX(L1_W, L1_P[1] + 2), L1_K[1]),
                                   `L1_MIN(`L1_MAX(L1_W, L1_P[2] + 2), L1_K[2]), `L1_MIN(`L1_MAX(L1_W, L1_P[3] + 2), L1_K[3]),
                                   `L1_MIN(`L1_MAX(L1_W, L1_P[4] + 2), L1_K[4]), `L1_MIN(`L1_MAX(L1_W, L1_P[5] + 2), L1_K[5])};
  localparam int   L1_A    [6] = '{`L1_MIN(L1_W - L1_I[0], int'(ANCHOR)), `L1_MIN(L1_W - L1_I[1], int'(ANCHOR)),
                                   `L1_MIN(L1_W - L1_I[2], int'(ANCHOR)), `L1_MIN(L1_W - L1_I[3], int'(ANCHOR)),
                                   `L1_MIN(L1_W - L1_I[4], int'(ANCHOR)), `L1_MIN(L1_W - L1_I[5], int'(ANCHOR))};
  localparam logic L1_OVF  [6] = '{L1_EN[0] && (L1_W < L1_K[0]), L1_EN[1] && (L1_W < L1_K[1]), L1_EN[2] && (L1_W < L1_K[2]),
                                   L1_EN[3] && (L1_W < L1_K[3]), L1_EN[4] && (L1_W < L1_K[4]), L1_EN[5] && (L1_W < L1_K[5])};
  localparam int   L1_A_HI [6] = '{L1_EN[0] ? L1_A[0] : -1024, L1_EN[1] ? L1_A[1] : -1024, L1_EN[2] ? L1_A[2] : -1024,
                                   L1_EN[3] ? L1_A[3] : -1024, L1_EN[4] ? L1_A[4] : -1024, L1_EN[5] ? L1_A[5] : -1024};
  localparam int   L1_A_LO [6] = '{L1_EN[0] ? L1_A[0] : 1024, L1_EN[1] ? L1_A[1] : 1024, L1_EN[2] ? L1_A[2] : 1024,
                                   L1_EN[3] ? L1_A[3] : 1024, L1_EN[4] ? L1_A[4] : 1024, L1_EN[5] ? L1_A[5] : 1024};
  localparam int   L1_SPARE[6] = '{L1_EN[0] ? L1_A[0] - L1_F[0] : 1024, L1_EN[1] ? L1_A[1] - L1_F[1] : 1024,
                                   L1_EN[2] ? L1_A[2] - L1_F[2] : 1024, L1_EN[3] ? L1_A[3] - L1_F[3] : 1024,
                                   L1_EN[4] ? L1_A[4] - L1_F[4] : 1024, L1_EN[5] ? L1_A[5] - L1_F[5] : 1024};
  localparam int   L1_REF_ANCHOR = `L1_MAX(`L1_MAX(`L1_MAX(L1_A_HI[0], L1_A_HI[1]), `L1_MAX(L1_A_HI[2], L1_A_HI[3])),
                                           `L1_MAX(L1_A_HI[4], L1_A_HI[5]));
  localparam int   L1_MIN_ANCHOR = `L1_MIN(`L1_MIN(`L1_MIN(L1_A_LO[0], L1_A_LO[1]), `L1_MIN(L1_A_LO[2], L1_A_LO[3])),
                                           `L1_MIN(L1_A_LO[4], L1_A_LO[5]));
  localparam int   L1_MIN_SPARE  = `L1_MIN(`L1_MIN(`L1_MIN(L1_SPARE[0], L1_SPARE[1]), `L1_MIN(L1_SPARE[2], L1_SPARE[3])),
                                           `L1_MIN(L1_SPARE[4], L1_SPARE[5]));
  localparam int   L1_MAX_ADJUST = L1_REF_ANCHOR - L1_MIN_ANCHOR;

  // Saturating accumulation in element order (FP8 lane, then FP6 lane, then FP4 lane) only where a format can overflow
  localparam logic L1_SAT_FP8   = !L1Wrap && FP8_LANES && (L1_OVF[0] || L1_OVF[1] || L1_OVF[2] || L1_OVF[3] || L1_OVF[4] || L1_OVF[5]);
  localparam logic L1_CHAIN_FP6 = !L1Wrap && FP8_LANES && FP6_LANES && (L1_OVF[2] || L1_OVF[3] || L1_OVF[4]);
  localparam logic L1_CHAIN_FP4 = !L1Wrap && FP8_LANES && FP4_LANES && L1_OVF[4];

  // FP8 lane: products on the L1 grid of the source format
  localparam int          FP8_OFFSET  [6] = '{L1_A[0] - 2*int'(SUPER_MAN_BITS), L1_A[1] - 2*int'(SUPER_MAN_BITS),
                                              L1_A[2] - 2*int'(SUPER_MAN_BITS), L1_A[3] - 2*int'(SUPER_MAN_BITS),
                                              L1_A[4] - 2*int'(SUPER_MAN_BITS), L1_A[5]};
  localparam int          FP8_Q       [6] = '{L1_EN[0] ? L1_P[0] + L1_A[0] : 1, L1_EN[1] ? L1_P[1] + L1_A[1] : 1,
                                              L1_EN[2] ? L1_P[2] + L1_A[2] : 1, L1_EN[3] ? L1_P[3] + L1_A[3] : 1,
                                              L1_EN[4] ? L1_P[4] + L1_A[4] : 1, L1_EN[5] ? L1_P[5] + L1_A[5] : 1};
  localparam int          FP8_MAX_Q       = `L1_MAX(`L1_MAX(`L1_MAX(FP8_Q[0], FP8_Q[1]), `L1_MAX(FP8_Q[2], FP8_Q[3])),
                                                    `L1_MAX(FP8_Q[4], FP8_Q[5]));
  localparam int unsigned FP8_MAX_Q_WIDTH = (FP8_MAX_Q > 1) ? FP8_MAX_Q : 1;
  localparam int unsigned FP8_TERM_WIDTH  = (L1Wrap && (FP8_MAX_Q_WIDTH >= L1Width)) ? L1Width :
                                            ((FP8_MAX_Q_WIDTH < L1Width) ? FP8_MAX_Q_WIDTH : L1Width) + 1;

  // FP6 lane (FP6, FP6ALT, FP4 sources): lane grid no finer than the format needs, aligned to the L1 grid after the sum
  localparam int          FP6_LA      [3] = '{L1_CHAIN_FP6 ? L1_A[2] : `L1_MIN(L1_A[2], L1_F[2]),
                                              L1_CHAIN_FP6 ? L1_A[3] : `L1_MIN(L1_A[3], L1_F[3]),
                                              L1_CHAIN_FP6 ? L1_A[4] : `L1_MIN(L1_A[4], L1_F[4])};
  localparam int          FP6_OFFSET  [3] = '{FP6_LA[0] - 2*int'(FP6_MAN_BITS), FP6_LA[1] - 2*int'(FP6_MAN_BITS),
                                              FP6_LA[2] - 2*int'(FP6_MAN_BITS)};
  localparam int          FP6_ALIGN   [3] = '{L1_A[2] - FP6_LA[0], L1_A[3] - FP6_LA[1], L1_A[4] - FP6_LA[2]};
  localparam int          FP6_Q       [3] = '{L1_EN[2] ? L1_P[2] + FP6_LA[0] : 1, L1_EN[3] ? L1_P[3] + FP6_LA[1] : 1,
                                              L1_EN[4] ? L1_P[4] + FP6_LA[2] : 1};
  localparam int          FP6_MAX_Q       = `L1_MAX(`L1_MAX(FP6_Q[0], FP6_Q[1]), FP6_Q[2]);
  localparam int unsigned FP6_MAX_Q_WIDTH = (FP6_MAX_Q > 1) ? FP6_MAX_Q : 1;
  localparam int unsigned FP6_TERM_WIDTH  = (L1Wrap && (FP6_MAX_Q_WIDTH >= L1Width)) ? L1Width :
                                            ((FP6_MAX_Q_WIDTH < L1Width) ? FP6_MAX_Q_WIDTH : L1Width) + 1;
  localparam int unsigned FP6_SUM_WIDTH   = FP6_TERM_WIDTH + $clog2(FP6_VECTOR_SIZE_GUARDED);

  // FP4 lane (FP4 source)
  localparam int          FP4_LA          = L1_CHAIN_FP4 ? L1_A[4] : `L1_MIN(L1_A[4], L1_F[4]);
  localparam int          FP4_OFFSET      = FP4_LA - 2*int'(FP4_MAN_BITS);
  localparam int          FP4_ALIGN       = L1_A[4] - FP4_LA;
  localparam int          FP4_MAX_Q       = L1_P[4] + FP4_LA;
  localparam int unsigned FP4_MAX_Q_WIDTH = (FP4_MAX_Q > 1) ? FP4_MAX_Q : 1;
  localparam int unsigned FP4_TERM_WIDTH  = (L1Wrap && (FP4_MAX_Q_WIDTH >= L1Width)) ? L1Width :
                                            ((FP4_MAX_Q_WIDTH < L1Width) ? FP4_MAX_Q_WIDTH : L1Width) + 1;
  localparam int unsigned FP4_SUM_WIDTH   = FP4_TERM_WIDTH + $clog2(FP4_VECTOR_SIZE_GUARDED);

  localparam int unsigned CHAIN_TERMS = VectorSize + (L1_CHAIN_FP6 ? FP6_VECTOR_SIZE : 0) + (L1_CHAIN_FP4 ? FP4_VECTOR_SIZE : 0);
  localparam int unsigned CHAIN_WIDTH = `L1_MAX(`L1_MAX(FP8_TERM_WIDTH, L1_CHAIN_FP6 ? FP6_TERM_WIDTH : 0),
                                                L1_CHAIN_FP4 ? FP4_TERM_WIDTH : 0);
  localparam int unsigned ALIGN_WIDTH = $clog2(int'(ANCHOR) + 1) + 1;

  // Scale: the format's L1 anchor is folded into the block scale relative to the reference anchor
  localparam int unsigned SCALE_EFF_WIDTH = SCALE_WIDTH + 2;
  localparam int          MAX_SCALE_EFF   = 2**SCALE_WIDTH - 2 + L1_MAX_ADJUST;
  localparam int          MIN_SCALE_EFF   = -(2**SCALE_WIDTH - 2);

  // Early accumulation constants
  localparam int unsigned EARLY_WINDOW    = (L1_MIN_SPARE >= 1) ? DST_PRECISION_BITS : DST_PRECISION_BITS + 1;
  localparam int unsigned EARLY_MAG_WIDTH = L1Width + DST_PRECISION_BITS + EARLY_WINDOW;
  localparam int unsigned EARLY_LZC_WIDTH = cc_pkg::idx_width(EARLY_MAG_WIDTH);
  localparam int          EARLY_ANCHOR    = L1_REF_ANCHOR + int'(EARLY_WINDOW);
  `undef L1_MAX
  `undef L1_MIN

  if (L1Width < 2 || L1Width > SOP_FIXED_WIDTH) begin
    $fatal(1, "MXDOTP requires L1Width in [2, SOP_FIXED_WIDTH], got L1Width=%0d and SOP_FIXED_WIDTH=%0d", L1Width, SOP_FIXED_WIDTH);
  end

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
  logic [2*FP6_VECTOR_SIZE_GUARDED-1:0][SRC_WIDTH-1:0] fp6_operands_post_inp_pipe;
  logic [2*FP4_VECTOR_SIZE_GUARDED-1:0][SRC_WIDTH-1:0] fp4_operands_post_inp_pipe;

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
      for (int i = 0; i < FP6_VECTOR_SIZE; i++) begin // Last FP6_VECTOR_SIZE elements use FP6 datapath
        fp6_operands_post_inp_pipe[i] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_a_q[(VectorSize*6+i*6) +: 6]};
        fp6_operands_post_inp_pipe[i+FP6_VECTOR_SIZE] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_b_q[(VectorSize*6+i*6) +: 6]};
        if (i == FP6_VECTOR_SIZE-1) begin // Last element of the FP6 remainder extends to LaneWidth+2 bits
          fp6_operands_post_inp_pipe[i][5:4] = operands_a_fp6_rem_q;
          fp6_operands_post_inp_pipe[i+FP6_VECTOR_SIZE][5:4] = operands_b_fp6_rem_q;
        end
      end
      for (int i = 0; i < VectorSize; i++) begin // First VectorSize elements use FP8 datapath
        operands_post_inp_pipe[i] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_a_q[(i*6) +: 6]};
        operands_post_inp_pipe[i+VectorSize] = {{(SRC_WIDTH-6){1'b0}}, flat_operands_b_q[(i*6) +: 6]};
      end
    end else if (src_fmt_q == fpnew_pkg::FP4) begin
      for (int i = 0; i < VectorSize; i++) begin
        if (i < FP6_VECTOR_SIZE) begin // First FP6_VECTOR_SIZE elements use FP6 datapath
          fp6_operands_post_inp_pipe[i] = {{(SRC_WIDTH-4){1'b0}}, operands_a_q[i][7:4]};
          fp6_operands_post_inp_pipe[i+FP6_VECTOR_SIZE] = {{(SRC_WIDTH-4){1'b0}}, operands_b_q[i][7:4]};
        end else begin // Last FP4_VECTOR_SIZE elements use FP4 datapath, remaining elements already use FP8 datapath via operands_post_inp_pipe
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

  fp6_src_t [FP6_VECTOR_SIZE_GUARDED-1:0] fp6_operands_a, fp6_operands_b;
  fpnew_pkg::fp_info_t [FP6_VECTOR_SIZE_GUARDED-1:0] fp6_info_a, fp6_info_b;

  fp4_src_t [FP4_VECTOR_SIZE_GUARDED-1:0] fp4_operands_a, fp4_operands_b;
  fpnew_pkg::fp_info_t [FP4_VECTOR_SIZE_GUARDED-1:0] fp4_info_a, fp4_info_b;

  fpnew_mxdotp_classifier #(
    .FpSrcFmtConfig ( FpSrcFmtConfig  ),
    .FpDstFmtConfig ( FpDstFmtConfig  ),
    .VectorSize     ( VectorSize      ),
    .FP6VectorSize  ( FP6_VECTOR_SIZE_GUARDED ),
    .FP4VectorSize  ( FP4_VECTOR_SIZE_GUARDED ),
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

  // -------------------------------------------------
  // Per-format L1 grid: shift offsets, alignment, scale
  // -------------------------------------------------
  logic signed [7:0]                 fp8_shift_offset;
  logic signed [7:0]                 fp6_shift_offset;
  logic signed [7:0]                 fp4_shift_offset;
  logic        [ALIGN_WIDTH-1:0]     fp6_align;
  logic        [ALIGN_WIDTH-1:0]     fp4_align;
  logic signed [SCALE_EFF_WIDTH-1:0] scale_adjust;
  logic signed [SCALE_EFF_WIDTH-1:0] scale_eff;

  always_comb begin : l1_format_select
    fp8_shift_offset = 8'(FP8_OFFSET[0]);
    fp6_shift_offset = 8'(FP6_OFFSET[0]);
    fp4_shift_offset = 8'(FP4_OFFSET);
    fp6_align        = ALIGN_WIDTH'(FP6_ALIGN[0]);
    fp4_align        = ALIGN_WIDTH'(FP4_ALIGN);
    scale_adjust     = SCALE_EFF_WIDTH'(L1_REF_ANCHOR - L1_A[0]);
    if (src_is_int) begin
      fp8_shift_offset = 8'(FP8_OFFSET[5]);
      scale_adjust     = SCALE_EFF_WIDTH'(L1_REF_ANCHOR - L1_A[5]);
    end else begin
      case (src_fmt_q)
        fpnew_pkg::FP8ALT: begin
          fp8_shift_offset = 8'(FP8_OFFSET[1]);
          scale_adjust     = SCALE_EFF_WIDTH'(L1_REF_ANCHOR - L1_A[1]);
        end
        fpnew_pkg::FP6: begin
          fp8_shift_offset = 8'(FP8_OFFSET[2]);
          fp6_shift_offset = 8'(FP6_OFFSET[0]);
          fp6_align        = ALIGN_WIDTH'(FP6_ALIGN[0]);
          scale_adjust     = SCALE_EFF_WIDTH'(L1_REF_ANCHOR - L1_A[2]);
        end
        fpnew_pkg::FP6ALT: begin
          fp8_shift_offset = 8'(FP8_OFFSET[3]);
          fp6_shift_offset = 8'(FP6_OFFSET[1]);
          fp6_align        = ALIGN_WIDTH'(FP6_ALIGN[1]);
          scale_adjust     = SCALE_EFF_WIDTH'(L1_REF_ANCHOR - L1_A[3]);
        end
        fpnew_pkg::FP4: begin
          fp8_shift_offset = 8'(FP8_OFFSET[4]);
          fp6_shift_offset = 8'(FP6_OFFSET[2]);
          fp6_align        = ALIGN_WIDTH'(FP6_ALIGN[2]);
          scale_adjust     = SCALE_EFF_WIDTH'(L1_REF_ANCHOR - L1_A[4]);
        end
        default: ;
      endcase
    end
  end

  assign scale_eff = SCALE_EFF_WIDTH'(scale) + scale_adjust;

  // ---------------------------------
  // Product and L1 shift data path
  // ---------------------------------
  logic signed [VectorSize-1:0][FP8_TERM_WIDTH-1:0]              fp8_term;
  logic signed [FP6_VECTOR_SIZE_GUARDED-1:0][FP6_TERM_WIDTH-1:0] fp6_term;
  logic signed [FP4_VECTOR_SIZE_GUARDED-1:0][FP4_TERM_WIDTH-1:0] fp4_term;

  if (FP8_LANES) begin : fp8_l1_lane
    fpnew_mxdotp_param_l1_lane #(
      .SrcType         ( fp_src_t        ),
      .LocalVectorSize ( VectorSize      ),
      .PrecisionBits   ( PRECISION_BITS  ),
      .ExpWidth        ( EXP_WIDTH       ),
      .MaxQWidth       ( FP8_MAX_Q_WIDTH ),
      .IntEnable       ( INT8_LANE       ),
      .L1Width         ( L1Width         ),
      .L1Wrap          ( L1Wrap          )
    ) i_fp8_l1_lane (
      .operands_a   ( operands_a       ),
      .operands_b   ( operands_b       ),
      .info_a       ( info_a           ),
      .info_b       ( info_b           ),
      .src_fmt      ( src_fmt_q        ),
      .int_fmt      ( int_fmt_q        ),
      .src_is_int   ( src_is_int       ),
      .shift_offset ( fp8_shift_offset ),
      .term         ( fp8_term         )
    );
  end else begin : no_fp8_l1_lane
    assign fp8_term = '0;
  end

  if (FP6_LANES) begin : fp6_l1_lane
    fpnew_mxdotp_param_l1_lane #(
      .SrcType         ( fp6_src_t       ),
      .LocalVectorSize ( FP6_VECTOR_SIZE ),
      .PrecisionBits   ( FP6_PREC_BITS   ),
      .ExpWidth        ( 5               ),
      .MaxQWidth       ( FP6_MAX_Q_WIDTH ),
      .IntEnable       ( 1'b0            ),
      .L1Width         ( L1Width         ),
      .L1Wrap          ( L1Wrap          )
    ) i_fp6_l1_lane (
      .operands_a   ( fp6_operands_a   ),
      .operands_b   ( fp6_operands_b   ),
      .info_a       ( fp6_info_a       ),
      .info_b       ( fp6_info_b       ),
      .src_fmt      ( src_fmt_q        ),
      .int_fmt      ( int_fmt_q        ),
      .src_is_int   ( 1'b0             ),
      .shift_offset ( fp6_shift_offset ),
      .term         ( fp6_term         )
    );
  end else begin : no_fp6_l1_lane
    assign fp6_term = '0;
  end

  if (FP4_LANES) begin : fp4_l1_lane
    fpnew_mxdotp_param_l1_lane #(
      .SrcType         ( fp4_src_t       ),
      .LocalVectorSize ( FP4_VECTOR_SIZE ),
      .PrecisionBits   ( FP4_PREC_BITS   ),
      .ExpWidth        ( 4               ),
      .MaxQWidth       ( FP4_MAX_Q_WIDTH ),
      .IntEnable       ( 1'b0            ),
      .L1Width         ( L1Width         ),
      .L1Wrap          ( L1Wrap          )
    ) i_fp4_l1_lane (
      .operands_a   ( fp4_operands_a   ),
      .operands_b   ( fp4_operands_b   ),
      .info_a       ( fp4_info_a       ),
      .info_b       ( fp4_info_b       ),
      .src_fmt      ( src_fmt_q        ),
      .int_fmt      ( int_fmt_q        ),
      .src_is_int   ( 1'b0             ),
      .shift_offset ( fp4_shift_offset ),
      .term         ( fp4_term         )
    );
  end else begin : no_fp4_l1_lane
    assign fp4_term = '0;
  end

  // --------------------
  // INP to MID pipeline
  // --------------------
  // Selected pipeline output signals as non-arrays
  logic signed [VectorSize-1:0][FP8_TERM_WIDTH-1:0]              fp8_term_q;
  logic signed [FP6_VECTOR_SIZE_GUARDED-1:0][FP6_TERM_WIDTH-1:0] fp6_term_q;
  logic signed [FP4_VECTOR_SIZE_GUARDED-1:0][FP4_TERM_WIDTH-1:0] fp4_term_q;

  // Inp-mid pipeline signals, index i holds signal after i register stages
  logic signed           [0:NUM_IM_REGS][VectorSize-1:0][FP8_TERM_WIDTH-1:0]              inp_mid_pipe_fp8_term_q;
  logic signed           [0:NUM_IM_REGS][FP6_VECTOR_SIZE_GUARDED-1:0][FP6_TERM_WIDTH-1:0] inp_mid_pipe_fp6_term_q;
  logic signed           [0:NUM_IM_REGS][FP4_VECTOR_SIZE_GUARDED-1:0][FP4_TERM_WIDTH-1:0] inp_mid_pipe_fp4_term_q;
  fpnew_pkg::fp_format_e [0:NUM_IM_REGS]                                                  inp_mid_pipe_dst_fmt_q;
  logic                  [0:NUM_IM_REGS][SCALE_EFF_WIDTH-1:0]                             inp_mid_pipe_scale_q;
  logic                  [0:NUM_IM_REGS][ALIGN_WIDTH-1:0]                                 inp_mid_pipe_fp6_align_q;
  logic                  [0:NUM_IM_REGS][ALIGN_WIDTH-1:0]                                 inp_mid_pipe_fp4_align_q;
  fp_dst_t               [0:NUM_IM_REGS]                                                  inp_mid_pipe_operand_d_q;
  fpnew_pkg::roundmode_e [0:NUM_IM_REGS]                                                  inp_mid_pipe_rnd_mode_q;
  logic                  [0:NUM_IM_REGS]                                                  inp_mid_pipe_res_is_spec_q;
  logic                  [0:NUM_IM_REGS][DST_WIDTH-1:0]                                   inp_mid_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_IM_REGS]                                                  inp_mid_pipe_spec_stat_q;
  TagType                [0:NUM_IM_REGS]                                                  inp_mid_pipe_tag_q;
  logic                  [0:NUM_IM_REGS]                                                  inp_mid_pipe_mask_q;
  AuxType                [0:NUM_IM_REGS]                                                  inp_mid_pipe_aux_q;
  logic                  [0:NUM_IM_REGS]                                                  inp_mid_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_IM_REGS]                                                                   inp_mid_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign inp_mid_pipe_fp8_term_q[0]    = fp8_term;
  assign inp_mid_pipe_fp6_term_q[0]    = fp6_term;
  assign inp_mid_pipe_fp4_term_q[0]    = fp4_term;
  assign inp_mid_pipe_dst_fmt_q[0]     = inp_pipe_dst_fmt_q[NUM_INP_REGS];
  assign inp_mid_pipe_scale_q[0]       = scale_eff;
  assign inp_mid_pipe_fp6_align_q[0]   = fp6_align;
  assign inp_mid_pipe_fp4_align_q[0]   = fp4_align;
  assign inp_mid_pipe_operand_d_q[0]   = operand_d;
  assign inp_mid_pipe_rnd_mode_q[0]    = inp_pipe_rnd_mode_q[NUM_INP_REGS];
  assign inp_mid_pipe_res_is_spec_q[0] = result_is_special;
  assign inp_mid_pipe_spec_res_q[0]    = special_result;
  assign inp_mid_pipe_spec_stat_q[0]   = special_status;
  assign inp_mid_pipe_tag_q[0]         = inp_pipe_tag_q[NUM_INP_REGS];
  assign inp_mid_pipe_mask_q[0]        = inp_pipe_mask_q[NUM_INP_REGS];
  assign inp_mid_pipe_aux_q[0]         = inp_pipe_aux_q[NUM_INP_REGS];
  assign inp_mid_pipe_valid_q[0]       = inp_pipe_valid_q[NUM_INP_REGS];
  // Input stage: Propagate pipeline ready signal to input pipe
  assign inp_pipe_ready[NUM_INP_REGS]  = inp_mid_pipe_ready[0];

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
    `FFL(inp_mid_pipe_fp8_term_q[i+1],    inp_mid_pipe_fp8_term_q[i],    reg_ena, '0)
    `FFL(inp_mid_pipe_fp6_term_q[i+1],    inp_mid_pipe_fp6_term_q[i],    reg_ena, '0)
    `FFL(inp_mid_pipe_fp4_term_q[i+1],    inp_mid_pipe_fp4_term_q[i],    reg_ena, '0)
    `FFL(inp_mid_pipe_dst_fmt_q[i+1],     inp_mid_pipe_dst_fmt_q[i],     reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_mid_pipe_scale_q[i+1],       inp_mid_pipe_scale_q[i],       reg_ena, '0)
    `FFL(inp_mid_pipe_fp6_align_q[i+1],   inp_mid_pipe_fp6_align_q[i],   reg_ena, '0)
    `FFL(inp_mid_pipe_fp4_align_q[i+1],   inp_mid_pipe_fp4_align_q[i],   reg_ena, '0)
    `FFL(inp_mid_pipe_operand_d_q[i+1],   inp_mid_pipe_operand_d_q[i],   reg_ena, '0)
    `FFL(inp_mid_pipe_rnd_mode_q[i+1],    inp_mid_pipe_rnd_mode_q[i],    reg_ena, fpnew_pkg::RNE)
    `FFL(inp_mid_pipe_res_is_spec_q[i+1], inp_mid_pipe_res_is_spec_q[i], reg_ena, '0)
    `FFL(inp_mid_pipe_spec_res_q[i+1],    inp_mid_pipe_spec_res_q[i],    reg_ena, '0)
    `FFL(inp_mid_pipe_spec_stat_q[i+1],   inp_mid_pipe_spec_stat_q[i],   reg_ena, '0)
    `FFL(inp_mid_pipe_tag_q[i+1],         inp_mid_pipe_tag_q[i],         reg_ena, TagType'('0))
    `FFL(inp_mid_pipe_mask_q[i+1],        inp_mid_pipe_mask_q[i],        reg_ena, '0)
    `FFL(inp_mid_pipe_aux_q[i+1],         inp_mid_pipe_aux_q[i],         reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign fp8_term_q = inp_mid_pipe_fp8_term_q[NUM_IM_REGS];
  assign fp6_term_q = inp_mid_pipe_fp6_term_q[NUM_IM_REGS];
  assign fp4_term_q = inp_mid_pipe_fp4_term_q[NUM_IM_REGS];

  // ------------------
  // Adder data path
  // ------------------
  logic signed [CHAIN_TERMS-1:0][CHAIN_WIDTH-1:0] chain_term;
  logic signed [L1Width-1:0]                      fp8_sum;
  logic signed [FP6_SUM_WIDTH-1:0]                fp6_sum;
  logic signed [FP4_SUM_WIDTH-1:0]                fp4_sum;
  logic signed [L1Width-1:0]                      l1_sum;

  for (genvar i = 0; i < VectorSize; i++) begin : gen_chain_fp8
    assign chain_term[i] = CHAIN_WIDTH'(signed'(fp8_term_q[i]));
  end
  if (L1_CHAIN_FP6) begin : gen_chain_fp6
    for (genvar i = 0; i < FP6_VECTOR_SIZE; i++) begin : gen_chain_fp6_term
      assign chain_term[VectorSize+i] = CHAIN_WIDTH'(signed'(fp6_term_q[i]));
    end
  end
  if (L1_CHAIN_FP4) begin : gen_chain_fp4
    for (genvar i = 0; i < FP4_VECTOR_SIZE; i++) begin : gen_chain_fp4_term
      assign chain_term[VectorSize+FP6_VECTOR_SIZE+i] = CHAIN_WIDTH'(signed'(fp4_term_q[i]));
    end
  end

  if (FP8_LANES) begin : fp8_l1_sum
    fpnew_mxdotp_l1_sum #(
      .LocalVectorSize ( CHAIN_TERMS ),
      .TermWidth       ( CHAIN_WIDTH ),
      .SumWidth        ( L1Width     ),
      .Saturate        ( L1_SAT_FP8  )
    ) i_fp8_l1_sum (
      .term ( chain_term ),
      .sum  ( fp8_sum    )
    );
  end else begin : no_fp8_l1_sum
    assign fp8_sum = '0;
  end

  if (FP6_LANES && !L1_CHAIN_FP6) begin : fp6_l1_sum
    fpnew_mxdotp_l1_sum #(
      .LocalVectorSize ( FP6_VECTOR_SIZE ),
      .TermWidth       ( FP6_TERM_WIDTH  ),
      .SumWidth        ( FP6_SUM_WIDTH   ),
      .Saturate        ( 1'b0            )
    ) i_fp6_l1_sum (
      .term ( fp6_term_q ),
      .sum  ( fp6_sum    )
    );
  end else begin : no_fp6_l1_sum
    assign fp6_sum = '0;
  end

  if (FP4_LANES && !L1_CHAIN_FP4) begin : fp4_l1_sum
    fpnew_mxdotp_l1_sum #(
      .LocalVectorSize ( FP4_VECTOR_SIZE ),
      .TermWidth       ( FP4_TERM_WIDTH  ),
      .SumWidth        ( FP4_SUM_WIDTH   ),
      .Saturate        ( 1'b0            )
    ) i_fp4_l1_sum (
      .term ( fp4_term_q ),
      .sum  ( fp4_sum    )
    );
  end else begin : no_fp4_l1_sum
    assign fp4_sum = '0;
  end

  assign l1_sum = fp8_sum + (L1Width'(fp6_sum) <<< inp_mid_pipe_fp6_align_q[NUM_IM_REGS])
                          + (L1Width'(fp4_sum) <<< inp_mid_pipe_fp4_align_q[NUM_IM_REGS]);

  // ---------------
  // Internal pipeline
  // ---------------
  // Pipeline output signals as non-arrays
  logic signed [L1Width-1:0] l1_sum_q;
  logic [SCALE_EFF_WIDTH-1:0] scale_q;
  fp_dst_t                   operand_d_q2;

  // Internal pipeline signals, index i holds signal after i register stages
  logic signed           [0:NUM_MID_REGS][L1Width-1:0]     mid_pipe_l1_sum_q;
  logic                  [0:NUM_MID_REGS][SCALE_EFF_WIDTH-1:0] mid_pipe_scale_q;
  fp_dst_t               [0:NUM_MID_REGS]                  mid_pipe_operand_d_q;
  fpnew_pkg::fp_format_e [0:NUM_MID_REGS]                  mid_pipe_dst_fmt_q;
  fpnew_pkg::roundmode_e [0:NUM_MID_REGS]                  mid_pipe_rnd_mode_q;
  logic                  [0:NUM_MID_REGS]                  mid_pipe_res_is_spec_q;
  logic                  [0:NUM_MID_REGS][DST_WIDTH-1:0]   mid_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_MID_REGS]                  mid_pipe_spec_stat_q;
  TagType                [0:NUM_MID_REGS]                  mid_pipe_tag_q;
  logic                  [0:NUM_MID_REGS]                  mid_pipe_mask_q;
  AuxType                [0:NUM_MID_REGS]                  mid_pipe_aux_q;
  logic                  [0:NUM_MID_REGS]                  mid_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_MID_REGS] mid_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign mid_pipe_l1_sum_q[0]            = l1_sum;
  assign mid_pipe_scale_q[0]             = inp_mid_pipe_scale_q[NUM_IM_REGS];
  assign mid_pipe_operand_d_q[0]         = inp_mid_pipe_operand_d_q[NUM_IM_REGS];
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
    `FFL(mid_pipe_l1_sum_q[i+1],      mid_pipe_l1_sum_q[i],      reg_ena, '0)
    `FFL(mid_pipe_scale_q[i+1],       mid_pipe_scale_q[i],       reg_ena, '0)
    `FFL(mid_pipe_operand_d_q[i+1],   mid_pipe_operand_d_q[i],   reg_ena, '0)
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
  assign l1_sum_q     = mid_pipe_l1_sum_q[NUM_MID_REGS];
  assign scale_q      = mid_pipe_scale_q[NUM_MID_REGS];
  assign operand_d_q2 = mid_pipe_operand_d_q[NUM_MID_REGS];

  // -------------------
  // Early accumulation
  // -------------------
  logic                       result_is_accumulator;
  logic                       sum_product_is_zero;
  logic                       final_sign;
  logic [EARLY_MAG_WIDTH-1:0] sum_magnitude;
  logic                       accumulator_sticky;

  fpnew_mxdotp_param_early_accumulate #(
    .SoPWidth   ( L1Width         ),
    .Anchor     ( L1_REF_ANCHOR   ),
    .Window     ( EARLY_WINDOW    ),
    .ScaleWidth ( SCALE_EFF_WIDTH )
  ) i_early_accumulate (
    .sum_product           ( l1_sum_q              ),
    .scale                 ( scale_q               ),
    .operand_d             ( operand_d_q2          ),
    .result_is_accumulator ( result_is_accumulator ),
    .sum_product_is_zero   ( sum_product_is_zero   ),
    .final_sign            ( final_sign            ),
    .sum_magnitude         ( sum_magnitude         ),
    .accumulator_sticky    ( accumulator_sticky    )
  );

  // -------------------------
  // MID to OUT EARLY pipeline
  // -------------------------
  // Pipeline output signals as non-arrays
  logic [EARLY_MAG_WIDTH-1:0] sum_magnitude_q;

  // MO-early pipeline signals, index i holds signal after i register stages
  logic                  [0:NUM_MO_EARLY_REGS][EARLY_MAG_WIDTH-1:0] mo_early_pipe_sum_magnitude_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_final_sign_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_acc_sticky_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_res_is_acc_q;
  logic                  [0:NUM_MO_EARLY_REGS]                      mo_early_pipe_sop_is_zero_q;
  logic                  [0:NUM_MO_EARLY_REGS][SCALE_EFF_WIDTH-1:0] mo_early_pipe_scale_q;
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
  assign mo_early_pipe_acc_sticky_q[0]    = accumulator_sticky;
  assign mo_early_pipe_res_is_acc_q[0]    = result_is_accumulator;
  assign mo_early_pipe_sop_is_zero_q[0]   = sum_product_is_zero;
  assign mo_early_pipe_scale_q[0]         = scale_q;
  assign mo_early_pipe_operand_d_q[0]     = operand_d_q2;
  assign mo_early_pipe_dst_fmt_q[0]       = mid_pipe_dst_fmt_q[NUM_MID_REGS];
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
    `FFL(mo_early_pipe_acc_sticky_q[i+1],    mo_early_pipe_acc_sticky_q[i],    reg_ena, '0)
    `FFL(mo_early_pipe_res_is_acc_q[i+1],    mo_early_pipe_res_is_acc_q[i],    reg_ena, '0)
    `FFL(mo_early_pipe_sop_is_zero_q[i+1],   mo_early_pipe_sop_is_zero_q[i],   reg_ena, '0)
    `FFL(mo_early_pipe_scale_q[i+1],         mo_early_pipe_scale_q[i],         reg_ena, '0)
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

  // ---------------------
  // Normalization 1: LZC
  // ---------------------
  logic [EARLY_LZC_WIDTH-1:0] leading_zero_count;
  logic                       lzc_zeroes;

  cc_lzc #(
    .Width ( EARLY_MAG_WIDTH              ),
    .Mode  ( cc_pkg::LZC_LEADING_ZERO_CNT )
  ) i_lzc (
    .in_i    ( sum_magnitude_q    ),
    .cnt_o   ( leading_zero_count ),
    .empty_o ( lzc_zeroes         )
  );

  // -------------------------
  // MID to OUT LATE pipeline
  // -------------------------
  // Pipeline output signals as non-arrays
  logic [EARLY_MAG_WIDTH-1:0] sum_magnitude_q2;
  logic [EARLY_LZC_WIDTH-1:0] leading_zero_count_q;
  logic                       lzc_zeroes_q;
  logic                       final_sign_q;
  logic                       accumulator_sticky_q;
  logic                       result_is_accumulator_q;
  logic                       sum_product_is_zero_q;
  logic [SCALE_EFF_WIDTH-1:0] scale_q2;
  fp_dst_t                    operand_d_q3;
  fpnew_pkg::fp_format_e      dst_fmt_q3;
  fpnew_pkg::roundmode_e      rnd_mode_q;
  logic                       result_is_special_q;
  logic [DST_WIDTH-1:0]       special_result_q;
  fpnew_pkg::status_t         special_status_q;

  // MO-late pipeline signals, index i holds signal after i register stages
  logic                  [0:NUM_MO_LATE_REGS][EARLY_MAG_WIDTH-1:0] mo_late_pipe_sum_magnitude_q;
  logic                  [0:NUM_MO_LATE_REGS][EARLY_LZC_WIDTH-1:0] mo_late_pipe_lzc_count_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_lzc_zeroes_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_final_sign_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_acc_sticky_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_res_is_acc_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_sop_is_zero_q;
  logic                  [0:NUM_MO_LATE_REGS][SCALE_EFF_WIDTH-1:0] mo_late_pipe_scale_q;
  fp_dst_t               [0:NUM_MO_LATE_REGS]                      mo_late_pipe_operand_d_q;
  fpnew_pkg::fp_format_e [0:NUM_MO_LATE_REGS]                      mo_late_pipe_dst_fmt_q;
  fpnew_pkg::roundmode_e [0:NUM_MO_LATE_REGS]                      mo_late_pipe_rnd_mode_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_res_is_spec_q;
  logic                  [0:NUM_MO_LATE_REGS][DST_WIDTH-1:0]       mo_late_pipe_spec_res_q;
  fpnew_pkg::status_t    [0:NUM_MO_LATE_REGS]                      mo_late_pipe_spec_stat_q;
  TagType                [0:NUM_MO_LATE_REGS]                      mo_late_pipe_tag_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_mask_q;
  AuxType                [0:NUM_MO_LATE_REGS]                      mo_late_pipe_aux_q;
  logic                  [0:NUM_MO_LATE_REGS]                      mo_late_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_MO_LATE_REGS]                                       mo_late_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign mo_late_pipe_sum_magnitude_q[0]        = sum_magnitude_q;
  assign mo_late_pipe_lzc_count_q[0]            = leading_zero_count;
  assign mo_late_pipe_lzc_zeroes_q[0]           = lzc_zeroes;
  assign mo_late_pipe_final_sign_q[0]           = mo_early_pipe_final_sign_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_acc_sticky_q[0]           = mo_early_pipe_acc_sticky_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_res_is_acc_q[0]           = mo_early_pipe_res_is_acc_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_sop_is_zero_q[0]          = mo_early_pipe_sop_is_zero_q[NUM_MO_EARLY_REGS];
  assign mo_late_pipe_scale_q[0]                = mo_early_pipe_scale_q[NUM_MO_EARLY_REGS];
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
    `FFL(mo_late_pipe_lzc_count_q[i+1],     mo_late_pipe_lzc_count_q[i],     reg_ena, '0)
    `FFL(mo_late_pipe_lzc_zeroes_q[i+1],    mo_late_pipe_lzc_zeroes_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_final_sign_q[i+1],    mo_late_pipe_final_sign_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_acc_sticky_q[i+1],    mo_late_pipe_acc_sticky_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_res_is_acc_q[i+1],    mo_late_pipe_res_is_acc_q[i],    reg_ena, '0)
    `FFL(mo_late_pipe_sop_is_zero_q[i+1],   mo_late_pipe_sop_is_zero_q[i],   reg_ena, '0)
    `FFL(mo_late_pipe_scale_q[i+1],         mo_late_pipe_scale_q[i],         reg_ena, '0)
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
  assign sum_magnitude_q2        = mo_late_pipe_sum_magnitude_q[NUM_MO_LATE_REGS];
  assign leading_zero_count_q    = mo_late_pipe_lzc_count_q[NUM_MO_LATE_REGS];
  assign lzc_zeroes_q            = mo_late_pipe_lzc_zeroes_q[NUM_MO_LATE_REGS];
  assign final_sign_q            = mo_late_pipe_final_sign_q[NUM_MO_LATE_REGS];
  assign accumulator_sticky_q    = mo_late_pipe_acc_sticky_q[NUM_MO_LATE_REGS];
  assign result_is_accumulator_q = mo_late_pipe_res_is_acc_q[NUM_MO_LATE_REGS];
  assign sum_product_is_zero_q   = mo_late_pipe_sop_is_zero_q[NUM_MO_LATE_REGS];
  assign scale_q2                = mo_late_pipe_scale_q[NUM_MO_LATE_REGS];
  assign operand_d_q3            = mo_late_pipe_operand_d_q[NUM_MO_LATE_REGS];
  assign dst_fmt_q3              = mo_late_pipe_dst_fmt_q[NUM_MO_LATE_REGS];
  assign rnd_mode_q              = mo_late_pipe_rnd_mode_q[NUM_MO_LATE_REGS];
  assign result_is_special_q     = mo_late_pipe_res_is_spec_q[NUM_MO_LATE_REGS];
  assign special_result_q        = mo_late_pipe_spec_res_q[NUM_MO_LATE_REGS];
  assign special_status_q        = mo_late_pipe_spec_stat_q[NUM_MO_LATE_REGS];

  // -------------------------------
  // Normalization 2: Shift + round
  // -------------------------------
  logic [DST_EXP_WIDTH-1:0]      final_exponent;
  logic [DST_PRECISION_BITS-1:0] final_mantissa;
  logic                          sticky_after_norm;
  logic [DST_WIDTH-1:0]          regular_result;
  fpnew_pkg::status_t            regular_status;

  fpnew_mxdotp_fixed_normalize #(
    .MagWidth   ( EARLY_MAG_WIDTH ),
    .Anchor     ( EARLY_ANCHOR    ),
    .ScaleWidth ( SCALE_EFF_WIDTH ),
    .MaxScale   ( MAX_SCALE_EFF   ),
    .MinScale   ( MIN_SCALE_EFF   )
  ) i_normalize (
    .magnitude          ( sum_magnitude_q2     ),
    .leading_zero_count ( leading_zero_count_q ),
    .lzc_zeroes         ( lzc_zeroes_q         ),
    .scale              ( scale_q2             ),
    .sticky_in          ( accumulator_sticky_q ),
    .final_exponent     ( final_exponent       ),
    .final_mantissa     ( final_mantissa       ),
    .sticky_after_norm  ( sticky_after_norm    )
  );

  fpnew_mxdotp_round #(
    .FpDstFmtConfig ( FpDstFmtConfig )
  ) i_round (
    .clk_i             ( clk_i             ),
    .rst_ni            ( rst_ni            ),
    .final_sign        ( final_sign_q      ),
    .final_exponent    ( final_exponent    ),
    .final_mantissa    ( final_mantissa    ),
    .sticky_after_norm ( sticky_after_norm ),
    .dst_fmt           ( dst_fmt_q3        ),
    .rnd_mode          ( rnd_mode_q        ),
    .result            ( regular_result    ),
    .status            ( regular_status    )
  );

  // -----------------
  // Result selection
  // -----------------
  logic [DST_WIDTH-1:0] accumulator_result;
  fpnew_pkg::status_t   accumulator_status;
  logic [DST_WIDTH-1:0] result_d;
  fpnew_pkg::status_t   status_d;

  assign accumulator_result = (FpDstFmtConfig[fpnew_pkg::FP16ALT] && (dst_fmt_q3 == fpnew_pkg::FP16ALT)) ?
                              {16'hFFFF, operand_d_q3[31:16]} : operand_d_q3;
  assign accumulator_status = '{NX: ~sum_product_is_zero_q, default: 1'b0};

  assign result_d = result_is_special_q     ? special_result_q   :
                    result_is_accumulator_q ? accumulator_result :
                                              regular_result;
  assign status_d = result_is_special_q     ? special_status_q   :
                    result_is_accumulator_q ? accumulator_status :
                                              regular_status;

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
