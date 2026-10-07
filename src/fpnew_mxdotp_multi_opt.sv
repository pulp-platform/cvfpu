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

module fpnew_mxdotp_multi_opt (
  input  logic                    clk_i,
  input  logic                    rst_ni,
  // Input signals
  input  logic [255:0]            operands_a_i,
  input  logic [255:0]            operands_b_i,
  input  logic [1:0][7:0]         operands_c_i,
  input  logic [31:0]             operand_d_i,
  input  fpnew_pkg::roundmode_e   rnd_mode_i,
  input  fpnew_pkg::fp_format_e   src_fmt_i,
  // Input Handshake
  input  logic                    in_valid_i,
  output logic                    in_ready_o,
  input  logic                    flush_i,
  // Output signals
  output logic [31:0]             result_o,
  // Output handshake
  output logic                    out_valid_o,
  input  logic                    out_ready_i,
  // Indication of valid data in flight
  output logic                    busy_o
);

  localparam int ANCHOR               = 34;
  localparam int SOP_SHIFT            = 28;
  localparam int FP4_SOP_SHIFT        = 32;
  localparam int SUPER_DST_MAN_BITS   = 23;
  localparam int DST_PRECISION_BITS   = 24;
  localparam int FIXED_SUM_WIDTH      = 97;
  localparam int LZC_SUM_WIDTH        = 121;
  localparam int MAX_ACC_SHIFT_AMOUNT = 72;
  localparam int DST_BIAS             = 127;

  typedef struct packed {
    logic       sign;
    logic [4:0] exponent;
    logic [2:0] mantissa;
  } fp_src_t;
  typedef struct packed {
    logic       sign;
    logic [1:0] exponent;
    logic [0:0] mantissa;
  } fp4_src_t;
  typedef struct packed {
    logic        sign;
    logic [7:0]  exponent;
    logic [22:0] mantissa;
  } fp_dst_t;

  // ---------------
  // Input pipeline
  // ---------------
  logic [255:0]           operands_a_q;
  logic [255:0]           operands_b_q;
  logic [1:0][7:0]        operands_c_q;
  logic [31:0]            operand_d_q;
  fpnew_pkg::fp_format_e  src_fmt_q;
  fpnew_pkg::roundmode_e  inp_rnd_mode_q;
  logic                   inp_valid_q;
  logic                   inp_ready;
  logic                   inp_reg_ena;

  assign in_ready_o  = inp_ready | ~inp_valid_q;
  assign inp_reg_ena = in_ready_o & in_valid_i;

  `FFLARNC(inp_valid_q, in_valid_i, in_ready_o, flush_i, 1'b0, clk_i, rst_ni)
  `FFL(operands_a_q,   operands_a_i, inp_reg_ena, '0)
  `FFL(operands_b_q,   operands_b_i, inp_reg_ena, '0)
  `FFL(operands_c_q,   operands_c_i, inp_reg_ena, '0)
  `FFL(operand_d_q,    operand_d_i,  inp_reg_ena, '0)
  `FFL(src_fmt_q,      src_fmt_i,    inp_reg_ena, fpnew_pkg::fp_format_e'(0))
  `FFL(inp_rnd_mode_q, rnd_mode_i,   inp_reg_ena, fpnew_pkg::RNE)

  logic signed [31:0] src_bias;

  always_comb begin
    unique case (src_fmt_q)
      fpnew_pkg::FP8:    src_bias = 15;
      fpnew_pkg::FP8ALT: src_bias = 7;
      fpnew_pkg::FP4:    src_bias = 1;
      default:           src_bias = 15;
    endcase
  end

  // ---------------------------------------
  // Operand unpacking and classification
  // ---------------------------------------
  logic                [63:0][7:0] src_ops;
  fp_src_t             [63:0]      src_unpacked;
  fpnew_pkg::fp_info_t [63:0]      src_info;
  fp4_src_t            [63:0]      fp4_unpacked;
  fpnew_pkg::fp_info_t [63:0]      fp4_info;

  fp_src_t             [31:0]      operands_a, operands_b;
  fpnew_pkg::fp_info_t [31:0]      info_a, info_b;
  fp4_src_t            [31:0]      fp4_operands_a, fp4_operands_b;
  fpnew_pkg::fp_info_t [31:0]      fp4_info_a, fp4_info_b;
  logic signed         [1:0][7:0]  operands_c;
  fpnew_pkg::fp_info_t [1:0]       info_c;
  fp_dst_t                         operand_d;
  fpnew_pkg::fp_info_t             info_d;

  assign src_ops = {operands_b_q, operands_a_q};

  for (genvar op = 0; op < 64; op++) begin : gen_src_operands
    logic                 exp_zero, exp_ones, man_zero, man_ones, man_msb;
    fp_src_t              unpacked;
    fpnew_pkg::fp_info_t  info;

    always_comb begin : unpack_classify
      unique case (src_fmt_q)
        fpnew_pkg::FP8ALT: begin
          unpacked    = {src_ops[op][7], {1'b0, src_ops[op][6:3]}, src_ops[op][2:0]};
          exp_zero    = (src_ops[op][6:3] == '0);
          exp_ones    = (src_ops[op][6:3] == '1);
          man_zero    = (src_ops[op][2:0] == '0);
          man_ones    = (src_ops[op][2:0] == '1);
          man_msb     = src_ops[op][2];
          info        = '0;
          info.is_nan = exp_ones && man_ones;
          info.is_inf = 1'b0;
        end
        fpnew_pkg::FP4: begin
          unpacked    = {src_ops[op][3], {3'b000, src_ops[op][2:1]}, {src_ops[op][0], 2'b00}};
          exp_zero    = (src_ops[op][2:1] == '0);
          exp_ones    = (src_ops[op][2:1] == '1);
          man_zero    = (src_ops[op][0] == 1'b0);
          man_ones    = (src_ops[op][0] == 1'b1);
          man_msb     = src_ops[op][0];
          info        = '0;
          info.is_nan = 1'b0;
          info.is_inf = 1'b0;
        end
        default: begin
          unpacked    = {src_ops[op][7], src_ops[op][6:2], {src_ops[op][1:0], 1'b0}};
          exp_zero    = (src_ops[op][6:2] == '0);
          exp_ones    = (src_ops[op][6:2] == '1);
          man_zero    = (src_ops[op][1:0] == '0);
          man_ones    = (src_ops[op][1:0] == '1);
          man_msb     = src_ops[op][1];
          info        = '0;
          info.is_nan = exp_ones && !man_zero;
          info.is_inf = exp_ones && man_zero;
        end
      endcase
      info.is_boxed      = 1'b1;
      info.is_zero       = exp_zero && man_zero;
      info.is_subnormal  = exp_zero && !man_zero;
      info.is_normal     = !exp_zero && !info.is_nan && !info.is_inf;
      info.is_signalling = info.is_nan && !man_msb;
      info.is_quiet      = info.is_nan && man_msb;
    end

    assign src_unpacked[op] = unpacked;
    assign src_info[op]     = info;
    assign fp4_unpacked[op] = (src_fmt_q == fpnew_pkg::FP4) ? src_ops[op][7:4] : '0;
    assign fp4_info[op]     = '{is_normal:    (fp4_unpacked[op].exponent != '0),
                                is_zero:      (fp4_unpacked[op].exponent == '0) && (fp4_unpacked[op].mantissa == '0),
                                is_subnormal: (fp4_unpacked[op].exponent == '0) && (fp4_unpacked[op].mantissa != '0),
                                is_boxed:     1'b1,
                                default:      1'b0};
  end

  assign operands_a     = src_unpacked[31:0];
  assign operands_b     = src_unpacked[63:32];
  assign info_a         = src_info[31:0];
  assign info_b         = src_info[63:32];
  assign fp4_operands_a = fp4_unpacked[31:0];
  assign fp4_operands_b = fp4_unpacked[63:32];
  assign fp4_info_a     = fp4_info[31:0];
  assign fp4_info_b     = fp4_info[63:32];

  for (genvar i = 0; i < 2; i++) begin : gen_scales
    assign operands_c[i] = signed'(operands_c_q[i]) - 127;
    assign info_c[i]     = '{is_normal: 1'b1, is_nan: (operands_c_q[i] == 8'hff), is_boxed: 1'b1, default: 1'b0};
  end

  always_comb begin : classify_dst
    operand_d            = operand_d_q;
    info_d               = '0;
    info_d.is_boxed      = 1'b1;
    info_d.is_zero       = (operand_d_q[30:23] == '0) && (operand_d_q[22:0] == '0);
    info_d.is_subnormal  = (operand_d_q[30:23] == '0) && (operand_d_q[22:0] != '0);
    info_d.is_inf        = (operand_d_q[30:23] == '1) && (operand_d_q[22:0] == '0);
    info_d.is_nan        = (operand_d_q[30:23] == '1) && (operand_d_q[22:0] != '0);
    info_d.is_normal     = (operand_d_q[30:23] != '0) && (operand_d_q[30:23] != '1);
    info_d.is_signalling = info_d.is_nan && !operand_d_q[22];
    info_d.is_quiet      = info_d.is_nan && operand_d_q[22];
  end

  // ---------------------
  // Special case handling
  // ---------------------
  logic [31:0] special_result;
  logic        result_is_special;

  logic any_operand_inf;
  logic any_operand_nan;
  logic any_produced_nan;
  logic any_pos_inf;
  logic any_neg_inf;

  logic [31:0] operand_inf_conditions;
  logic [31:0] operand_nan_conditions;
  logic [31:0] nan_conditions;
  logic [31:0] pos_inf_conditions;
  logic [31:0] neg_inf_conditions;

  for (genvar i = 0; i < 32; i++) begin : gen_conditions
    assign operand_inf_conditions[i] = info_a[i].is_inf || info_b[i].is_inf;
    assign operand_nan_conditions[i] = info_a[i].is_nan || info_b[i].is_nan;
    assign nan_conditions[i]         = (info_a[i].is_inf && info_b[i].is_zero) ||
                                       (info_b[i].is_inf && info_a[i].is_zero);
    assign pos_inf_conditions[i]     = (info_a[i].is_inf && ~(operands_a[i].sign ^ operands_b[i].sign)) ||
                                       (info_b[i].is_inf && ~(operands_a[i].sign ^ operands_b[i].sign));
    assign neg_inf_conditions[i]     = (info_a[i].is_inf && (operands_a[i].sign ^ operands_b[i].sign)) ||
                                       (info_b[i].is_inf && (operands_a[i].sign ^ operands_b[i].sign));
  end

  assign any_operand_inf  = |operand_inf_conditions || info_d.is_inf;
  assign any_operand_nan  = |operand_nan_conditions || info_c[0].is_nan || info_c[1].is_nan || info_d.is_nan;
  assign any_produced_nan = |nan_conditions;
  assign any_pos_inf      = |pos_inf_conditions || (info_d.is_inf && ~operand_d.sign);
  assign any_neg_inf      = |neg_inf_conditions || (info_d.is_inf && operand_d.sign);

  always_comb begin : special_cases
    special_result    = 32'h7fc00000;
    result_is_special = 1'b0;
    if (any_produced_nan || any_operand_nan) begin
      result_is_special = 1'b1;
    end else if (any_operand_inf) begin
      result_is_special = 1'b1;
      if (any_pos_inf && !any_neg_inf) begin
        special_result = 32'h7f800000;
      end else if (any_neg_inf && !any_pos_inf) begin
        special_result = 32'hff800000;
      end
    end
  end

  // ------------------
  // Scale data path
  // ------------------
  logic signed [8:0] scale;

  assign scale = signed'(operands_c[0]) + signed'(operands_c[1]);

  // ------------------
  // Product data path
  // ------------------
  logic        [31:0][3:0] mantissa_a, mantissa_b;
  logic        [31:0][7:0] product;
  logic signed [31:0][8:0] product_signed;

  logic        [31:0][1:0] fp4_mantissa_a, fp4_mantissa_b;
  logic        [31:0][3:0] fp4_product;
  logic signed [31:0][4:0] fp4_product_signed;

  for (genvar i = 0; i < 32; i++) begin : gen_products
    assign mantissa_a[i]         = {info_a[i].is_normal, operands_a[i].mantissa};
    assign mantissa_b[i]         = {info_b[i].is_normal, operands_b[i].mantissa};
    assign product[i]            = mantissa_a[i] * mantissa_b[i];
    assign product_signed[i]     = (operands_a[i].sign ^ operands_b[i].sign) ? -product[i] : product[i];

    assign fp4_mantissa_a[i]     = {fp4_info_a[i].is_normal, fp4_operands_a[i].mantissa};
    assign fp4_mantissa_b[i]     = {fp4_info_b[i].is_normal, fp4_operands_b[i].mantissa};
    assign fp4_product[i]        = fp4_mantissa_a[i] * fp4_mantissa_b[i];
    assign fp4_product_signed[i] = (fp4_operands_a[i].sign ^ fp4_operands_b[i].sign) ? -fp4_product[i] : fp4_product[i];
  end

  // ------------------
  // Shift data path
  // ------------------
  logic signed [31:0][5:0]  exponent_product;
  logic signed [31:0][66:0] shifted_product;

  logic signed [31:0][2:0]  fp4_exponent_product;
  logic signed [31:0][8:0]  fp4_shifted_product;

  for (genvar i = 0; i < 32; i++) begin : gen_shifts
    assign exponent_product[i]     = operands_a[i].exponent + info_a[i].is_subnormal
                                   + operands_b[i].exponent + info_b[i].is_subnormal
                                   - 2*src_bias;
    assign shifted_product[i]      = signed'(product_signed[i]) << (SOP_SHIFT + signed'(exponent_product[i]));

    assign fp4_exponent_product[i] = fp4_operands_a[i].exponent + fp4_info_a[i].is_subnormal
                                   + fp4_operands_b[i].exponent + fp4_info_b[i].is_subnormal
                                   - 2*src_bias;
    assign fp4_shifted_product[i]  = signed'(fp4_product_signed[i]) << fp4_exponent_product[i];
  end

  // --------------------
  // INP to MID pipeline
  // --------------------
  logic signed [31:0][66:0] shifted_product_q;
  logic signed [31:0][8:0]  fp4_shifted_product_q;
  logic        [8:0]        im_scale_q;
  fp_dst_t                  im_operand_d_q;
  fpnew_pkg::fp_info_t      im_info_d_q;
  fpnew_pkg::roundmode_e    im_rnd_mode_q;
  logic                     im_res_is_spec_q;
  logic        [31:0]       im_spec_res_q;
  logic                     im_valid_q;
  logic                     im_ready;
  logic                     im_reg_ena;

  assign inp_ready  = im_ready | ~im_valid_q;
  assign im_reg_ena = inp_ready & inp_valid_q;

  `FFLARNC(im_valid_q, inp_valid_q, inp_ready, flush_i, 1'b0, clk_i, rst_ni)
  `FFL(shifted_product_q,     shifted_product,     im_reg_ena, '0)
  `FFL(fp4_shifted_product_q, fp4_shifted_product, im_reg_ena, '0)
  `FFL(im_scale_q,            scale,               im_reg_ena, '0)
  `FFL(im_operand_d_q,        operand_d,           im_reg_ena, '0)
  `FFL(im_info_d_q,           info_d,              im_reg_ena, '0)
  `FFL(im_rnd_mode_q,         inp_rnd_mode_q,      im_reg_ena, fpnew_pkg::RNE)
  `FFL(im_res_is_spec_q,      result_is_special,   im_reg_ena, '0)
  `FFL(im_spec_res_q,         special_result,      im_reg_ena, '0)

  // ------------------
  // Adder data path
  // ------------------
  logic signed [71:0] sum_product_fp8;
  logic signed [13:0] sum_product_fp4;
  logic signed [96:0] sum_product_fp4_shifted;
  logic signed [96:0] sum_product;

  always_comb begin : sum_products_fp8
    sum_product_fp8 = '0;
    for (int i = 0; i < 32; i++) begin : gen_sum_products_fp8
      sum_product_fp8 += signed'(shifted_product_q[i]);
    end
  end

  always_comb begin : sum_products_fp4
    sum_product_fp4 = '0;
    for (int i = 0; i < 32; i++) begin : gen_sum_products_fp4
      sum_product_fp4 += signed'(fp4_shifted_product_q[i]);
    end
  end

  assign sum_product_fp4_shifted = signed'(sum_product_fp4) << FP4_SOP_SHIFT;
  assign sum_product             = sum_product_fp8 + sum_product_fp4_shifted;

  // -----------------------------
  // Accumulator shift data path
  // -----------------------------
  logic                     result_is_accumulator;
  logic                     accumulator_is_right_shifted;
  logic signed [9:0]        accumulator_right_shift_amount;
  logic signed [96:0]       accumulator_shifted;
  logic signed [24:0]       signed_mantissa_d;
  logic                     accumulator_sticky;
  logic signed [23:0]       accumulator_remaining;

  logic signed [9:0]        acc_shift_amount;
  logic signed [9:0]        acc_exponent_d;
  logic        [23:0]       acc_mantissa_d;

  assign acc_exponent_d    = {1'b0, im_operand_d_q.exponent};
  assign acc_mantissa_d    = {im_info_d_q.is_normal, im_operand_d_q.mantissa};
  assign signed_mantissa_d = im_operand_d_q.sign ? -acc_mantissa_d : acc_mantissa_d;

  assign acc_shift_amount  = (ANCHOR - SUPER_DST_MAN_BITS) - signed'(im_scale_q)
                             + signed'(acc_exponent_d + im_info_d_q.is_subnormal)
                             - DST_BIAS;

  always_comb begin : accumulator_shift
    result_is_accumulator          = 1'b0;
    accumulator_is_right_shifted   = 1'b0;
    accumulator_right_shift_amount = '0;
    accumulator_remaining          = '0;
    accumulator_sticky             = 1'b0;
    if (acc_shift_amount > MAX_ACC_SHIFT_AMOUNT) begin
      accumulator_shifted   = '0;
      result_is_accumulator = 1'b1;
    end else if (acc_shift_amount >= 0) begin
      accumulator_shifted = signed'(signed_mantissa_d) <<< acc_shift_amount;
    end else begin
      accumulator_is_right_shifted   = 1'b1;
      accumulator_right_shift_amount = -acc_shift_amount;
      accumulator_shifted            = signed'(signed_mantissa_d) >>> accumulator_right_shift_amount;
      if (accumulator_right_shift_amount > DST_PRECISION_BITS) begin
        result_is_accumulator = (sum_product == '0) ? 1'b1 : 1'b0;
        accumulator_remaining = signed'(signed_mantissa_d) >>> (accumulator_right_shift_amount - DST_PRECISION_BITS);
        accumulator_sticky    = |(signed'(signed_mantissa_d) & ((1 << (accumulator_right_shift_amount - DST_PRECISION_BITS)) - 1));
      end else begin
        accumulator_remaining = signed'(signed_mantissa_d) << (DST_PRECISION_BITS - accumulator_right_shift_amount);
        accumulator_sticky    = 1'b0;
      end
    end
  end

  // -----------------
  // Accumulator + SoP
  // -----------------
  logic signed [96:0]  sum_product_accumulator;
  logic signed [120:0] sum_product_accumulator_extended;

  assign sum_product_accumulator          = sum_product + accumulator_shifted;
  assign sum_product_accumulator_extended = {sum_product_accumulator, accumulator_remaining};

  // ----------------------------------
  // Normalization 1: Two's complement
  // ----------------------------------
  logic         final_sign;
  logic [120:0] sum_magnitude;

  assign final_sign = sum_product_accumulator_extended[120];

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

  // -------------------------
  // MID to OUT EARLY pipeline
  // -------------------------
  logic [120:0]           sum_magnitude_q;
  logic                   mo_final_sign_q;
  logic [8:0]             mo_scale_q;
  logic                   mo_acc_sticky_q;
  logic                   mo_res_is_acc_q;
  fp_dst_t                mo_operand_d_q;
  fpnew_pkg::roundmode_e  mo_rnd_mode_q;
  logic                   mo_res_is_spec_q;
  logic [31:0]            mo_spec_res_q;
  logic                   mo_valid_q;
  logic                   mo_ready;
  logic                   mo_reg_ena;

  assign im_ready   = mo_ready | ~mo_valid_q;
  assign mo_reg_ena = im_ready & im_valid_q;

  `FFLARNC(mo_valid_q, im_valid_q, im_ready, flush_i, 1'b0, clk_i, rst_ni)
  `FFL(sum_magnitude_q,  sum_magnitude,         mo_reg_ena, '0)
  `FFL(mo_final_sign_q,  final_sign,            mo_reg_ena, '0)
  `FFL(mo_scale_q,       im_scale_q,            mo_reg_ena, '0)
  `FFL(mo_acc_sticky_q,  accumulator_sticky,    mo_reg_ena, '0)
  `FFL(mo_res_is_acc_q,  result_is_accumulator, mo_reg_ena, '0)
  `FFL(mo_operand_d_q,   im_operand_d_q,        mo_reg_ena, '0)
  `FFL(mo_rnd_mode_q,    im_rnd_mode_q,         mo_reg_ena, fpnew_pkg::RNE)
  `FFL(mo_res_is_spec_q, im_res_is_spec_q,      mo_reg_ena, '0)
  `FFL(mo_spec_res_q,    im_spec_res_q,         mo_reg_ena, '0)

  // ---------------------
  // Normalization 2: LZC
  // ---------------------
  logic        [6:0] leading_zero_count;
  logic signed [7:0] leading_zero_count_sgn;
  logic              lzc_zeroes;

  cc_lzc #(
    .Width ( LZC_SUM_WIDTH                ),
    .Mode  ( cc_pkg::LZC_LEADING_ZERO_CNT )
  ) i_lzc (
    .in_i    ( sum_magnitude_q    ),
    .cnt_o   ( leading_zero_count ),
    .empty_o ( lzc_zeroes         )
  );

  assign leading_zero_count_sgn = signed'({1'b0, leading_zero_count});

  // -------------------------------------------
  // Normalization 3: Shift + mantissa assembly
  // -------------------------------------------
  logic        [23:0]  final_mantissa;
  logic signed [9:0]   final_exponent;
  logic                sticky_after_norm;

  logic signed [9:0]   final_tentative_exponent;
  logic        [8:0]   norm_shamt;
  logic signed [9:0]   normalized_exponent;

  logic        [120:0] sum_shifted;
  logic        [96:0]  sum_sticky_bits;

  assign final_tentative_exponent = DST_BIAS - (ANCHOR - signed'(mo_scale_q))
                                    + (FIXED_SUM_WIDTH - leading_zero_count_sgn - 1);

  always_comb begin : norm_shift_amount
    if (final_tentative_exponent > 0 && !lzc_zeroes) begin
      norm_shamt          = leading_zero_count_sgn + 1;
      normalized_exponent = final_tentative_exponent;
    end else begin
      norm_shamt          = leading_zero_count_sgn + final_tentative_exponent;
      normalized_exponent = '0;
    end
  end

  assign sum_shifted = sum_magnitude_q << norm_shamt;

  assign {final_mantissa, sum_sticky_bits} = sum_shifted;
  assign final_exponent                    = normalized_exponent;
  assign sticky_after_norm                 = (|sum_sticky_bits) | mo_acc_sticky_q;

  // ----------------------------
  // Rounding and classification
  // ----------------------------
  logic        of_before_round;
  logic [30:0] pre_round_abs;
  logic [1:0]  round_sticky_bits;
  logic        round_up;
  logic [30:0] rounded_abs;
  logic [31:0] regular_result;

  assign of_before_round   = final_exponent >= 255;
  assign pre_round_abs     = {(of_before_round ? 8'd254      : final_exponent[7:0]),
                              (of_before_round ? 23'h7fffff  : final_mantissa[23:1])};
  assign round_sticky_bits = {final_mantissa[0] | of_before_round, sticky_after_norm | of_before_round};

  always_comb begin : rounding_decision
    unique case (mo_rnd_mode_q)
      fpnew_pkg::RNE:
        unique case (round_sticky_bits)
          2'b00,
          2'b01: round_up = 1'b0;
          2'b10: round_up = pre_round_abs[0];
          2'b11: round_up = 1'b1;
        endcase
      fpnew_pkg::RTZ: round_up = 1'b0;
      fpnew_pkg::RDN: round_up = (|round_sticky_bits) ? mo_final_sign_q  : 1'b0;
      fpnew_pkg::RUP: round_up = (|round_sticky_bits) ? ~mo_final_sign_q : 1'b0;
      fpnew_pkg::RMM: round_up = round_sticky_bits[1];
      fpnew_pkg::ROD: round_up = ~pre_round_abs[0] & (|round_sticky_bits);
      default:        round_up = fpnew_pkg::DONT_CARE;
    endcase
  end

  assign rounded_abs    = pre_round_abs + round_up;
  assign regular_result = {mo_final_sign_q, rounded_abs};

  // -----------------
  // Result selection
  // -----------------
  logic [31:0] result_d;

  assign result_d = mo_res_is_spec_q ? mo_spec_res_q :
                    (mo_res_is_acc_q ? mo_operand_d_q : regular_result);

  // ----------------
  // Output Pipeline
  // ----------------
  logic [31:0] out_result_q;
  logic        out_valid_q;
  logic        out_reg_ena;

  assign mo_ready    = out_ready_i | ~out_valid_q;
  assign out_reg_ena = mo_ready & mo_valid_q;

  `FFLARNC(out_valid_q, mo_valid_q, mo_ready, flush_i, 1'b0, clk_i, rst_ni)
  `FFL(out_result_q, result_d, out_reg_ena, '0)

  assign result_o    = out_result_q;
  assign out_valid_o = out_valid_q;
  assign busy_o      = in_valid_i | inp_valid_q | im_valid_q | mo_valid_q | out_valid_q;

endmodule : fpnew_mxdotp_multi_opt