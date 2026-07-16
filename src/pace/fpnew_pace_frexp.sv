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

// Author: Arpan Suravi Prasad <prasadar@iis.ee.ethz.ch>

// Extracts exponent metadata and prepares a range-reduced operand for PACE modes.
module fpnew_pace_frexp #(
  parameter fpnew_pkg::fmt_logic_t    FpFmtConfig  = '1,
  parameter type                      FrexpInfoType = logic,
  localparam fpnew_pkg::fp_encoding_t SuperFormat = fpnew_pkg::super_format(FpFmtConfig),
  localparam int unsigned             Width        = fpnew_pkg::max_fp_width(FpFmtConfig),
  localparam int unsigned             NumFormats   = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned             SuperExpBits = SuperFormat.exp_bits,
  localparam int unsigned             SuperManBits = SuperFormat.man_bits,
  localparam int unsigned             SuperWidth   = 1 + SuperFormat.man_bits + SuperFormat.exp_bits
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  fpnew_pkg::fp_format_e src_fmt_i,
  input  fpnew_pkg::operation_e op_i,
  input  logic [SuperWidth-1:0] eps_i,
  input  logic [Width-1:0]      operand_i,
  output logic [Width-1:0]      operand_o,
  output FrexpInfoType          frexp_info_o
);

  logic inv_op, sqrt_op, rsqrt_op;
  assign inv_op   = (op_i == fpnew_pkg::PACE_INV);
  assign sqrt_op  = (op_i == fpnew_pkg::PACE_SQRT);
  assign rsqrt_op = (op_i == fpnew_pkg::PACE_RSQRT);

  logic                                    lt_eps;
  logic [NumFormats-1:0]                   fmt_sign;
  logic [NumFormats-1:0][SuperManBits-1:0] fmt_mantissa;
  logic [NumFormats-1:0][SuperExpBits-1:0] fmt_exponent;
  logic [NumFormats-1:0][SuperExpBits-1:0] fmt_bias;

  logic [SuperExpBits:0]                unbiased_exponent;
  logic [SuperExpBits-1:0]              pace_exponent;
  logic [SuperExpBits-1:0]              adjusted_exponent;

  logic [NumFormats-1:0][SuperWidth-1:0] fmt_pace_operand;

  // Extract each enabled format and rebuild it in the shared super format.
  for (genvar fmt = 0; fmt < int'(NumFormats); fmt++) begin : gen_fmt_init_inputs
    localparam int unsigned FpWidth = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ExpBits = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ManBits = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned FpBias  = fpnew_pkg::bias(fpnew_pkg::fp_format_e'(fmt));

    if (FpFmtConfig[fmt]) begin : gen_active_format
      assign fmt_sign[fmt]     = operand_i[FpWidth-1];
      assign fmt_mantissa[fmt] = operand_i[0+:ManBits];
      assign fmt_exponent[fmt] = operand_i[ManBits+:ExpBits];
      assign fmt_bias[fmt]     = FpBias;

      if (FpWidth < Width) begin : gen_narrow_format
        assign fmt_pace_operand[fmt] = {
            {(Width-FpWidth){1'b0}},
            1'b0,
            pace_exponent[0+:ExpBits],
            fmt_mantissa[fmt][0+:ManBits]
        };
      end else begin : gen_wide_format
        assign fmt_pace_operand[fmt] = {
            1'b0,
            pace_exponent[0+:ExpBits],
            fmt_mantissa[fmt][0+:ManBits]
        };
      end
    end else begin : gen_inactive_format
      assign fmt_bias[fmt]     = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_sign[fmt]     = fpnew_pkg::DONT_CARE;
      assign fmt_exponent[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_mantissa[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_pace_operand[fmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Extract the exponent term that downstream PACE stages consume.
  assign unbiased_exponent = {1'b0, fmt_exponent[src_fmt_i]} - fmt_bias[src_fmt_i];
  assign pace_exponent     = inv_op ? fmt_bias[src_fmt_i]
                           : (sqrt_op | rsqrt_op) ? fmt_bias[src_fmt_i] + unbiased_exponent[0]
                           : fmt_exponent[src_fmt_i];
  assign adjusted_exponent = inv_op ? unbiased_exponent
                           : (unbiased_exponent - unbiased_exponent[0]) >> 1;

  assign operand_o = fmt_pace_operand[src_fmt_i];

  // Compare operand magnitude against epsilon in super format.
  logic [1:0][SuperWidth-1:0] sfmt_cmp_operand;
  logic [SuperWidth-1:0]      sfmt_operand;

  assign sfmt_cmp_operand[1] = {1'b0, sfmt_operand[0+:SuperWidth-1]};
  assign sfmt_cmp_operand[0] = eps_i;

  fpnew_pace_cast #(
    .FpFmtConfig(FpFmtConfig)
  ) i_pace_ldcast (
    .operand_i,
    .src_fmt_i,
    .result_o(sfmt_operand)
  );

  fpnew_pace_cmp #(
    .FpFmtConfig(FpFmtConfig)
  ) i_eps_cmp (
    .clk_i,
    .rst_ni,
    .operands_i ( sfmt_cmp_operand ),
    .operand_o  (),
    .tag_i      ( 1'b0 ),
    .in_valid_i ( 1'b1 ),
    .in_ready_o (),
    .flush_i    ( 1'b0 ),
    .result_o   ( lt_eps ),
    .tag_o      (),
    .out_valid_o (),
    .out_ready_i ( 1'b1 ),
    .busy_o     ()
  );

  assign frexp_info_o.inv      = inv_op;
  assign frexp_info_o.sqrt     = sqrt_op;
  assign frexp_info_o.rsqrt    = rsqrt_op;
  assign frexp_info_o.exponent = adjusted_exponent;
  assign frexp_info_o.sign     = fmt_sign[src_fmt_i];
  assign frexp_info_o.lt_eps   = lt_eps & (inv_op | sqrt_op | rsqrt_op);

endmodule
