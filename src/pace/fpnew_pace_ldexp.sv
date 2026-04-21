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

// Restores the scaled result back into the selected floating-point format.
module fpnew_pace_ldexp #(
  parameter fpnew_pkg::fmt_logic_t    FpFmtConfig  = '1,
  localparam fpnew_pkg::fp_encoding_t SuperFormat = fpnew_pkg::super_format(FpFmtConfig),
  localparam int unsigned             Width       = fpnew_pkg::max_fp_width(FpFmtConfig),
  localparam int unsigned             NumFormats  = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned             SuperExpBits = SuperFormat.exp_bits,
  localparam int unsigned             SuperManBits = SuperFormat.man_bits,
  localparam int unsigned             SuperWidth   = 1 + SuperFormat.man_bits
                                                        + SuperFormat.exp_bits
) (
  input  fpnew_pkg::fp_format_e src_fmt_i,
  input  logic                  pace_op_i,
  input  logic                  op_inv_i,
  input  logic                  op_sqrt_i,
  input  logic                  op_rsqrt_i,
  input  logic                  lt_eps_i,
  input  logic [Width-1:0]      operand_i,
  input  logic [Width-1:0]      eps_val_i,
  input  logic [SuperExpBits-1:0] exponent_i,
  input  logic                  sign_i,
  output logic [Width-1:0]      operand_o
);

  logic [NumFormats-1:0]                   fmt_sign;
  logic [NumFormats-1:0][SuperManBits-1:0] fmt_mantissa;
  logic [NumFormats-1:0][SuperExpBits-1:0] fmt_exponent;
  logic [NumFormats-1:0][Width-1:0]        fmt_operand;

  logic inv_sqrt_op;
  logic sqrt_op;

  assign inv_sqrt_op = pace_op_i & (op_inv_i | op_sqrt_i | op_rsqrt_i);
  assign sqrt_op     = pace_op_i & op_sqrt_i;

  // Re-encode the scaled result into the selected destination format.
  for (genvar fmt = 0; fmt < int'(NumFormats); fmt++) begin : gen_fmt_outputs
    localparam int unsigned FpWidth = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ExpBits = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ManBits = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpFmtConfig[fmt]) begin : gen_active_format
      assign fmt_sign[fmt]     = inv_sqrt_op ? sign_i : operand_i[FpWidth-1];
      assign fmt_mantissa[fmt] = operand_i[0+:ManBits];
      assign fmt_exponent[fmt] = sqrt_op
                               ? operand_i[ManBits+:ExpBits] + exponent_i[0+:ExpBits]
                               : inv_sqrt_op
                                   ? operand_i[ManBits+:ExpBits] - exponent_i[0+:ExpBits]
                                   : operand_i[ManBits+:ExpBits];

      if (FpWidth < Width) begin : gen_narrow_format
        assign fmt_operand[fmt] = {
            {(Width - FpWidth){1'b0}},
            fmt_sign[fmt],
            fmt_exponent[fmt][ExpBits-1:0],
            fmt_mantissa[fmt][ManBits-1:0]
        };
      end else begin : gen_wide_format
        assign fmt_operand[fmt] = {
            fmt_sign[fmt],
            fmt_exponent[fmt][ExpBits-1:0],
            fmt_mantissa[fmt][ManBits-1:0]
        };
      end
    end else begin : gen_inactive_format
      assign fmt_sign[fmt]     = fpnew_pkg::DONT_CARE;
      assign fmt_exponent[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_mantissa[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_operand[fmt]  = '0;
    end
  end

  assign operand_o = lt_eps_i ? {sign_i, eps_val_i[Width-2:0]}
                                  : fmt_operand[src_fmt_i];

endmodule
