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

// Expands the selected input format into the shared super format.
module fpnew_pace_cast #(
  parameter fpnew_pkg::fmt_logic_t   FpFmtConfig   = '1,
  localparam int unsigned            Width         = fpnew_pkg::max_fp_width(FpFmtConfig),
  localparam fpnew_pkg::fp_encoding_t SuperFormat  = fpnew_pkg::super_format(FpFmtConfig),
  localparam int unsigned            NumFormats    = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned            SuperExpBits  = SuperFormat.exp_bits,
  localparam int unsigned            SuperManBits  = SuperFormat.man_bits,
  localparam int unsigned            SuperWidth    = 1 + SuperFormat.man_bits + SuperFormat.exp_bits
) (
  input logic [Width-1:0]            operand_i,
  input fpnew_pkg::fp_format_e       src_fmt_i,
  output logic [SuperWidth-1:0]      result_o
);

  logic [NumFormats-1:0]                    fmt_sign;
  logic [NumFormats-1:0][SuperManBits-1:0]  fmt_mantissa;
  logic [NumFormats-1:0][SuperExpBits-1:0]  fmt_exponent;

  for (genvar fmt = 0; fmt < int'(NumFormats); fmt++) begin : gen_fmt_init_inputs
    localparam int unsigned FpWidth = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ExpBits = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ManBits = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned ExpDiff = SuperExpBits - ExpBits;
    localparam int unsigned ManDiff = SuperManBits - ManBits;

    if (FpFmtConfig[fmt]) begin : gen_active_format
      assign fmt_sign[fmt] = operand_i[FpWidth-1];
      // Smaller formats reuse the super-format exponent width by sign-extending the exponent field.
      assign fmt_exponent[fmt] = ExpDiff > 0
          ? {{ExpDiff{1'b1}}, operand_i[ManBits+:ExpBits]}
          : operand_i[ManBits+:ExpBits];
      assign fmt_mantissa[fmt] = ManDiff > 0
          ? {{ManDiff{1'b0}}, operand_i[0+:ManBits]}
          : operand_i[0+:ManBits];
    end else begin : gen_inactive_format
      assign fmt_sign[fmt]     = fpnew_pkg::DONT_CARE;
      assign fmt_exponent[fmt] = '{default: fpnew_pkg::DONT_CARE};
      assign fmt_mantissa[fmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  assign result_o = {fmt_sign[src_fmt_i], fmt_exponent[src_fmt_i], fmt_mantissa[src_fmt_i]};

endmodule
