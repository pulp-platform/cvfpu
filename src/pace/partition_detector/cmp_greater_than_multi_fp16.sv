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

// Author: Arpan Suravi Prasad <prasadar@iis.ee.ethz.ch>

module fp_cmp_greater_than_multi_fp16
  import pace_package::*;
#(
  parameter int ManBits = 10,
  parameter int ExpBits = 8,
  localparam int OpBits = ManBits + ExpBits + 1
)
(
  input  logic [msb(OpBits):0]          operand_a_i,
  input  logic [msb(OpBits):0]          operand_b_i,
  input  pace_package::pace_fp_mode_t   fp_type_i,
  input  logic                          enable_i,
  output logic                          is_greater_o
);

  // ---------------------------------------------
  // Internal Decomposed FP Components
  // ---------------------------------------------
  logic               sign_a, sign_b;
  logic [ExpBits-1:0] exponent_a, exponent_b;
  logic [ManBits-1:0] mantissa_a, mantissa_b;
  logic               is_nan_a, is_nan_b;
  logic               is_inf_a, is_inf_b;

  logic [1:0] compare_sign, compare_exponent, compare_mantissa;

  localparam logic [1:0] Greater = 2'b01;
  localparam logic [1:0] Smaller = 2'b10;
  localparam logic [1:0] Equal   = 2'b11;

  // ---------------------------------------------
  // Extract Sign Bit
  // ---------------------------------------------
  assign sign_a = (fp_type_i == BFP16) ? operand_a_i[msb(PartitionBFP16OpBits)] :
                  (fp_type_i == FP16)  ? operand_a_i[msb(PartitionFP16OpBits)]  :
                                         operand_a_i[msb(PartitionFP8OpBits)];

  assign sign_b = (fp_type_i == BFP16) ? operand_b_i[msb(PartitionBFP16OpBits)] :
                  (fp_type_i == FP16)  ? operand_b_i[msb(PartitionFP16OpBits)]  :
                                         operand_b_i[msb(PartitionFP8OpBits)];

  // ---------------------------------------------
  // Extract and Normalize Exponent Bits
  // ---------------------------------------------
  assign exponent_a = (fp_type_i == FP16)  ? {{(ExpBits - PartitionFP16ExpBits){1'b1}}, operand_a_i[PartitionFP16OpBits-2 : PartitionFP16ManBits]} :
                      (fp_type_i == BFP16) ? {{(ExpBits - PartitionBFP16ExpBits){1'b1}}, operand_a_i[PartitionBFP16OpBits-2 : PartitionBFP16ManBits]} :
                                             {{(ExpBits - PartitionFP8ExpBits){1'b1}}, operand_a_i[PartitionFP8OpBits-2 : PartitionFP8ManBits]};

  assign exponent_b = (fp_type_i == FP16)  ? {{(ExpBits - PartitionFP16ExpBits){1'b1}}, operand_b_i[PartitionFP16OpBits-2 : PartitionFP16ManBits]} :
                      (fp_type_i == BFP16) ? {{(ExpBits - PartitionBFP16ExpBits){1'b1}}, operand_b_i[PartitionBFP16OpBits-2 : PartitionBFP16ManBits]} :
                                             {{(ExpBits - PartitionFP8ExpBits){1'b1}}, operand_b_i[PartitionFP8OpBits-2 : PartitionFP8ManBits]};

  // ---------------------------------------------
  // Extract and Normalize Mantissa Bits
  // ---------------------------------------------
  assign mantissa_a = (fp_type_i == FP16)  ? {{(ManBits - PartitionFP16ManBits){1'b0}}, operand_a_i[PartitionFP16ManBits-1 : 0]} :
                      (fp_type_i == BFP16) ? {{(ManBits - PartitionBFP16ManBits){1'b0}}, operand_a_i[PartitionBFP16ManBits-1 : 0]} :
                                             {{(ManBits - PartitionFP8ManBits){1'b0}}, operand_a_i[PartitionFP8ManBits-1 : 0]};

  assign mantissa_b = (fp_type_i == FP16)  ? {{(ManBits - PartitionFP16ManBits){1'b0}}, operand_b_i[PartitionFP16ManBits-1 : 0]} :
                      (fp_type_i == BFP16) ? {{(ManBits - PartitionBFP16ManBits){1'b0}}, operand_b_i[PartitionBFP16ManBits-1 : 0]} :
                                             {{(ManBits - PartitionFP8ManBits){1'b0}}, operand_b_i[PartitionFP8ManBits-1 : 0]};

  // ---------------------------------------------
  // Detect Special Cases (NaN & Infinity)
  // ---------------------------------------------
  assign is_nan_a = (exponent_a == {ExpBits{1'b1}}) && (mantissa_a != 0);
  assign is_nan_b = (exponent_b == {ExpBits{1'b1}}) && (mantissa_b != 0);

  assign is_inf_a = (exponent_a == {ExpBits{1'b1}}) && (mantissa_a == 0);
  assign is_inf_b = (exponent_b == {ExpBits{1'b1}}) && (mantissa_b == 0);

  // ---------------------------------------------
  // Comparator Logic
  // ---------------------------------------------
  assign compare_sign     = (sign_a < sign_b)         ? Greater :
                            (sign_a > sign_b)         ? Smaller : Equal;

  assign compare_exponent = (exponent_a > exponent_b) ? Greater :
                            (exponent_a < exponent_b) ? Smaller : Equal;

  assign compare_mantissa = (mantissa_a > mantissa_b) ? Greater :
                            (mantissa_a < mantissa_b) ? Smaller : Equal;

  // ---------------------------------------------
  // Final Greater-Than Evaluation
  // ---------------------------------------------
  assign is_greater_o = enable_i && !is_nan_a && !is_nan_b &&
    (
      (compare_sign == Greater) ||
      ((!sign_a) && (compare_sign == Equal) && (compare_exponent == Greater)) ||
      (( sign_a) && (compare_sign == Equal) && (compare_exponent == Smaller)) ||
      ((!sign_a) && (compare_sign == Equal) && (compare_exponent == Equal) && (compare_mantissa == Greater)) ||
      (( sign_a) && (compare_sign == Equal) && (compare_exponent == Equal) && (compare_mantissa == Smaller)) ||
      (is_inf_a && !is_inf_b) ||
      (!is_inf_a && is_inf_b)
    );

endmodule : fp_cmp_greater_than_multi_fp16
