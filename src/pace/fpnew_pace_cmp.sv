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

`include "common_cells/registers.svh"

// Compares two super-format operands and optionally pipelines the result.
module fpnew_pace_cmp #(
  parameter fpnew_pkg::fmt_logic_t    FpFmtConfig  = '1,
  parameter logic                     PipeEnable       = 1'b0,
  parameter fpnew_pkg::pipe_config_t  PipeConfig   = fpnew_pkg::BEFORE,
  parameter type                      TagType      = logic,
  parameter type                      AuxType      = logic,
  localparam fpnew_pkg::fp_encoding_t SuperFormat = fpnew_pkg::super_format(FpFmtConfig),
  localparam int unsigned             SuperExpBits = SuperFormat.exp_bits,
  localparam int unsigned             SuperManBits = SuperFormat.man_bits,
  localparam int unsigned             SuperWidth   = 1 + SuperFormat.man_bits + SuperFormat.exp_bits
) (
  input logic [1:0][SuperWidth-1:0] operands_i,
  output logic [SuperWidth-1:0]     operand_o,
  input logic                       clk_i,
  input logic                       rst_ni,
  input TagType                     tag_i,
  input logic                       in_valid_i,
  output logic                      in_ready_o,
  input logic                       flush_i,
  output logic                      result_o,
  output TagType                    tag_o,
  output logic                      out_valid_o,
  input logic                       out_ready_i,
  output logic                      busy_o
);

  localparam int unsigned NumInpRegs = (PipeConfig == fpnew_pkg::BEFORE)  ? PipeEnable : 0;
  localparam int unsigned NumOutRegs = (PipeConfig == fpnew_pkg::AFTER
                                     || PipeConfig == fpnew_pkg::INSIDE) ? PipeEnable : 0;

  typedef struct packed {
    logic                    sign;
    logic [SuperExpBits-1:0] exponent;
    logic [SuperManBits-1:0] mantissa;
  } fp_t;

  // Input pipeline.
  logic [1:0][SuperWidth-1:0] inp_pipe_operands_q [NumInpRegs+1];
  TagType                     inp_pipe_tag_q      [NumInpRegs+1];
  logic                       inp_pipe_valid_q    [NumInpRegs+1];
  logic                       inp_pipe_ready      [NumInpRegs+1];
  logic                       inp_pipe_reg_ena    [NumInpRegs > 0 ? NumInpRegs : 1];
  logic [NumInpRegs:0]        inp_pipe_valid_vec;

  assign inp_pipe_operands_q[0] = operands_i;
  assign inp_pipe_tag_q[0]      = tag_i;
  assign inp_pipe_valid_q[0]    = in_valid_i;
  assign in_ready_o             = inp_pipe_ready[0];

  for (genvar i = 0; i < NumInpRegs; i++) begin : gen_input_pipeline
    assign inp_pipe_ready[i] = inp_pipe_ready[i+1] | ~inp_pipe_valid_q[i+1];
    `FFLARNC(
        inp_pipe_valid_q[i+1],
        inp_pipe_valid_q[i],
        inp_pipe_ready[i],
        flush_i,
        1'b0,
        clk_i,
        rst_ni
    )
    assign inp_pipe_reg_ena[i] = inp_pipe_ready[i] & inp_pipe_valid_q[i];

    `FFL(inp_pipe_operands_q[i+1], inp_pipe_operands_q[i], inp_pipe_reg_ena[i], '0)
    `FFL(inp_pipe_tag_q[i+1],      inp_pipe_tag_q[i],      inp_pipe_reg_ena[i], TagType'('0))
  end

  fp_t operand_a, operand_b;
  logic result_d;

  assign operand_a = inp_pipe_operands_q[NumInpRegs][0];
  assign operand_b = inp_pipe_operands_q[NumInpRegs][1];
  assign result_d  = (operand_a == operand_b) ? 1'b0
                    : (operand_a > operand_b) ^ (operand_a.sign || operand_b.sign);

  // Output pipeline.
  fp_t    out_pipe_operand_q [NumOutRegs+1];
  logic   out_pipe_result_q  [NumOutRegs+1];
  TagType out_pipe_tag_q     [NumOutRegs+1];
  logic   out_pipe_valid_q   [NumOutRegs+1];
  logic   out_pipe_ready     [NumOutRegs+1];
  logic   out_pipe_reg_ena   [NumOutRegs > 0 ? NumOutRegs : 1];
  logic [NumOutRegs:0]       out_pipe_valid_vec;

  assign out_pipe_result_q[0]  = result_d;
  assign out_pipe_operand_q[0] = operand_a;
  assign out_pipe_tag_q[0]     = inp_pipe_tag_q[NumInpRegs];
  assign out_pipe_valid_q[0]   = inp_pipe_valid_q[NumInpRegs];
  assign inp_pipe_ready[NumInpRegs] = out_pipe_ready[0];

  for (genvar i = 0; i < NumOutRegs; i++) begin : gen_output_pipeline
    assign out_pipe_ready[i]   = out_pipe_ready[i+1] | ~out_pipe_valid_q[i+1];
    assign out_pipe_reg_ena[i] = out_pipe_ready[i] & out_pipe_valid_q[i];
    `FFLARNC(
        out_pipe_valid_q[i+1],
        out_pipe_valid_q[i],
        out_pipe_ready[i],
        flush_i,
        1'b0,
        clk_i,
        rst_ni
    )
    `FFL(out_pipe_result_q[i+1],  out_pipe_result_q[i],  out_pipe_reg_ena[i], '0)
    `FFL(out_pipe_operand_q[i+1], out_pipe_operand_q[i], out_pipe_reg_ena[i], '0)
    `FFL(out_pipe_tag_q[i+1],     out_pipe_tag_q[i],     out_pipe_reg_ena[i], TagType'('0))
  end

  for (genvar i = 0; i <= NumInpRegs; i++) begin : gen_inp_valid_vec
    assign inp_pipe_valid_vec[i] = inp_pipe_valid_q[i];
  end

  for (genvar i = 0; i <= NumOutRegs; i++) begin : gen_out_valid_vec
    assign out_pipe_valid_vec[i] = out_pipe_valid_q[i];
  end

  assign out_pipe_ready[NumOutRegs] = out_ready_i;
  assign result_o    = out_pipe_result_q[NumOutRegs];
  assign operand_o   = out_pipe_operand_q[NumOutRegs];
  assign tag_o       = out_pipe_tag_q[NumOutRegs];
  assign out_valid_o = out_pipe_valid_q[NumOutRegs];
  assign busy_o      = |inp_pipe_valid_vec | |out_pipe_valid_vec;
endmodule
