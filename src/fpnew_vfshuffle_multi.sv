// Copyright 2024 ETH Zurich and University of Bologna.
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

// Authors: Tim Fischer <fischeti@iis.ee.ethz.ch

// This unit can be used to shuffle elements of a SIMD vector with a generic mask
// Currently the unit supports two different operations:
// - SHUFFLE: Used if `op_mod_i` is *not* set. Uses only the first operand as input SIMD vector.
// - SHUFFLE2: USed if `op_mod_i` is set. Uses both operand as input SIMD vector.
//
// The operands are expected to be in the following format:
// operands_i[0]: 1st SIMD vector to shuffle
// operands_i[1]: Mask for the shuffle operation
// operands_i[2]: 2nd SIMD vector to shuffle (only used if `op_mod_i` is set)
//
// The mask only uses the LSB 4 bits of the 2nd operand:
// - Bit 3: Select between the two input vectors (only used if `op_mod_i` is set)
// - Bit 2-0: Select the element from the selected vector
//
// Pipeline registers can be inserted before and after the unit by setting the `PipeConfig` parameter.
// However, `AFTER` might be more preferable as the input operands contain the entire SIMD vector, whereas
// the output only contains the selected element. The unit should not be timing-critical,
// therefore only a single pipeline register is supported.

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

module fpnew_vfshuffle_multi #(
  parameter fpnew_pkg::fmt_logic_t   FpFmtConfig = '1,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::AFTER,
  parameter int unsigned             NumPipeRegs = 0,
  parameter int unsigned SrcWidth                = 0,
  parameter type                     TagType     = logic,
  parameter type                     AuxType     = logic,
  // Do not change
  localparam int unsigned DstWidth = fpnew_pkg::max_fp_width(FpFmtConfig)
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Input signals
  input  logic [2:0][SrcWidth-1:0]    operands_i, // 3 operands
  input  fpnew_pkg::operation_e       op_i,       // Currently only single shuffle operation
  input  logic                        op_mod_i,   // Whether to use the second operand
  input  fpnew_pkg::fp_format_e       src_fmt_i,  // format of the input operands
  input  fpnew_pkg::fp_format_e       dst_fmt_i,  // format of the output operands
  input  TagType                      tag_i,
  input  logic                        mask_i,
  input  AuxType                      aux_i,
  // Input Handshake
  input  logic                        in_valid_i,
  output logic                        in_ready_o,
  input  logic                        flush_i,
  // Output signals
  output logic [DstWidth-1:0]         result_o,
  output fpnew_pkg::status_t          status_o,
  output logic                        extension_bit_o,
  output TagType                      tag_o,
  output logic                        mask_o,
  output AuxType                      aux_o,
  // Output handshake
  output logic                        out_valid_o,
  input  logic                        out_ready_i,
  // Indication of valid data in flight
  output logic                        busy_o);

  // ---------------
  // Input registers
  // ---------------
  logic [2:0][SrcWidth-1:0]  inp_operands_q;
  fpnew_pkg::operation_e     inp_op_q;
  logic                      inp_op_mod_q;
  fpnew_pkg::fp_format_e     inp_src_fmt_q;
  fpnew_pkg::fp_format_e     inp_dst_fmt_q;
  TagType                    inp_tag_q;
  logic                      inp_mask_q;
  AuxType                    inp_aux_q;
  logic                      inp_valid_q;
  logic                      inp_ready;
  logic                      out_ready;

  // Input stage: Propagate pipeline ready signal to updtream circuitry
  assign in_ready_o = inp_ready;
  if (PipeConfig == fpnew_pkg::BEFORE && NumPipeRegs == 1) begin : gen_inp_regs
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign inp_ready = out_ready | ~inp_valid_q;
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(inp_valid_q, in_valid_i, inp_ready, flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipeline ready and a valid data item is present
    assign reg_ena = inp_ready & inp_valid_q;
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(inp_operands_q, operands_i, reg_ena, '0)
    `FFL(inp_op_q,       op_i,       reg_ena, fpnew_pkg::VFSHFL)
    `FFL(inp_op_mod_q,            op_mod_i,   reg_ena, 1'b0)
    `FFL(inp_src_fmt_q,  src_fmt_i,  reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_dst_fmt_q,  dst_fmt_i,  reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_tag_q,      tag_i,      reg_ena, TagType'('0))
    `FFL(inp_mask_q,     mask_i,     reg_ena, '0)
    `FFL(inp_aux_q,      aux_i,      reg_ena, AuxType'('0))
  end else begin : gen_no_inp_regs
    assign inp_ready = out_ready;
    assign inp_valid_q = in_valid_i;
    assign inp_operands_q = operands_i;
    assign inp_op_q = op_i;
    assign inp_op_mod_q = op_mod_i;
    assign inp_src_fmt_q = src_fmt_i;
    assign inp_dst_fmt_q = dst_fmt_i;
    assign inp_tag_q = tag_i;
    assign inp_mask_q = mask_i;
    assign inp_aux_q = aux_i;
  end

  // ----------------------
  // Mask
  // ----------------------

  logic       vec_sel;
  logic [2:0] elm_sel;

  assign vec_sel = inp_operands_q[1][3];
  assign elm_sel = inp_operands_q[1][2:0];

  // ----------------------
  // Shuffle Logic
  // ----------------------

  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][DstWidth-1:0] result;
  logic [DstWidth-1:0]                              result_out;

  for (genvar f = 0; f < fpnew_pkg::NUM_FP_FORMATS; f++) begin : gen_fmts
    // Only implement formats that are enabled
    if (FpFmtConfig[f]) begin : gen_fmt
      localparam FpWidth = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(f));
      localparam NumLanes = SrcWidth/FpWidth;
      logic [NumLanes-1:0][FpWidth-1:0] opa_vec, opb_vec;
      logic [FpWidth-1:0] opa_elm, opb_elm;
      // Convert the operands to a SIMD representation
      assign opa_vec = inp_operands_q[0];
      assign opb_vec = inp_operands_q[2];
      // Select based on element mask
      assign opa_elm = opa_vec[elm_sel[$clog2(NumLanes)-1:0]];
      assign opb_elm = opb_vec[elm_sel[$clog2(NumLanes)-1:0]];
      // Select based on vector mask and op mode
      assign result[f] = (vec_sel & inp_op_mod_q) ? opb_elm : opa_elm;
    end else begin
      assign result[f] = '0;
    end
  end

  // Select result based on destination format
  always_comb begin : gen_result
    unique case (inp_dst_fmt_q)
      fpnew_pkg::FP32: result_out = result[fpnew_pkg::FP32];
      fpnew_pkg::FP16,
      fpnew_pkg::FP16ALT: result_out = result[fpnew_pkg::FP16];
      fpnew_pkg::FP8,
      fpnew_pkg::FP8ALT: result_out = result[fpnew_pkg::FP8];
      default: result_out = '0;
    endcase
  end

  // ---------------
  // Output registers
  // ---------------
  logic [DstWidth-1:0] out_result_q;
  TagType              out_tag_q;
  logic                out_mask_q;
  AuxType              out_aux_q;
  logic                out_valid_q;

  if (PipeConfig == fpnew_pkg::AFTER && NumPipeRegs == 1) begin : gen_out_regs
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign out_ready = out_ready_i | ~out_valid_q;
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(out_valid_q, inp_valid_q, out_ready, flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    `FFL(out_result_q, result_out, reg_ena, '0)
    `FFL(out_tag_q,    inp_tag_q,  reg_ena, TagType'('0))
    `FFL(out_mask_q,   inp_mask_q, reg_ena, '0)
    `FFL(out_aux_q,    inp_aux_q,  reg_ena, AuxType'('0))
  end else begin : gen_no_out_regs
    assign out_ready = out_ready_i;
    assign out_valid_q = inp_valid_q;
    assign out_result_q = result_out;
    assign out_tag_q = inp_tag_q;
    assign out_mask_q = inp_mask_q;
    assign out_aux_q = inp_aux_q;
  end

  // Output signals
  assign result_o = out_result_q;
  assign tag_o = out_tag_q;
  assign mask_o = out_mask_q;
  assign aux_o = out_aux_q;
  assign out_valid_o = out_valid_q;
  assign status_o = fpnew_pkg::status_t'('0); // Not used
  assign extension_bit_o = 1'b0; // No NaN-boxing
  assign busy_o = inp_valid_q | out_valid_q;

  `ASSERT_INIT(ShflTooManyPipeRegs, !(NumPipeRegs > 1))

endmodule
