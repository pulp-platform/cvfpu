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

// Author: Gamze Islamoglu <gislamoglu@iis.ee.ethz.ch>

module fpnew_mxdotp_multi_wrapper #(
  parameter int unsigned             LaneWidth   = 64,
  parameter int unsigned             VectorSize  = 8,
  parameter int unsigned             NumPipeRegs = 0,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::BEFORE,
  parameter type                     TagType     = logic,
  parameter type                     AuxType     = logic,
  parameter fpnew_pkg::rsr_impl_t    StochasticRndImplementation = fpnew_pkg::DEFAULT_NO_RSR,
  // Do not change
  localparam fpnew_pkg::fmt_logic_t FpSrcFmtConfig = 6'b000101,
  localparam fpnew_pkg::fmt_logic_t FpDstFmtConfig = 6'b100000,
  localparam int                    SRC_WIDTH      = fpnew_pkg::maximum(fpnew_pkg::max_fp_width(FpSrcFmtConfig), 1),
  localparam int                    DST_WIDTH      = fpnew_pkg::maximum(fpnew_pkg::max_fp_width(FpDstFmtConfig), 1),
  localparam int                    OPERAND_WIDTH  = LaneWidth,
  localparam int unsigned           NUM_FORMATS    = fpnew_pkg::NUM_FP_FORMATS
) (
  input logic                          clk_i,
  input logic                          rst_ni,
  // Input signals
  input logic [2:0][OPERAND_WIDTH-1:0] operands_i, // 3 operands
  input logic [NUM_FORMATS-1:0][2:0]   is_boxed_i, // 3 operands
  input fpnew_pkg::roundmode_e         rnd_mode_i,
  input fpnew_pkg::operation_e         op_i,
  input logic                          op_mod_i,
  input fpnew_pkg::fp_format_e         src_fmt_i,
  input fpnew_pkg::fp_format_e         dst_fmt_i,
  input TagType                        tag_i,
  input logic                          mask_i,
  input AuxType                        aux_i,
  // Input Handshake
  input  logic                         in_valid_i,
  output logic                         in_ready_o,
  input  logic                         flush_i,
  // Output signals
  output logic [OPERAND_WIDTH-1:0]     result_o,
  output fpnew_pkg::status_t           status_o,
  output logic                         extension_bit_o,
  output TagType                       tag_o,
  output logic                         mask_o,
  output AuxType                       aux_o,
  // Output handshake
  output logic                         out_valid_o,
  input  logic                         out_ready_i,
  // Indication of valid data in flight
  output logic                         busy_o
);

  // ----------
  // Constants
  // ----------

  localparam int unsigned SCALE_WIDTH = 8;
  localparam int unsigned NUM_OPERANDS = 2*VectorSize+1; // scale is not included

  // -----------------
  // Input processing
  // -----------------
  logic [NUM_FORMATS-1:0][VectorSize-1:0][SRC_WIDTH-1:0] local_src_fmt_operand_a;
  logic [NUM_FORMATS-1:0][VectorSize-1:0][SRC_WIDTH-1:0] local_src_fmt_operand_b;
  logic [1:0][SCALE_WIDTH-1:0] local_src_fmt_operand_c;
  logic [NUM_FORMATS-1:0][DST_WIDTH-1:0] local_src_fmt_operand_d;
  logic [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] local_is_boxed;
  logic [OPERAND_WIDTH-1:0] local_result;


  // ----------------------------------
  // assign scale operands
  // ----------------------------------
  assign local_src_fmt_operand_c[1] = operands_i[2][(DST_WIDTH+SCALE_WIDTH)+:SCALE_WIDTH];
  assign local_src_fmt_operand_c[0] = operands_i[2][DST_WIDTH+:SCALE_WIDTH];

  // ----------------------------------
  // assign operands with src format
  // ----------------------------------
  // NaN-boxing check
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_nanbox

    localparam int unsigned FP_WIDTH         = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned FP_WIDTH_MIN     = fpnew_pkg::minimum(SRC_WIDTH, FP_WIDTH);
    localparam int unsigned FP_WIDTH_DST_MIN = fpnew_pkg::minimum(DST_WIDTH, FP_WIDTH);

    always_comb begin : nanbox
      // nan-box if needed
      local_src_fmt_operand_a[fmt] = '1;
      local_src_fmt_operand_b[fmt] = '1;
      local_src_fmt_operand_d[fmt] = '1;

      local_src_fmt_operand_d[fmt][FP_WIDTH_DST_MIN-1:0] = operands_i[2][FP_WIDTH_DST_MIN-1:0];

      for (int i = 0; i < VectorSize; i++) begin
        local_src_fmt_operand_a[fmt][i] = operands_i[0][i*FP_WIDTH_MIN +: FP_WIDTH_MIN];
        local_src_fmt_operand_b[fmt][i] = operands_i[1][i*FP_WIDTH_MIN +: FP_WIDTH_MIN];
        local_is_boxed[fmt][i] = is_boxed_i[fmt][0];
        local_is_boxed[fmt][i+VectorSize] = is_boxed_i[fmt][1];
      end

      local_is_boxed[fmt][2*VectorSize] = is_boxed_i[fmt][2];
    end
  end

  fpnew_mxdotp_multi #(
    .SrcDotpFpFmtConfig ( FpSrcFmtConfig ), // FP8, FP8ALT 
    .DstDotpFpFmtConfig ( FpDstFmtConfig ), // FP32
    .NumPipeRegs        ( NumPipeRegs    ),
    .PipeConfig         ( PipeConfig     ),
    .TagType            ( TagType        ),
    .AuxType            ( AuxType        )
  ) i_fpnew_mxdotp_multi (
    .clk_i,
    .rst_ni,
    .operands_a_i ( local_src_fmt_operand_a[src_fmt_i] ),
    .operands_b_i ( local_src_fmt_operand_b[src_fmt_i] ),
    .operands_c_i ( local_src_fmt_operand_c            ),
    .operand_d_i  ( local_src_fmt_operand_d[dst_fmt_i] ),
    .is_boxed_i   ( local_is_boxed                     ),
    .rnd_mode_i,
    .op_i,
    .op_mod_i,
    .src_fmt_i, // format of the multiplicands
    .dst_fmt_i, // format of the addend and result
    .tag_i,
    .mask_i,
    .aux_i,
    .in_valid_i,
    .in_ready_o ,
    .flush_i,
    .result_o     ( local_result[DST_WIDTH-1:0] ),
    .status_o,
    .extension_bit_o,
    .tag_o,
    .mask_o,
    .aux_o,
    .out_valid_o,
    .out_ready_i,
    .busy_o
  );

  if(OPERAND_WIDTH > DST_WIDTH) begin
   assign local_result[OPERAND_WIDTH-1:DST_WIDTH]  = '1;
  end
  assign result_o = local_result;

endmodule
