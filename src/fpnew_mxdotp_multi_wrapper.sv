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

module fpnew_mxdotp_multi_wrapper
  import fpnew_mxdotp_multi_pkg::*;
#(
  parameter int unsigned             LaneWidth       = 64,
  parameter int unsigned             VectorSize      = 8,
  parameter fpnew_pkg::fmt_logic_t   FpSrcFmtConfig  = '1,  // Supported FP source formats (FP8, FP8ALT, FP6, FP6ALT, FP4)
  parameter fpnew_pkg::ifmt_logic_t  IntSrcFmtConfig = '1,  // Supported INT formats (INT8)
  parameter fpnew_pkg::fmt_logic_t   FpDstFmtConfig  = '1,  // Supported FP destination formats (FP32, FP16ALT)
  parameter int unsigned             Unroll          = 8,   // Unroll factor for FP6 extended operands, possible values: 1, 2, 4, 8
  parameter int unsigned             NumPipeRegs     = 4,
  parameter fpnew_pkg::pipe_config_t PipeConfig      = fpnew_pkg::BEFORE,
  parameter type                     TagType         = logic,
  parameter type                     AuxType         = logic,
  parameter fpnew_pkg::rsr_impl_t    StochasticRndImplementation = fpnew_pkg::DEFAULT_NO_RSR,
  // Do not change
  localparam int                     OPERAND_WIDTH    = LaneWidth,
  localparam int                     UNROLL_IDX_WIDTH = (Unroll > 1) ? $clog2(Unroll) : 1,
  localparam int unsigned            NUM_OPERANDS     = 2*VectorSize+1
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
  input fpnew_pkg::int_format_e        int_fmt_i,
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

  // -----------------
  // Input processing
  // -----------------
  logic [VectorSize-1:0][SRC_WIDTH-1:0] local_src_fmt_operand_a;
  logic [VectorSize-1:0][SRC_WIDTH-1:0] local_src_fmt_operand_b;
  logic [1:0] local_src_fmt_operand_a_rem;
  logic [1:0] local_src_fmt_operand_b_rem;
  logic [1:0][SCALE_WIDTH-1:0] local_src_fmt_operand_c;
  logic [NUM_FORMATS-1:0][DST_WIDTH-1:0] local_src_fmt_operand_d;
  logic [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] local_is_boxed;
  logic [OPERAND_WIDTH-1:0] local_result;

  // -------------------------
  // Extended operands for FP6
  // -------------------------

  if (FpSrcFmtConfig[fpnew_pkg::FP6] || FpSrcFmtConfig[fpnew_pkg::FP6ALT]) begin : gen_fp6_operands

    typedef enum logic [1:0] {
      STEP0 = 2'b00,
      STEP1 = 2'b01,
      STEP2 = 2'b10
    } fp6_step_e;

    fp6_step_e step;

    // Count for the number of FP6 extended operands processed
    // Each 192b/6b = 32 FP6 operands are processed in 3 steps
    logic [$clog2(3*Unroll)-1:0] count_q, count_d;
    logic [UNROLL_IDX_WIDTH-1:0] unroll_index;

    // Store the FP6 extended operands
    logic [1:0][Unroll-1:0][3:0] local_fp6_stores_d, local_fp6_stores_q;
    logic [1:0][3:0] local_fp6_stores;

    if (Unroll > 1) begin : gen_unroll_idx
      assign unroll_index = count_q[$clog2(Unroll)-1:0];
    end else begin : gen_no_unroll
      assign unroll_index = '0;
    end

    assign step = fp6_step_e'(count_q >> $clog2(Unroll));

    always_comb begin
      count_d            = count_q;
      local_fp6_stores_d = local_fp6_stores_q;

      local_fp6_stores = '0;

      local_src_fmt_operand_a     = '0;
      local_src_fmt_operand_b     = '0;
      local_src_fmt_operand_a_rem = '0;
      local_src_fmt_operand_b_rem = '0;

      if (src_fmt_i == fpnew_pkg::FP6 || src_fmt_i == fpnew_pkg::FP6ALT) begin
        if (step == STEP0) begin
          local_src_fmt_operand_a = {4'b0000, operands_i[0][59:0]};
          local_fp6_stores[0]     = operands_i[0][63:60];
          local_src_fmt_operand_b = {4'b0000, operands_i[1][59:0]};
          local_fp6_stores[1]     = operands_i[1][63:60];
        end else if (step == STEP1) begin
          local_src_fmt_operand_a     = {operands_i[0][59:0], local_fp6_stores_q[0][unroll_index][3:0]};
          local_src_fmt_operand_a_rem = operands_i[0][61:60];
          local_fp6_stores[0]         = {2'b00, operands_i[0][63:62]};
          local_src_fmt_operand_b     = {operands_i[1][59:0], local_fp6_stores_q[1][unroll_index][3:0]};
          local_src_fmt_operand_b_rem = operands_i[1][61:60];
          local_fp6_stores[1]         = {2'b00, operands_i[1][63:62]};
        end else if (step == STEP2) begin
          local_src_fmt_operand_a     = {operands_i[0][61:0], local_fp6_stores_q[0][unroll_index][1:0]};
          local_src_fmt_operand_a_rem = operands_i[0][63:62];
          local_src_fmt_operand_b     = {operands_i[1][61:0], local_fp6_stores_q[1][unroll_index][1:0]};
          local_src_fmt_operand_b_rem = operands_i[1][63:62];
        end

        if (in_valid_i && in_ready_o) begin
          // Store the FP6 extended operands
          local_fp6_stores_d[0][unroll_index] = local_fp6_stores[0];
          local_fp6_stores_d[1][unroll_index] = local_fp6_stores[1];
          count_d = count_q + 1;
          if (count_d == 3 * Unroll) begin
            count_d = '0;
          end
        end
      end else begin
        local_src_fmt_operand_a = operands_i[0];
        local_src_fmt_operand_b = operands_i[1];
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        count_q            <= '0;
        local_fp6_stores_q <= '0;
      end else begin
        count_q            <= count_d;
        local_fp6_stores_q <= local_fp6_stores_d;
      end
    end

  end else begin : gen_no_fp6_operands
    assign local_src_fmt_operand_a     = operands_i[0];
    assign local_src_fmt_operand_b     = operands_i[1];
    assign local_src_fmt_operand_a_rem = '0;
    assign local_src_fmt_operand_b_rem = '0;
  end

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
    localparam int unsigned FP_WIDTH_DST_MIN = fpnew_pkg::minimum(DST_WIDTH, FP_WIDTH);

    always_comb begin : nanbox
      local_src_fmt_operand_d[fmt] = '1;
      local_src_fmt_operand_d[fmt][FP_WIDTH_DST_MIN-1:0] = operands_i[2][FP_WIDTH_DST_MIN-1:0];

      for (int i = 0; i < VectorSize; i++) begin
        local_is_boxed[fmt][i] = is_boxed_i[fmt][0];
        local_is_boxed[fmt][i+VectorSize] = is_boxed_i[fmt][1];
      end

      local_is_boxed[fmt][2*VectorSize] = is_boxed_i[fmt][2];
    end
  end

  fpnew_mxdotp_multi #(
    .FpSrcFmtConfig     ( FpSrcFmtConfig  ),
    .IntSrcFmtConfig    ( IntSrcFmtConfig ),
    .FpDstFmtConfig     ( FpDstFmtConfig  ),
    .LaneWidth          ( LaneWidth       ),
    .VectorSize         ( VectorSize      ),
    .NumPipeRegs        ( NumPipeRegs     ),
    .PipeConfig         ( PipeConfig      ),
    .TagType            ( TagType         ),
    .AuxType            ( AuxType         )
  ) i_fpnew_mxdotp_multi (
    .clk_i,
    .rst_ni,
    .operands_a_i ( local_src_fmt_operand_a ),
    .operands_b_i ( local_src_fmt_operand_b ),
    .operands_a_fp6_rem_i ( local_src_fmt_operand_a_rem ),
    .operands_b_fp6_rem_i ( local_src_fmt_operand_b_rem ),
    .operands_c_i ( local_src_fmt_operand_c            ),
    .operand_d_i  ( local_src_fmt_operand_d[dst_fmt_i] ),
    .is_boxed_i   ( local_is_boxed                     ),
    .rnd_mode_i,
    .op_i,
    .op_mod_i,
    .src_fmt_i, // format of the multiplicands
    .int_fmt_i, // format of the multiplicands if they are integers
    .dst_fmt_i, // format of the addend and result
    .tag_i,
    .mask_i,
    .aux_i,
    .in_valid_i,
    .in_ready_o,
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

  if (OPERAND_WIDTH > DST_WIDTH) begin
    assign local_result[OPERAND_WIDTH-1:DST_WIDTH] = '1;
  end
  assign result_o = local_result;

endmodule
