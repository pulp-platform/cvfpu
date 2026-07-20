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

// Traverses the partition tree and returns the selected bound index.
module fpnew_pace_partition #(
  parameter fpnew_pkg::fmt_logic_t    FpFmtConfig  = '1,
  parameter fpnew_pkg::pipe_config_t  PipeConfig   = fpnew_pkg::BEFORE,
  parameter type                      TagType      = logic,
  parameter type                      AuxType      = logic,
  parameter int unsigned              Bounds       = 7,
  parameter int unsigned              NumCmpStages = $clog2(Bounds),
  parameter fpnew_pkg::pace_pipe_t    PipeRegs     = '0,
  localparam fpnew_pkg::fp_encoding_t SuperFormat = fpnew_pkg::super_format(FpFmtConfig),
  localparam int unsigned             Width        = fpnew_pkg::max_fp_width(FpFmtConfig),
  localparam int unsigned             SuperWidth   = 1 + SuperFormat.man_bits + SuperFormat.exp_bits
) (
  input  logic                              clk_i,
  input  logic                              rst_ni,
  input  logic                              flush_i,
  input  logic [Bounds-1:0][SuperWidth-1:0] bounds_i,
  input  logic [Width-1:0]                  operand_i,
  output logic [Width-1:0]                  operand_o,
  input  fpnew_pkg::fp_format_e             src_fmt_i,
  output fpnew_pkg::fp_format_e dst_fmt_o,
  input  TagType                            tag_i,
  input  logic                              in_valid_i,
  output logic                              in_ready_o,
  output logic [NumCmpStages-1:0]           bound_id_o,
  output TagType                            tag_o,
  output logic                              out_valid_o,
  input  logic                              out_ready_i,
  output logic                              inflight_o,
  output logic                              busy_o
);
  // ----------------
  // Type Definitions
  // ----------------
  typedef struct packed {
    TagType tag;
    logic [NumCmpStages-1:0] bound_id;
    fpnew_pkg::fp_format_e src_fmt;
  } part_tag_t;

  // ----------------
  // Local Constants
  // ----------------
  localparam int unsigned MaxBoundsPerStage = 1 << (NumCmpStages - 1);
  localparam int unsigned LastCmpStage      = NumCmpStages - 1;

  // -----------------
  // Stage Bookkeeping
  // -----------------
  part_tag_t [NumCmpStages-1:0]                              stage_tag_in;
  part_tag_t [NumCmpStages-1:0]                              stage_tag_out;

  logic [NumCmpStages:0][SuperWidth-1:0]                     stage_probe_operand;
  logic [NumCmpStages-1:0][MaxBoundsPerStage-1:0][SuperWidth-1:0] stage_bounds;
  logic [NumCmpStages-1:0][1:0][SuperWidth-1:0]              stage_cmp_operands;
  logic [NumCmpStages-1:0][SuperWidth-1:0]                   stage_output_operand;
  logic [NumCmpStages-1:0]                                   stage_compare_result;
  logic [NumCmpStages:0]                                     stage_sel;
  logic [NumCmpStages-1:0]                                   stage_in_valid;
  logic [NumCmpStages-1:0]                                   stage_in_ready;
  logic [NumCmpStages-1:0]                                   stage_out_valid;
  logic [NumCmpStages-1:0]                                   stage_out_ready;
  logic [NumCmpStages-1:0][SuperWidth-1:0]                   stage_selected_bound;
  logic [NumCmpStages-1:0]                                   stage_busy;
  logic [NumCmpStages-1:0]                                   stage_busy_vec;
  logic [NumCmpStages-1:0][NumCmpStages-1:0]                 stage_next_bound_id;
  logic [SuperWidth-1:0]                                     super_operand_in;
  logic [SuperWidth-1:0]                                     super_operand_out;

  // ----------------
  // Top-Level Wiring
  // ----------------
  for (genvar stage = 0; stage < NumCmpStages; stage++) begin : gen_busy_vec
    assign stage_busy_vec[stage] = stage_busy[stage];
  end

  assign busy_o                 = |stage_busy_vec;
  assign inflight_o             = busy_o | out_valid_o;
  assign dst_fmt_o              = stage_tag_out[LastCmpStage].src_fmt;
  assign stage_probe_operand[0] = super_operand_in;
  assign super_operand_out      = stage_probe_operand[NumCmpStages];

  fpnew_pace_cast #(
    .FpFmtConfig(FpFmtConfig)
  ) i_input_cast (
    .operand_i(operand_i),
    .src_fmt_i(src_fmt_i),
    .result_o(super_operand_in)
  );

  fpnew_pace_decast #(
    .FpFmtConfig(FpFmtConfig)
  ) i_output_cast (
    .operand_i(super_operand_out),
    .src_fmt_i(stage_tag_out[LastCmpStage].src_fmt),
    .result_o(operand_o)
  );

  assign stage_out_ready[LastCmpStage] = out_ready_i;
  assign out_valid_o                   = stage_out_valid[LastCmpStage];
  assign in_ready_o                    = stage_in_ready[0];

  for (genvar stage = 0; stage < NumCmpStages; stage++) begin : gen_tag_flow
    localparam int unsigned StageSelIdx = (stage == 0)
        ? NumCmpStages
        : (NumCmpStages - stage + 1);
    localparam int unsigned BoundBitIdx = NumCmpStages - stage;

    assign stage_tag_in[stage].tag = (stage == 0) ? tag_i : stage_tag_out[stage-1].tag;
    assign stage_tag_in[stage].src_fmt = (stage == 0) ? src_fmt_i
                                                      : stage_tag_out[stage-1].src_fmt;
    assign stage_next_bound_id[stage] = (stage == 0)
        ? '0
        : stage_tag_out[stage-1].bound_id |
            ({{(NumCmpStages-1){1'b0}}, stage_sel[StageSelIdx]} << BoundBitIdx);
    assign stage_tag_in[stage].bound_id = stage_next_bound_id[stage];
  end

  assign tag_o      = stage_tag_out[LastCmpStage].tag;
  assign bound_id_o = stage_tag_out[LastCmpStage].bound_id |
                      {{(NumCmpStages-1){1'b0}}, stage_sel[1]};

  for (genvar stage = 0; stage < NumCmpStages; stage++) begin : gen_stages
    localparam int unsigned NumBounds     = 1 << stage;
    localparam int unsigned BoundSelWidth = NumBounds == 1 ? 1 : $clog2(NumBounds);
    localparam int unsigned StageSelIdx   = NumCmpStages - stage;

    for (genvar bound = 0; bound < NumBounds; bound++) begin : gen_bounds
      localparam int unsigned BoundIdx = NumBounds - 1 + bound;

      // Stage ordering follows the binary-search-tree layout.
      assign stage_bounds[stage][bound] = bounds_i[BoundIdx];
    end

    assign stage_in_valid[stage] = (stage == 0) ? in_valid_i : stage_out_valid[stage-1];

    if (stage < LastCmpStage) begin : gen_stage_ready
      assign stage_out_ready[stage] = stage_in_ready[stage+1];
    end

    fpnew_pace_bound_select #(
      .Bounds(NumBounds),
      .Width(SuperWidth)
    ) i_pace_bound_selector (
      .bounds_i(stage_bounds[stage][0+:NumBounds]),
      .sel_i(
        (stage == 0)
          ? BoundSelWidth'('0)
          : stage_tag_in[stage].bound_id[NumCmpStages-1-:BoundSelWidth]
      ),
      .result_o(stage_selected_bound[stage])
    );

    assign stage_cmp_operands[stage][0]   = stage_probe_operand[stage];
    assign stage_cmp_operands[stage][1]   = stage_selected_bound[stage];
    assign stage_probe_operand[stage + 1] = stage_output_operand[stage];
    assign stage_sel[StageSelIdx]         = stage_compare_result[stage];

    fpnew_pace_cmp #(
      .FpFmtConfig (FpFmtConfig),
      .PipeEnable  (PipeRegs[stage]),
      .PipeConfig  (PipeConfig),
      .TagType     (part_tag_t)
    ) i_pace_gt_cmp (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .operands_i (stage_cmp_operands[stage]),
      .operand_o  (stage_output_operand[stage]),
      .tag_i      (stage_tag_in[stage]),
      .in_valid_i (stage_in_valid[stage]),
      .in_ready_o (stage_in_ready[stage]),
      .flush_i    (flush_i),
      .result_o   (stage_compare_result[stage]),
      .tag_o      (stage_tag_out[stage]),
      .out_valid_o(stage_out_valid[stage]),
      .out_ready_i(stage_out_ready[stage]),
      .busy_o     (stage_busy[stage])
    );
  end

endmodule
