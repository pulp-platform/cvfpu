// Copyright 2019 ETH Zurich and University of Bologna.
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

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module fpnew_opgroup_multifmt_slice #(
  parameter fpnew_pkg::opgroup_e      OpGroup        = fpnew_pkg::CONV,
  parameter int unsigned              Width          = 64,
  // FPU configuration
  parameter fpnew_pkg::fmt_logic_t     FpFmtConfig    = '1,
  parameter fpnew_pkg::ifmt_logic_t    IntFmtConfig   = '1,
  parameter fpnew_pkg::fmt_logic_t     MxFpFmtConfig  = '0,  // MX-specific FP formats
  parameter fpnew_pkg::ifmt_logic_t    MxIntFmtConfig = '0,  // MX-specific INT formats
  parameter fpnew_pkg::fmt_unit_types_t FmtUnitTypes  = '{default: fpnew_pkg::MERGED},
  parameter logic                      EnableVectors  = 1'b1,
  parameter logic                      EnableSlotSelect = 1'b1,
  parameter logic                      EnableMXConv   = 1'b1,
  parameter fpnew_pkg::divsqrt_unit_t  DivSqrtSel     = fpnew_pkg::THMULTI,
  parameter int unsigned               NumPipeRegs    = 0,
  parameter fpnew_pkg::pipe_config_t   PipeConfig     = fpnew_pkg::BEFORE,
  parameter fpnew_pkg::pace_features_t PaceFeatures   = '{default: 0},
  parameter type                       TagType        = logic,
  parameter fpnew_pkg::rsr_impl_t      StochasticRndImplementation = fpnew_pkg::DEFAULT_NO_RSR,
  // Do not change
  localparam int unsigned NUM_OPERANDS = fpnew_pkg::num_operands(OpGroup),
  localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned NUM_SIMD_LANES = fpnew_pkg::max_num_lanes(Width, FpFmtConfig, EnableVectors),
  localparam type         MaskType     = logic [NUM_SIMD_LANES-1:0],
  localparam fpnew_pkg::fmt_logic_t PaceFmtConfig = PaceFeatures.FmtConfig,
  localparam int unsigned PaceParamWidth = PaceFeatures.PaceParamWidth,
  localparam int unsigned PaceParamMsb   = (PaceParamWidth > 0) ? (PaceParamWidth - 1) : 0

) (
  input logic                                     clk_i,
  input logic                                     rst_ni,
  input logic [31:0]                              hart_id_i,
  // Input signals
  input logic [NUM_OPERANDS-1:0][Width-1:0]       operands_i,
  input logic [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] is_boxed_i,
  input fpnew_pkg::roundmode_e                    rnd_mode_i,
  input fpnew_pkg::operation_e                    op_i,
  input logic                                     op_mod_i,
  input fpnew_pkg::fp_format_e                    src_fmt_i,
  input fpnew_pkg::fp_format_e                    dst_fmt_i,
  input fpnew_pkg::int_format_e                   int_fmt_i,
  input logic                                     vectorial_op_i,
  input TagType                                   tag_i,
  input MaskType                                  simd_mask_i,
  input  logic [PaceParamMsb:0]                   pace_param_i,
  input  fpnew_pkg::pace_mode_t                   pace_mode_i,
  // Input Handshake
  input  logic                                    in_valid_i,
  output logic                                    in_ready_o,
  input  logic                                    flush_i,
  // Output signals
  output logic [Width-1:0]                        result_o,
  output fpnew_pkg::status_t                      status_o,
  output logic                                    extension_bit_o,
  output TagType                                  tag_o,
  // Output handshake
  output logic                                    out_valid_o,
  input  logic                                    out_ready_i,
  // Indication of valid data in flight
  output logic                                    busy_o
);

  localparam fpnew_pkg::fmt_logic_t MERGED_FP_FORMATS =
      fpnew_pkg::get_merged_formats(FmtUnitTypes, FpFmtConfig);   // mask disable fmt from opgroup cfg


  if ((OpGroup == fpnew_pkg::DIVSQRT)) begin
    if ((DivSqrtSel == fpnew_pkg::TH32) && !((MERGED_FP_FORMATS[0] == 1) && (MERGED_FP_FORMATS[1:NUM_FORMATS-1] == '0))) begin
      $fatal(1, "T-Head-based DivSqrt unit supported only in FP32-only configurations. \
Set DivSqrtSel = THMULTI or DivSqrtSel = PULP to use a multi-format divider");
    end else if ((DivSqrtSel == fpnew_pkg::THMULTI) && (MERGED_FP_FORMATS[3] == 1'b1 || MERGED_FP_FORMATS[5] == 1'b1)) begin
      $warning("The DivSqrt unit of C910 (instantiated by DivSqrtSel = THMULTI) does not support \
FP8, FP8alt. Please use the PULP DivSqrt unit when in need of div/sqrt operations on FP8, FP8alt.");
    end
  end

  if ((OpGroup == fpnew_pkg::DOTP) &&
      !(MERGED_FP_FORMATS[0] && (MERGED_FP_FORMATS[2] || MERGED_FP_FORMATS[4]) && (MERGED_FP_FORMATS[3] || MERGED_FP_FORMATS[5]))) begin
    $fatal(1, "SDOTP only supported on 32b and 64b CVFPU instances in which at \
least one 16b and one 8b format are supported. \
The SDOTP operations compute on 8b inputs producing 16b outputs \
or on 16b inputs producing 32b outputs");
  end

  if (OpGroup == fpnew_pkg::MXDOTP) begin
    if (Width != 64) begin
      $fatal(1, "MXDOTP only supported on 64b CVFPU instances, got Width=%0d", Width);
    end else if (!FpFmtConfig[fpnew_pkg::FP32]) begin
      $fatal(1, "MXDOTP requires FP32 to be enabled as a destination format. Please enable FP32 in FpFmtConfig");
    end else if (!MxFpFmtConfig[fpnew_pkg::FP8]) begin
      $fatal(1, "MXDOTP requires FP8 to be enabled as a source format. Please enable FP8 in MxFpFmtConfig.");
    end
  end

  localparam int unsigned MAX_FP_WIDTH   = fpnew_pkg::max_fp_width(MERGED_FP_FORMATS);
  localparam int unsigned MAX_INT_WIDTH  = fpnew_pkg::max_int_width(IntFmtConfig);
  localparam int unsigned NUM_LANES = fpnew_pkg::max_num_lanes(Width, MERGED_FP_FORMATS, 1'b1);
  localparam int unsigned NUM_DIVSQRT_LANES = fpnew_pkg::num_divsqrt_lanes(Width, MERGED_FP_FORMATS, 1'b1, DivSqrtSel);
  localparam int unsigned NUM_DOTP_LANES = fpnew_pkg::num_dotp_lanes(Width, MERGED_FP_FORMATS);
  localparam int unsigned NUM_MX_LANES = fpnew_pkg::num_mxdotp_lanes(Width, MxFpFmtConfig, MxIntFmtConfig);
  localparam int unsigned NUM_CONV_LANES = fpnew_pkg::num_conv_lanes(Width, MERGED_FP_FORMATS, IntFmtConfig, MxFpFmtConfig, MxIntFmtConfig);
  localparam int unsigned NUM_INT_FORMATS = fpnew_pkg::NUM_INT_FORMATS;
  // We will send the format information along with the data
  localparam int unsigned FMT_BITS =
      fpnew_pkg::maximum($clog2(NUM_FORMATS), $clog2(NUM_INT_FORMATS));
  localparam int unsigned AUX_BITS = FMT_BITS + 4; // also add vectorial and integer flags

  localparam int unsigned SELECTOR_BASE = 32;      // position of selector in op2
  localparam int unsigned SELECTOR_WIDTH = 4;
  localparam int unsigned INSERT_NUM_SLOTS = 16;   // max parallelism

  typedef enum logic [1:0] {
    INSERT_NONE = 2'b00,
    INSERT_FP   = 2'b01,
    INSERT_INT  = 2'b10,
    INSERT_BYTE = 2'b11
  } insert_kind_e;


  logic [NUM_LANES-1:0] lane_in_ready, lane_out_valid, divsqrt_done, divsqrt_ready; // Handshake signals for the lanes
  logic                 vectorial_op;
  logic [FMT_BITS-1:0]  dst_fmt; // destination format to pass along with operation
  logic [AUX_BITS-1:0]  aux_data;

  // additional flags for CONV
  logic       dst_fmt_is_int, dst_is_cpk;
  logic [1:0] dst_vec_op; // info for vectorial results (for packing)
  logic [1:0] target_aux_d;
  logic       is_up_cast, is_down_cast, mxi_is_up_cast, fi_is_up_cast;

  logic [SELECTOR_WIDTH-1:0] slot_select_imm;
  logic                     target_is_insert_d;
  logic [2:0]               target_insert_nlanes_idx_d;
  insert_kind_e             target_insert_kind_d;


  logic [NUM_FORMATS-1:0][Width-1:0]      fmt_slice_result;
  logic [NUM_INT_FORMATS-1:0][Width-1:0]  ifmt_slice_result;
  logic [NUM_FORMATS-1:0][3:0][Width-1:0] fmt_conv_cpk_result;


  logic [Width-1:0] conv_target_d, conv_target_q; // vectorial conversions update a register

  fpnew_pkg::status_t [NUM_LANES-1:0]   lane_status;
  logic   [NUM_LANES-1:0]               lane_ext_bit; // only the first one is actually used
  TagType [NUM_LANES-1:0]               lane_tags; // only the first one is actually used
  logic   [NUM_LANES-1:0]               lane_masks;
  logic   [NUM_LANES-1:0][AUX_BITS-1:0] lane_aux; // only the first one is actually used
  logic   [NUM_LANES-1:0]               lane_busy; // dito

  logic                result_is_vector, result_is_vsum, op_is_vsum;
  logic [FMT_BITS-1:0] result_fmt;
  logic                result_fmt_is_int, result_is_cpk;
  logic [1:0]          result_vec_op; // info for vectorial results (for packing)
  logic                result_is_insert;
  logic [2:0]          result_insert_nlanes_idx;
  logic [SELECTOR_WIDTH-1:0] result_insert_slot;
  insert_kind_e        result_insert_kind;
  logic [Width-1:0]    insert_result;
  logic [7:0]          mxscale_scale_byte;

  logic simd_synch_rdy, simd_synch_done;
  fpnew_pkg::roundmode_e rnd_mode;

  // -----------
  // Input Side
  // -----------
  // RSR supported only on SDOTP module
  assign rnd_mode = (rnd_mode_i == fpnew_pkg::RSR) ? fpnew_pkg::RNE : rnd_mode_i;

  assign in_ready_o   = lane_in_ready[0]; // Upstream ready is given by first lane
  assign vectorial_op = vectorial_op_i & EnableVectors; // only do vectorial stuff if enabled

  // Cast-and-Pack ops are encoded in operation and modifier
  assign dst_fmt_is_int = (OpGroup == fpnew_pkg::CONV) &
                          (op_i == fpnew_pkg::F2I || op_i == fpnew_pkg::F2MI);

  assign dst_is_cpk     = (OpGroup == fpnew_pkg::CONV) & (op_i == fpnew_pkg::CPKAB ||
                                                          op_i == fpnew_pkg::CPKCD);
  assign dst_vec_op     = {2{(OpGroup == fpnew_pkg::CONV)}} & {(op_i == fpnew_pkg::CPKCD), op_mod_i};

  assign is_up_cast     = fpnew_pkg::fp_width_gt(dst_fmt_i, src_fmt_i);
  assign is_down_cast   = fpnew_pkg::fp_width_gt(src_fmt_i, dst_fmt_i);
  assign mxi_is_up_cast = fpnew_pkg::fp_width_gt_int(dst_fmt_i, int_fmt_i);
  assign fi_is_up_cast  = fpnew_pkg::int_width_gt_fp(int_fmt_i, src_fmt_i);
  assign op_is_vsum   = op_i == fpnew_pkg::VSUM ? 1'b1 : 1'b0;

  if (EnableSlotSelect) begin : gen_slot_select_enabled
    assign slot_select_imm = operands_i[2][SELECTOR_BASE +: SELECTOR_WIDTH];     // extract selector
  end else begin : gen_slot_select_disabled
    assign slot_select_imm = '0;
  end


  // The destination format is the int format for F2I casts
  assign dst_fmt    = dst_fmt_is_int ? int_fmt_i : dst_fmt_i;

  // The data sent along consists of the vectorial flag and format bits
  assign aux_data      = {dst_is_cpk, dst_fmt_is_int, vectorial_op, dst_fmt, op_is_vsum};
  assign target_aux_d  = dst_vec_op;

  always_comb begin : conv_target_insert_ctrl
    automatic int unsigned src_lanes;

    target_is_insert_d         = 1'b0;
    target_insert_nlanes_idx_d = fpnew_pkg::op0_nlanes_idx(1);
    target_insert_kind_d       = INSERT_NONE;

    unique case (op_i)
      fpnew_pkg::F2M: begin
        src_lanes = fpnew_pkg::num_lanes(Width, src_fmt_i, vectorial_op);
        target_is_insert_d         = 1'b1;
        target_insert_nlanes_idx_d = fpnew_pkg::op0_nlanes_idx(src_lanes);
        target_insert_kind_d       = INSERT_FP;
      end
      fpnew_pkg::F2MI: begin
        src_lanes = fpnew_pkg::num_lanes(Width, src_fmt_i, vectorial_op);
        target_is_insert_d         = 1'b1;
        target_insert_nlanes_idx_d = fpnew_pkg::op0_nlanes_idx(src_lanes);
        target_insert_kind_d       = INSERT_INT;
      end
      fpnew_pkg::FNF: begin
        if (!is_up_cast) begin
          src_lanes = fpnew_pkg::num_lanes(Width, src_fmt_i, 1'b1);
          target_is_insert_d         = 1'b1;
          target_insert_nlanes_idx_d = fpnew_pkg::op0_nlanes_idx(src_lanes);
          target_insert_kind_d       = INSERT_FP;
        end
      end
      fpnew_pkg::MXSCALE,
      fpnew_pkg::MXISCALE: begin
        target_is_insert_d         = 1'b1;
        target_insert_nlanes_idx_d = fpnew_pkg::op0_nlanes_idx(1);
        target_insert_kind_d       = INSERT_BYTE;
      end
      default: begin
      end
    endcase
  end


  // CONV passes one operand for assembly after the unit: opC for cpk, opB for others
  if (OpGroup == fpnew_pkg::CONV) begin : conv_target
    assign conv_target_d = dst_is_cpk ? operands_i[2] : operands_i[1];
  end else begin : not_conv_target
    assign conv_target_d = '0;
  end

  // For 2-operand units, prepare boxing info
  logic [NUM_FORMATS-1:0]      is_boxed_1op;
  logic [NUM_FORMATS-1:0][1:0] is_boxed_2op;

  always_comb begin : boxed_2op
    for (int fmt = 0; fmt < NUM_FORMATS; fmt++) begin
      is_boxed_1op[fmt] = is_boxed_i[fmt][0];
      is_boxed_2op[fmt] = is_boxed_i[fmt][1:0];
    end
  end

  // ---------------
  // Generate Lanes
  // ---------------
  localparam int unsigned PaceMaxDataWidth = fpnew_pkg::max_fp_width(PaceFmtConfig);
  localparam fpnew_pkg::fp_encoding_t PaceSuperFmt = fpnew_pkg::super_format(PaceFmtConfig);
  localparam int unsigned PaceMaxManWidth = PaceSuperFmt.man_bits;
  for (genvar lane = 0; lane < int'(NUM_LANES); lane++) begin : gen_num_lanes
    localparam int unsigned LANE = unsigned'(lane); // unsigned to please the linter
    // Get a mask of active formats for this lane
    localparam fpnew_pkg::fmt_logic_t ACTIVE_FORMATS =
        fpnew_pkg::get_lane_formats(Width, MERGED_FP_FORMATS, LANE);
    localparam fpnew_pkg::ifmt_logic_t ACTIVE_INT_FORMATS =
        fpnew_pkg::get_lane_int_formats(Width, MERGED_FP_FORMATS, IntFmtConfig, LANE);
    localparam int unsigned MAX_WIDTH = fpnew_pkg::max_fp_width(ACTIVE_FORMATS);
    localparam fpnew_pkg::fmt_logic_t PaceActiveFormats =
        fpnew_pkg::get_pace_lane_formats(ACTIVE_FORMATS, PaceFmtConfig);
    localparam int unsigned EnablePace = (PaceActiveFormats != 0);
    // Cast-specific parameters
    localparam fpnew_pkg::fmt_logic_t CONV_FORMATS =
        fpnew_pkg::get_conv_lane_formats(Width, MERGED_FP_FORMATS, LANE);
    localparam fpnew_pkg::ifmt_logic_t CONV_INT_FORMATS =
        fpnew_pkg::get_conv_lane_int_formats(Width, MERGED_FP_FORMATS, IntFmtConfig, LANE);
    localparam fpnew_pkg::fmt_logic_t CONV_MX_FORMATS =
        fpnew_pkg::get_conv_lane_formats(Width, MxFpFmtConfig, LANE);
    localparam fpnew_pkg::ifmt_logic_t CONV_MX_INT_FORMATS =
        fpnew_pkg::get_conv_lane_int_formats(Width, MxFpFmtConfig, MxIntFmtConfig, LANE);
    localparam fpnew_pkg::fmt_logic_t CONV_ALL_FORMATS = CONV_FORMATS | CONV_MX_FORMATS;
    localparam fpnew_pkg::ifmt_logic_t CONV_ALL_INT_FORMATS = CONV_INT_FORMATS | CONV_MX_INT_FORMATS;
    localparam int unsigned CONV_WIDTH = fpnew_pkg::maximum(
        fpnew_pkg::max_fp_width(CONV_ALL_FORMATS),
        fpnew_pkg::maximum(fpnew_pkg::max_int_width(CONV_ALL_INT_FORMATS),
                             fpnew_pkg::MX_SCALE_WIDTH));



    // Dotp-specific parameters
    localparam fpnew_pkg::fmt_logic_t DOTP_FORMATS =
        fpnew_pkg::get_dotp_lane_formats(Width, MERGED_FP_FORMATS, LANE);
    localparam int unsigned DOTP_MAX_FMT_WIDTH = fpnew_pkg::max_fp_width(DOTP_FORMATS);
    localparam int unsigned DOTP_WIDTH = fpnew_pkg::minimum(2*DOTP_MAX_FMT_WIDTH, Width);

    // MXDOTP-specific parameters
    localparam fpnew_pkg::lane_formats_t MXDOTP_FORMATS =
        fpnew_pkg::get_mxdotp_formats(Width, FpFmtConfig, MxFpFmtConfig, MxIntFmtConfig, LANE);
    localparam fpnew_pkg::fmt_logic_t MXDOTP_FP_FORMATS =
        MXDOTP_FORMATS.src_fp_formats;
    localparam fpnew_pkg::ifmt_logic_t MXDOTP_INT_FORMATS =
        MXDOTP_FORMATS.src_int_formats;
    localparam fpnew_pkg::fmt_logic_t MXDOTP_DST_FORMATS =
        MXDOTP_FORMATS.dst_fp_formats;
    localparam int unsigned MXDOTP_WIDTH = Width; // Only one MXDOTP lane, processing the whole vector

    // Lane parameters from Opgroup
    localparam fpnew_pkg::fmt_logic_t LANE_FORMATS = (OpGroup == fpnew_pkg::CONV) ? CONV_FORMATS :
                                                     (OpGroup == fpnew_pkg::DOTP) ? DOTP_FORMATS :
                                                                                    ACTIVE_FORMATS;
    localparam int unsigned LANE_WIDTH = (OpGroup == fpnew_pkg::CONV) ? CONV_WIDTH :
                                         (OpGroup == fpnew_pkg::DOTP) ? DOTP_WIDTH :
                                         (OpGroup == fpnew_pkg::MXDOTP) ? MXDOTP_WIDTH : MAX_WIDTH;

    logic [LANE_WIDTH-1:0] local_result; // lane-local results

    // Generate instances only if needed, lane 0 always generated
    if ((lane == 0) || (EnableVectors & (!(OpGroup == fpnew_pkg::DOTP && (lane >= NUM_DOTP_LANES))
                                        && !(OpGroup == fpnew_pkg::DIVSQRT && (lane >= NUM_DIVSQRT_LANES))
                                         && !(OpGroup == fpnew_pkg::MXDOTP && (lane >= NUM_MX_LANES))
                                         && !(OpGroup == fpnew_pkg::CONV && (lane >= NUM_CONV_LANES))
                                         ))) begin : active_lane
      logic in_valid, out_valid, out_ready; // lane-local handshake

      logic [NUM_OPERANDS-1:0][LANE_WIDTH-1:0] local_operands;  // lane-local oprands
      logic [LANE_WIDTH-1:0]                   op_result;       // lane-local results
      fpnew_pkg::status_t                      op_status;

      logic lane_is_used;
      if (OpGroup == fpnew_pkg::CONV) begin : gen_conv_connections
        logic conv_is_up_cast;
        logic conv_src_lane_is_used;
        always_comb begin : conv_lane_activity
          unique case (op_i)
            fpnew_pkg::I2F: begin
              conv_is_up_cast = mxi_is_up_cast;
              conv_src_lane_is_used = CONV_INT_FORMATS[int_fmt_i];
            end
            fpnew_pkg::MI2F: begin
              conv_is_up_cast = mxi_is_up_cast;
              conv_src_lane_is_used = CONV_MX_INT_FORMATS[int_fmt_i];
            end
            fpnew_pkg::F2I: begin
              conv_is_up_cast = fi_is_up_cast;
              conv_src_lane_is_used = LANE_FORMATS[src_fmt_i];
            end
            fpnew_pkg::F2MI: begin
              conv_is_up_cast = fi_is_up_cast;
              conv_src_lane_is_used = LANE_FORMATS[src_fmt_i];
            end
            fpnew_pkg::MXSCALE,
            fpnew_pkg::MXISCALE: begin
              conv_is_up_cast       = 1'b0;
              conv_src_lane_is_used = (LANE == 0) & CONV_ALL_FORMATS[src_fmt_i];
            end
            default: begin
              conv_is_up_cast = is_up_cast;
              conv_src_lane_is_used = LANE_FORMATS[src_fmt_i];
            end
          endcase
        end
        always_comb begin : conv_lane_used
          if (!conv_is_up_cast) begin
            lane_is_used = conv_src_lane_is_used;
          end else begin
            unique case (op_i)
              fpnew_pkg::F2I:  lane_is_used = CONV_INT_FORMATS[int_fmt_i];
              fpnew_pkg::F2MI: lane_is_used = CONV_MX_INT_FORMATS[int_fmt_i];
              default:         lane_is_used = LANE_FORMATS[dst_fmt_i];
            endcase
          end
        end
      end else begin : gen_nonconv_connections
        assign lane_is_used = (LANE_FORMATS[src_fmt_i] & ~is_up_cast) |
                              (LANE_FORMATS[dst_fmt_i] &  is_up_cast) |
                              (OpGroup == fpnew_pkg::DIVSQRT) | (OpGroup == fpnew_pkg::MXDOTP);
      end
      assign in_valid = in_valid_i & ((lane == 0) | vectorial_op) & lane_is_used; // upper lanes only for vectors

      fpnew_pkg::op0_window_t op0_window_sel;                                           // instantiated selection logic
      logic [2:0] src_widx;
      logic [2:0] int_widx;
      logic [2:0] dst_nidx;
      logic [4:0] subgroup_sel;
      fpnew_pkg::op0_window_table_t op0_window_table;
      fpnew_pkg::op0_width_table_t  op0_f2f_upper_table;

      assign src_widx     = fpnew_pkg::op0_width_idx(fpnew_pkg::fp_width(src_fmt_i));
      assign int_widx     = fpnew_pkg::op0_width_idx(fpnew_pkg::int_width(int_fmt_i));
      assign dst_nidx     = fpnew_pkg::op0_nlanes_idx(
          fpnew_pkg::num_lanes(Width, dst_fmt_i, 1'b1));
      assign subgroup_sel = {1'b0, slot_select_imm};

      for (genvar widx = 0; widx < fpnew_pkg::OP0_NUM_WIDTHS; widx++) begin : gen_op0_widths
        localparam int unsigned W = fpnew_pkg::op0_idx_to_width(widx);
        localparam int unsigned F2F_UPPER_BASE = LANE * W + (Width / 2);
        for (genvar f2f_b = 0; f2f_b < fpnew_pkg::OP0_WINDOW_MAX_WIDTH; f2f_b++) begin : gen_op0_f2f_upper_bits
          if (f2f_b < LANE_WIDTH && (F2F_UPPER_BASE + f2f_b) < Width) begin
            assign op0_f2f_upper_table[widx][f2f_b] = operands_i[0][F2F_UPPER_BASE + f2f_b];
          end else begin
            assign op0_f2f_upper_table[widx][f2f_b] = 1'b0;
          end
        end
        for (genvar nidx = 0; nidx < fpnew_pkg::OP0_NUM_NLANES; nidx++) begin : gen_op0_nlanes
          localparam int unsigned N = fpnew_pkg::op0_idx_to_nlanes(nidx);
          for (genvar sg = 0; sg < fpnew_pkg::OP0_NUM_SUBGROUPS; sg++) begin : gen_op0_subgroups
            localparam int unsigned BASE = (LANE + sg * N) * W;
            for (genvar b = 0; b < fpnew_pkg::OP0_WINDOW_MAX_WIDTH; b++) begin : gen_op0_bits
              if (b < LANE_WIDTH && (BASE + b) < Width) begin
                assign op0_window_table[widx][nidx][sg][b] = operands_i[0][BASE + b];    // nested mux construction
              end else begin
                assign op0_window_table[widx][nidx][sg][b] = 1'b0;
              end
            end
          end
        end
      end


      // Slice out the operands for this lane, upper bits are ignored in the unit
      if (EnableSlotSelect) begin : gen_prepare_input_slot_select
      always_comb begin : prepare_input
        op0_window_sel = '0;
        for (int unsigned i = 0; i < NUM_OPERANDS; i++) begin
          local_operands[i] = operands_i[i] >> LANE*fpnew_pkg::fp_width(src_fmt_i);
        end

        if (OpGroup == fpnew_pkg::DOTP) begin
          for (int unsigned i = 0; i < NUM_OPERANDS; i++) begin
            if (i == 2) begin
              local_operands[i] = operands_i[i] >> LANE*fpnew_pkg::fp_width(dst_fmt_i); // expanded format the width of dst_fmt
            end else begin
              local_operands[i] = operands_i[i] >> LANE*2*fpnew_pkg::fp_width(src_fmt_i); // twice the width of src_fmt
            end
          end
        end else if (OpGroup == fpnew_pkg::CONV) begin
          local_operands[1] = operands_i[1];
          local_operands[2] = operands_i[2];
          op0_window_sel = fpnew_pkg::pick_op0_window(
              op0_window_table, src_widx, 3'd0, 5'd0);
          local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];    // mux recall

          if (op_i == fpnew_pkg::I2F) begin                     // special cases
            op0_window_sel = fpnew_pkg::pick_op0_window(
                op0_window_table, int_widx, 3'd0, 5'd0);
            local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
          end else if (op_i == fpnew_pkg::M2F) begin
            if (EnableMXConv && vectorial_op && (slot_select_imm != '0) && is_up_cast) begin
              op0_window_sel = fpnew_pkg::pick_op0_window(
                  op0_window_table, src_widx, dst_nidx, subgroup_sel);
              local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
            end
          end else if (op_i == fpnew_pkg::MI2F) begin
            op0_window_sel = fpnew_pkg::pick_op0_window(
                op0_window_table, int_widx, 3'd0, 5'd0);
            local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
            if (EnableMXConv && vectorial_op && (slot_select_imm != '0) && mxi_is_up_cast) begin
              op0_window_sel = fpnew_pkg::pick_op0_window(
                  op0_window_table, int_widx, dst_nidx, subgroup_sel);
              local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
            end
          // vectorial F2F up casts
          end else if (op_i == fpnew_pkg::F2F) begin
            if (vectorial_op && op_mod_i && is_up_cast) begin
              op0_window_sel = fpnew_pkg::pick_op0_width_window(
                  op0_f2f_upper_table, src_widx);
              local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
            end
          end else if (op_i == fpnew_pkg::FNF) begin
            if (vectorial_op && (slot_select_imm != '0) && is_up_cast) begin
              op0_window_sel = fpnew_pkg::pick_op0_window(
                  op0_window_table, src_widx, dst_nidx, subgroup_sel);
              local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
            end
          // CPK
          end else if (dst_is_cpk) begin
            if (lane == 1) begin
              local_operands[0] = operands_i[1];
            end
          end
        end
      end
      end else begin : gen_prepare_input_slot0_only
      always_comb begin : prepare_input
        op0_window_sel = '0;
        for (int unsigned i = 0; i < NUM_OPERANDS; i++) begin
          local_operands[i] = operands_i[i] >> LANE*fpnew_pkg::fp_width(src_fmt_i);
        end

        if (OpGroup == fpnew_pkg::DOTP) begin
          for (int unsigned i = 0; i < NUM_OPERANDS; i++) begin
            if (i == 2) begin
              local_operands[i] = operands_i[i] >> LANE*fpnew_pkg::fp_width(dst_fmt_i);
            end else begin
              local_operands[i] = operands_i[i] >> LANE*2*fpnew_pkg::fp_width(src_fmt_i);
            end
          end
        end else if (OpGroup == fpnew_pkg::CONV) begin
          local_operands[1] = operands_i[1];
          local_operands[2] = operands_i[2];
          op0_window_sel = fpnew_pkg::pick_op0_window(
              op0_window_table, src_widx, 3'd0, 5'd0);
          local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];

          if (op_i == fpnew_pkg::I2F || op_i == fpnew_pkg::MI2F) begin
            op0_window_sel = fpnew_pkg::pick_op0_window(
                op0_window_table, int_widx, 3'd0, 5'd0);
            local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
          end else if (op_i == fpnew_pkg::F2F) begin
            if (vectorial_op && op_mod_i && is_up_cast) begin
              op0_window_sel = fpnew_pkg::pick_op0_width_window(
                  op0_f2f_upper_table, src_widx);
              local_operands[0] = op0_window_sel[LANE_WIDTH-1:0];
            end
          end else if (dst_is_cpk) begin
            if (lane == 1) begin
              local_operands[0] = operands_i[1];
            end
          end
        end
      end
      end


      // Instantiate the operation from the selected opgroup
      if (OpGroup == fpnew_pkg::ADDMUL) begin : gen_lane_instance
        if (EnablePace) begin : gen_pace_instance
          localparam fpnew_pkg::pace_features_t PaceLaneFeatures = '{
            PaceDegree      : PaceFeatures.PaceDegree,
            PaceParts       : PaceFeatures.PaceParts,
            PaceEps         : PaceFeatures.PaceEps,
            PaceDataWidth   : PaceFeatures.PaceDataWidth,
            PaceParamWidth  : PaceFeatures.PaceParamWidth,
            PaceBstPipeRegs : PaceFeatures.PaceBstPipeRegs,
            FmtConfig       : PaceActiveFormats
          };

          fpnew_pace_fma_multi #(
            .FpFmtConfig ( LANE_FORMATS         ),
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           ),
            .TagType     ( TagType              ),
            .AuxType     ( logic [AUX_BITS-1:0] ),
            .PaceFeat    ( PaceLaneFeatures     ),
            .PaceDataW   ( PaceMaxDataWidth     ),
            .PaceManOff  ( PaceMaxManWidth      )
          ) i_fpnew_pace_fma_multi (
            .clk_i,
            .rst_ni,
            .operands_i      ( local_operands  ),
            .is_boxed_i,
            .rnd_mode_i      ( rnd_mode        ),
            .op_i            ( op_i            ),
            .op_mod_i,
            .src_fmt_i,
            .dst_fmt_i,
            .pace_param_i,
            .pace_mode_i,
            .tag_i,
            .mask_i          ( simd_mask_i[lane]   ),
            .aux_i           ( aux_data            ),
            .in_valid_i      ( in_valid            ),
            .in_ready_o      ( lane_in_ready[lane] ),
            .flush_i,
            .result_o        ( op_result           ),
            .status_o        ( op_status           ),
            .extension_bit_o ( lane_ext_bit[lane]  ),
            .tag_o           ( lane_tags[lane]     ),
            .mask_o          ( lane_masks[lane]    ),
            .aux_o           ( lane_aux[lane]      ),
            .out_valid_o     ( out_valid           ),
            .out_ready_i     ( out_ready           ),
            .busy_o          ( lane_busy[lane]     )
          );
        end else begin : gen_fma_instance
          fpnew_fma_multi #(
            .FpFmtConfig ( LANE_FORMATS            ),
            .NumPipeRegs ( NumPipeRegs             ),
            .PipeConfig  ( PipeConfig              ),
            .TagType     ( TagType                 ),
            .AuxType     ( logic [AUX_BITS-1:0]    )
          ) i_fpnew_fma_multi (
            .clk_i,
            .rst_ni,
            .operands_i      ( local_operands      ),
            .is_boxed_i,
            .rnd_mode_i      ( rnd_mode            ),
            .op_i            ( op_i                ),
            .op_mod_i,
            .src_fmt_i,
            .dst_fmt_i,
            .tag_i,
            .mask_i          ( simd_mask_i[lane]   ),
            .aux_i           ( aux_data            ),
            .in_valid_i      ( in_valid            ),
            .in_ready_o      ( lane_in_ready[lane] ),
            .flush_i,
            .result_o        ( op_result           ),
            .status_o        ( op_status           ),
            .extension_bit_o ( lane_ext_bit[lane]  ),
            .tag_o           ( lane_tags[lane]     ),
            .mask_o          ( lane_masks[lane]    ),
            .aux_o           ( lane_aux[lane]      ),
            .pace_operand_o  (                     ),
            .pace_fmt_o      (                     ),
            .out_valid_o     ( out_valid           ),
            .out_ready_i     ( out_ready           ),
            .busy_o          ( lane_busy[lane]     )
          );
        end
      end else if (OpGroup == fpnew_pkg::DOTP) begin : lane_instance
        fpnew_sdotp_multi_wrapper #(
          .LaneWidth   ( LANE_WIDTH           ),
          .FpFmtConfig ( LANE_FORMATS         ), // fp64 and fp32 not supported
          .NumPipeRegs ( NumPipeRegs          ),
          .PipeConfig  ( PipeConfig           ),
          .TagType     ( TagType              ),
          .AuxType     ( logic [AUX_BITS-1:0] ),
          .StochasticRndImplementation ( StochasticRndImplementation )
        ) i_fpnew_sdotp_multi_wrapper (
          .clk_i,
          .rst_ni,
          .sdotp_hart_id_i ( {hart_id_i, 2'b00} + lane ),
          .operands_i      ( local_operands[2:0] ), // 3 operands
          .is_boxed_i,
          .rnd_mode_i,
          .op_i,
          .op_mod_i,
          .src_fmt_i,
          .dst_fmt_i,
          .tag_i,
          .mask_i          ( simd_mask_i[lane]   ),
          .aux_i           ( aux_data            ),
          .in_valid_i      ( in_valid            ),
          .in_ready_o      ( lane_in_ready[lane] ),
          .flush_i,
          .result_o        ( op_result           ),
          .status_o        ( op_status           ),
          .extension_bit_o ( lane_ext_bit[lane]  ),
          .tag_o           ( lane_tags[lane]     ),
          .mask_o          ( lane_masks[lane]    ),
          .aux_o           ( lane_aux[lane]      ),
          .out_valid_o     ( out_valid           ),
          .out_ready_i     ( out_ready           ),
          .busy_o          ( lane_busy[lane]     )
        );
      end else if (OpGroup == fpnew_pkg::DIVSQRT) begin : lane_instance
         if (DivSqrtSel == fpnew_pkg::TH32 && LANE_FORMATS[0] && (LANE_FORMATS[1:fpnew_pkg::NUM_FP_FORMATS-1] == '0)) begin : gen_th32_e906_divsqrt
          // The T-head-based DivSqrt unit is supported only in FP32-only configurations
          fpnew_divsqrt_th_32 #(
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           ),
            .TagType     ( TagType              ),
            .AuxType     ( logic [AUX_BITS-1:0] )
          ) i_fpnew_divsqrt_multi_th (
            .clk_i,
            .rst_ni,
            .operands_i      ( local_operands[1:0] ), // 2 operands
            .is_boxed_i      ( is_boxed_2op        ), // 2 operands
            .rnd_mode_i      ( rnd_mode            ),
            .op_i,
            .tag_i,
            .mask_i          ( simd_mask_i[lane]   ),
            .aux_i           ( aux_data            ),
            .in_valid_i      ( in_valid            ),
            .in_ready_o      ( lane_in_ready[lane] ),
            .flush_i,
            .result_o        ( op_result           ),
            .status_o        ( op_status           ),
            .extension_bit_o ( lane_ext_bit[lane]  ),
            .tag_o           ( lane_tags[lane]     ),
            .mask_o          ( lane_masks[lane]    ),
            .aux_o           ( lane_aux[lane]      ),
            .out_valid_o     ( out_valid           ),
            .out_ready_i     ( out_ready           ),
            .busy_o          ( lane_busy[lane]     )
          );
        end else if(DivSqrtSel == fpnew_pkg::THMULTI) begin : gen_thmulti_c910_divsqrt
          fpnew_divsqrt_th_64_multi #(
            .FpFmtConfig ( LANE_FORMATS         ),
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           ),
            .TagType     ( TagType              ),
            .AuxType     ( logic [AUX_BITS-1:0] )
          ) i_fpnew_divsqrt_th_64_c910 (
           .clk_i,
            .rst_ni,
            .operands_i       ( local_operands[1:0] ), // 2 operands
            .is_boxed_i       ( is_boxed_2op        ), // 2 operands
            .rnd_mode_i       ( rnd_mode            ),
            .op_i,
            .dst_fmt_i,
            .tag_i,
            .mask_i           ( simd_mask_i[lane]   ),
            .aux_i            ( aux_data            ),
            .vectorial_op_i   ( vectorial_op        ), // synchronize only vectorial operations
            .in_valid_i       ( in_valid            ),
            .in_ready_o       ( lane_in_ready[lane] ),
            .divsqrt_done_o   ( divsqrt_done[lane]  ),
            .simd_synch_done_i( simd_synch_done     ),
            .divsqrt_ready_o  ( divsqrt_ready[lane] ),
            .simd_synch_rdy_i ( simd_synch_rdy      ),
            .flush_i,
            .result_o         ( op_result           ),
            .status_o         ( op_status           ),
            .extension_bit_o  ( lane_ext_bit[lane]  ),
            .tag_o            ( lane_tags[lane]     ),
            .mask_o           ( lane_masks[lane]    ),
            .aux_o            ( lane_aux[lane]      ),
            .out_valid_o      ( out_valid           ),
            .out_ready_i      ( out_ready           ),
            .busy_o           ( lane_busy[lane]     )
          );
        end else begin : gen_pulp_divsqrt
          fpnew_divsqrt_multi #(
            .FpFmtConfig ( LANE_FORMATS         ),
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           ),
            .TagType     ( TagType              ),
            .AuxType     ( logic [AUX_BITS-1:0] )
          ) i_fpnew_divsqrt_multi (
            .clk_i,
            .rst_ni,
            .operands_i       ( local_operands[1:0] ), // 2 operands
            .is_boxed_i       ( is_boxed_2op        ), // 2 operands
            .rnd_mode_i       ( rnd_mode            ),
            .op_i,
            .dst_fmt_i,
            .tag_i,
            .mask_i           ( simd_mask_i[lane]   ),
            .aux_i            ( aux_data            ),
            .vectorial_op_i   ( vectorial_op        ), // synchronize only vectorial operations
            .in_valid_i       ( in_valid            ),
            .in_ready_o       ( lane_in_ready[lane] ),
            .divsqrt_done_o   ( divsqrt_done[lane]  ),
            .simd_synch_done_i( simd_synch_done     ),
            .divsqrt_ready_o  ( divsqrt_ready[lane] ),
            .simd_synch_rdy_i ( simd_synch_rdy      ),
            .flush_i,
            .result_o         ( op_result           ),
            .status_o         ( op_status           ),
            .extension_bit_o  ( lane_ext_bit[lane]  ),
            .tag_o            ( lane_tags[lane]     ),
            .mask_o           ( lane_masks[lane]    ),
            .aux_o            ( lane_aux[lane]      ),
            .out_valid_o      ( out_valid           ),
            .out_ready_i      ( out_ready           ),
            .busy_o           ( lane_busy[lane]     )
          );
        end
      end else if (OpGroup == fpnew_pkg::NONCOMP) begin : lane_instance

      end else if (OpGroup == fpnew_pkg::CONV) begin : lane_instance
        fpnew_cast_multi #(
          .FpFmtConfig    ( CONV_FORMATS         ),
          .IntFmtConfig   ( CONV_INT_FORMATS     ),
          .MxFpFmtConfig  ( CONV_MX_FORMATS      ),
          .MxIntFmtConfig ( CONV_MX_INT_FORMATS  ),
          .EnableMXScale  ( LANE == 0            ),
          .NumPipeRegs    ( NumPipeRegs          ),
          .PipeConfig     ( PipeConfig           ),
          .TagType        ( TagType              ),
          .AuxType        ( logic [AUX_BITS-1:0] )
        ) i_fpnew_cast_multi (
          .clk_i,
          .rst_ni,
          .operands_i      ( local_operands[2:0]   ),
          .is_boxed_i      ( is_boxed_1op        ),
          .rnd_mode_i      ( rnd_mode            ),
          .op_i,
          .op_mod_i,
          .src_fmt_i,
          .dst_fmt_i,
          .int_fmt_i,
          .tag_i,
          .mask_i          ( simd_mask_i[lane]   ),
          .aux_i           ( aux_data            ),
          .in_valid_i      ( in_valid            ),
          .in_ready_o      ( lane_in_ready[lane] ),
          .flush_i,
          .result_o        ( op_result           ),
          .status_o        ( op_status           ),
          .extension_bit_o ( lane_ext_bit[lane]  ),
          .tag_o           ( lane_tags[lane]     ),
          .mask_o          ( lane_masks[lane]    ),
          .aux_o           ( lane_aux[lane]      ),
          .out_valid_o     ( out_valid           ),
          .out_ready_i     ( out_ready           ),
          .busy_o          ( lane_busy[lane]     )
        );
      end else if (OpGroup == fpnew_pkg::MXDOTP) begin : lane_instance
        fpnew_mxdotp_multi_wrapper #(
          .LaneWidth       ( LANE_WIDTH           ),
          .FpSrcFmtConfig  ( MXDOTP_FP_FORMATS    ),
          .IntSrcFmtConfig ( MXDOTP_INT_FORMATS   ),
          .FpDstFmtConfig  ( MXDOTP_DST_FORMATS   ),
          .NumPipeRegs     ( NumPipeRegs          ),
          .PipeConfig      ( PipeConfig           ),
          .TagType         ( TagType              ),
          .AuxType         ( logic [AUX_BITS-1:0] )
        ) i_fpnew_mxdotp_multi_wrapper (
          .clk_i,
          .rst_ni,
          .operands_i      ( local_operands[2:0]  ),
          .is_boxed_i,
          .rnd_mode_i,
          .op_i,
          .op_mod_i,
          .src_fmt_i,
          .int_fmt_i,
          .dst_fmt_i,
          .tag_i,
          .mask_i          ( simd_mask_i[lane]   ),
          .aux_i           ( aux_data            ),
          .in_valid_i      ( in_valid            ),
          .in_ready_o      ( lane_in_ready[lane] ),
          .flush_i,
          .result_o        ( op_result           ),
          .status_o        ( op_status           ),
          .extension_bit_o ( lane_ext_bit[lane]  ),
          .tag_o           ( lane_tags[lane]     ),
          .mask_o          ( lane_masks[lane]    ),
          .aux_o           ( lane_aux[lane]      ),
          .out_valid_o     ( out_valid           ),
          .out_ready_i     ( out_ready           ),
          .busy_o          ( lane_busy[lane]     )
        );
      end // ADD OTHER OPTIONS HERE

      // Handshakes are only done if the lane is actually used
      assign out_ready            = out_ready_i & ((lane == 0) | result_is_vector);
      assign lane_out_valid[lane] = out_valid & ((lane == 0) | result_is_vector);

      // Properly NaN-box or sign-extend the slice result if not in use
      assign local_result      = lane_out_valid[lane] ? op_result : {(LANE_WIDTH){lane_ext_bit[0]}};
      assign lane_status[lane] = lane_out_valid[lane] ? op_status : '0;

      if (OpGroup == fpnew_pkg::CONV && LANE == 0) begin : drive_mxscale_scale_byte
        assign mxscale_scale_byte = local_result[7:0];
      end

    // Otherwise generate constant sign-extension
    end else begin : inactive_lane
      assign lane_out_valid[lane] = 1'b0; // unused lane
      assign lane_in_ready[lane]  = 1'b0; // unused lane
      assign lane_aux[lane]       = 1'b0; // unused lane
      assign lane_masks[lane]     = 1'b1; // unused lane
      assign lane_tags[lane]      = 1'b0; // unused lane
      assign divsqrt_done[lane]   = 1'b0; // unused lane
      assign divsqrt_ready[lane]  = 1'b0; // unused lane
      assign lane_ext_bit[lane]   = 1'b1; // NaN-box unused lane
      assign local_result         = {(LANE_WIDTH){lane_ext_bit[0]}}; // sign-extend/nan box
      assign lane_status[lane]    = '0;
      assign lane_busy[lane]      = 1'b0;
    end

    // Generate result packing depending on float format
    for (genvar fmt = 0; fmt < NUM_FORMATS; fmt++) begin : pack_fp_result
      // Set up some constants
      if (OpGroup == fpnew_pkg::DOTP) begin
        localparam int unsigned INACTIVE_MASK = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(LANE_FORMATS[fmt]));
        localparam int unsigned FP_WIDTH      = fpnew_pkg::minimum(INACTIVE_MASK, fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt)));
        // only for active formats within the lane
        if (ACTIVE_FORMATS[fmt] && (LANE_WIDTH>0)) begin
          if (FP_WIDTH==INACTIVE_MASK) begin
            assign fmt_slice_result[fmt][(LANE+1)*FP_WIDTH-1:LANE*FP_WIDTH] =
                local_result[FP_WIDTH-1:0];
          end else begin
            assign fmt_slice_result[fmt][(LANE+1)*FP_WIDTH-1:LANE*FP_WIDTH] =
                local_result[FP_WIDTH-1:0];
          end
        end else if ((LANE+1)*FP_WIDTH <= Width) begin
          assign fmt_slice_result[fmt][(LANE+1)*FP_WIDTH-1:LANE*FP_WIDTH] =
              '{default: lane_ext_bit[LANE]};
        end else if (LANE*FP_WIDTH < Width) begin
          assign fmt_slice_result[fmt][Width-1:LANE*FP_WIDTH] =
              '{default: lane_ext_bit[LANE]};
        end
      end else begin
        localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
        localparam logic LANE_FMT_ACTIVE = (OpGroup == fpnew_pkg::CONV) ?
                                           CONV_ALL_FORMATS[fmt] : ACTIVE_FORMATS[fmt];
        // only for active formats within the lane
        if (LANE_FMT_ACTIVE && ((LANE+1)*FP_WIDTH <= Width)) begin
          assign fmt_slice_result[fmt][(LANE+1)*FP_WIDTH-1:LANE*FP_WIDTH] =
              local_result[FP_WIDTH-1:0];
        end else if (LANE_FMT_ACTIVE && (LANE*FP_WIDTH < Width)) begin
          assign fmt_slice_result[fmt][Width-1:LANE*FP_WIDTH] =
              local_result[Width-LANE*FP_WIDTH-1:0];
        end else if ((LANE+1)*FP_WIDTH <= Width) begin
          assign fmt_slice_result[fmt][(LANE+1)*FP_WIDTH-1:LANE*FP_WIDTH] =
              '{default: lane_ext_bit[LANE]};
        end else if (LANE*FP_WIDTH < Width) begin
          assign fmt_slice_result[fmt][Width-1:LANE*FP_WIDTH] =
              '{default: lane_ext_bit[LANE]};
        end
      end
    end

    // Generate result packing depending on integer format
    if (OpGroup == fpnew_pkg::CONV) begin : int_results_enabled
      for (genvar ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin : pack_int_result
        // Set up some constants
        localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));
        if (ACTIVE_INT_FORMATS[ifmt]) begin
          assign ifmt_slice_result[ifmt][(LANE+1)*INT_WIDTH-1:LANE*INT_WIDTH] =
            local_result[INT_WIDTH-1:0];
        end else if ((LANE+1)*INT_WIDTH <= Width) begin
          assign ifmt_slice_result[ifmt][(LANE+1)*INT_WIDTH-1:LANE*INT_WIDTH] = '0;
        end else if (LANE*INT_WIDTH < Width) begin
          assign ifmt_slice_result[ifmt][Width-1:LANE*INT_WIDTH] = '0;
        end
      end
    end
  end

  // Extend slice result if needed
  for (genvar fmt = 0; fmt < NUM_FORMATS; fmt++) begin : extend_fp_result
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    if (NUM_LANES*FP_WIDTH < Width)
      assign fmt_slice_result[fmt][Width-1:NUM_LANES*FP_WIDTH] = '{default: lane_ext_bit[0]};
  end

  for (genvar ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin : extend_or_mute_int_result
    // Mute int results if unused
    if (OpGroup != fpnew_pkg::CONV) begin : mute_int_result
      assign ifmt_slice_result[ifmt] = '0;

    // Extend slice result if needed
    end else begin : extend_int_result
      // Set up some constants
      localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));
      if (NUM_LANES*INT_WIDTH < Width)
        assign ifmt_slice_result[ifmt][Width-1:NUM_LANES*INT_WIDTH] = '0;
    end
  end

  // Bypass lanes with target operand for  insert/pack operations
  if (OpGroup == fpnew_pkg::CONV) begin : target_regs
    // Bypass pipeline signals, index i holds signal after i register stages
    logic [0:NumPipeRegs][Width-1:0] byp_pipe_target_q;
    logic [0:NumPipeRegs][1:0]       byp_pipe_aux_q;
    logic [0:NumPipeRegs][2:0]       byp_pipe_insert_nlanes_idx_q;
    insert_kind_e                    byp_pipe_insert_kind_q [0:NumPipeRegs];
    logic [0:NumPipeRegs]            byp_pipe_valid_q;
    // Ready signal is combinatorial for all stages
    logic [0:NumPipeRegs] byp_pipe_ready;

    // Input stage: First element of pipeline is taken from inputs
    assign byp_pipe_target_q[0]            = conv_target_d;
    assign byp_pipe_aux_q[0]               = target_aux_d;
    assign byp_pipe_insert_nlanes_idx_q[0] = target_insert_nlanes_idx_d;
    assign byp_pipe_insert_kind_q[0]       = target_insert_kind_d;
    assign byp_pipe_valid_q[0]             = in_valid_i & (dst_is_cpk | target_is_insert_d);
    // Generate the register stages
    for (genvar i = 0; i < NumPipeRegs; i++) begin : gen_bypass_pipeline
      // Internal register enable for this stage
      logic reg_ena;
      // Determine the ready signal of the current stage - advance the pipeline:
      // 1. if the next stage is ready for our data
      // 2. if the next stage only holds a bubble (not valid) -> we can pop it
      assign byp_pipe_ready[i] = byp_pipe_ready[i+1] | ~byp_pipe_valid_q[i+1];
      // Valid: enabled by ready signal, synchronous clear with the flush signal
      `FFLARNC(byp_pipe_valid_q[i+1], byp_pipe_valid_q[i], byp_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
      // Enable register if pipleine ready and a valid data item is present
      assign reg_ena = byp_pipe_ready[i] & byp_pipe_valid_q[i];
      // Generate the pipeline registers within the stages, use enable-registers
      `FFL(byp_pipe_target_q[i+1],            byp_pipe_target_q[i],            reg_ena, '0)
      `FFL(byp_pipe_aux_q[i+1],               byp_pipe_aux_q[i],               reg_ena, '0)
      `FFL(byp_pipe_insert_nlanes_idx_q[i+1], byp_pipe_insert_nlanes_idx_q[i], reg_ena, '0)
      `FFL(byp_pipe_insert_kind_q[i+1],       byp_pipe_insert_kind_q[i],       reg_ena, INSERT_NONE)

    end
    // Output stage: Ready travels backwards from output side, driven by downstream circuitry
    assign byp_pipe_ready[NumPipeRegs] = out_ready_i & (result_is_cpk | result_is_insert);
    // Output stage: assign module outputs
    assign conv_target_q = byp_pipe_target_q[NumPipeRegs];

    // decode the aux data
    assign result_vec_op = byp_pipe_aux_q[NumPipeRegs];

    assign result_is_insert         = (byp_pipe_insert_kind_q[NumPipeRegs] != INSERT_NONE);
    assign result_insert_nlanes_idx = byp_pipe_insert_nlanes_idx_q[NumPipeRegs];
    assign result_insert_kind       = byp_pipe_insert_kind_q[NumPipeRegs];

    if (EnableSlotSelect) begin : gen_insert_slot_pipe
      logic [0:NumPipeRegs][SELECTOR_WIDTH-1:0] byp_pipe_insert_slot_q;

      assign byp_pipe_insert_slot_q[0] = slot_select_imm;

      for (genvar i = 0; i < NumPipeRegs; i++) begin : gen_insert_slot_pipe_regs
        logic reg_ena;
        assign reg_ena = byp_pipe_ready[i] & byp_pipe_valid_q[i];
        `FFL(byp_pipe_insert_slot_q[i+1], byp_pipe_insert_slot_q[i], reg_ena, '0)
      end

      assign result_insert_slot = byp_pipe_insert_slot_q[NumPipeRegs];            // replicate result bypassed
    end else begin : gen_no_insert_slot_pipe
      assign result_insert_slot = '0;
    end


    for (genvar fmt = 0; fmt < NUM_FORMATS; fmt++) begin : pack_conv_cpk_result
      localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));

      for (genvar op_idx = 0; op_idx < 4; op_idx++) begin : pack_conv_cpk_result_operands
        localparam int unsigned UPPER_LEFT  = 2*(op_idx+1)*FP_WIDTH;
        localparam int unsigned LOWER_LEFT  = 2*op_idx*FP_WIDTH;
        localparam int unsigned UPPER_RIGHT = 2*FP_WIDTH;

        if(UPPER_LEFT <= Width) begin
          always_comb begin : pack_conv_cpk
            fmt_conv_cpk_result[fmt][op_idx] = conv_target_q; // rd pre-load
            fmt_conv_cpk_result[fmt][op_idx][UPPER_LEFT-1:LOWER_LEFT] = fmt_slice_result[fmt][UPPER_RIGHT-1:0*FP_WIDTH]; // vfcpk
          end
        end else begin
          assign fmt_conv_cpk_result[fmt][op_idx] = '0;
        end
      end
    end

  end else begin : no_conv
    assign result_is_insert = 1'b0;
    assign result_insert_nlanes_idx = '0;
    assign result_insert_slot = '0;
    assign result_insert_kind = INSERT_NONE;
    assign mxscale_scale_byte = '0;
  end

  if ((DivSqrtSel != fpnew_pkg::TH32) && (OpGroup == fpnew_pkg::DIVSQRT)) begin
    // Synch lanes if there is more than one
    assign simd_synch_rdy  = EnableVectors ? &divsqrt_ready[NUM_DIVSQRT_LANES-1:0] : divsqrt_ready[0];
    assign simd_synch_done = EnableVectors ? &divsqrt_done[NUM_DIVSQRT_LANES-1:0]  : divsqrt_done[0];
  end else begin
    // Unused (TH32 divider only supported for scalar FP32 divsqrt)
    assign simd_synch_rdy  = '0;
    assign simd_synch_done = '0;
  end

  // ------------
  // Output Side
  // ------------
  assign {result_is_cpk, result_fmt_is_int, result_is_vector, result_fmt, result_is_vsum} = lane_aux[0];

  if (EnableSlotSelect) begin : gen_insert_slot_select
    logic [NUM_FORMATS-1:0][fpnew_pkg::OP0_NUM_NLANES-1:0]
          [INSERT_NUM_SLOTS-1:0][Width-1:0] fmt_insert_result;
    logic [NUM_INT_FORMATS-1:0][fpnew_pkg::OP0_NUM_NLANES-1:0]
          [INSERT_NUM_SLOTS-1:0][Width-1:0] ifmt_insert_result;
    logic [INSERT_NUM_SLOTS-1:0][Width-1:0] byte_insert_result;

    for (genvar fmt = 0; fmt < NUM_FORMATS; fmt++) begin : gen_fmt_insert_result               // insertion logic
      localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
      for (genvar nidx = 0; nidx < fpnew_pkg::OP0_NUM_NLANES; nidx++) begin : gen_fmt_insert_nlanes
        localparam int unsigned NLANES = fpnew_pkg::op0_idx_to_nlanes(nidx);
        localparam int unsigned GROUP_BITS = NLANES * FP_WIDTH;
        for (genvar slot = 0; slot < INSERT_NUM_SLOTS; slot++) begin : gen_fmt_insert_slots
          localparam int unsigned SLOT_LSB = slot * GROUP_BITS;
          localparam int unsigned SLOT_MSB = SLOT_LSB + GROUP_BITS;
          if ((GROUP_BITS <= Width) && (SLOT_MSB <= Width)) begin : gen_fmt_insert_slot_valid
            always_comb begin
              fmt_insert_result[fmt][nidx][slot] = conv_target_q;                              // original lanes
              fmt_insert_result[fmt][nidx][slot][SLOT_MSB-1:SLOT_LSB] =
                  fmt_slice_result[fmt][GROUP_BITS-1:0];                                       // result lanes
            end
          end else begin : gen_fmt_insert_slot_invalid
            assign fmt_insert_result[fmt][nidx][slot] = conv_target_q;
          end
        end
      end
    end

    for (genvar slot = 0; slot < INSERT_NUM_SLOTS; slot++) begin : gen_byte_insert_result
      localparam int unsigned SLOT_LSB = slot * 8;
      localparam int unsigned SLOT_MSB = SLOT_LSB + 8;
      if (SLOT_MSB <= Width) begin : valid
        always_comb begin
          byte_insert_result[slot] = conv_target_q;
          byte_insert_result[slot][SLOT_MSB-1:SLOT_LSB] = mxscale_scale_byte;
        end
      end else begin : invalid
        assign byte_insert_result[slot] = conv_target_q;
      end
    end

    for (genvar ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin : gen_ifmt_insert_result
      localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));
      for (genvar nidx = 0; nidx < fpnew_pkg::OP0_NUM_NLANES; nidx++) begin : gen_ifmt_insert_nlanes
        localparam int unsigned NLANES = fpnew_pkg::op0_idx_to_nlanes(nidx);
        localparam int unsigned GROUP_BITS = NLANES * INT_WIDTH;
        for (genvar slot = 0; slot < INSERT_NUM_SLOTS; slot++) begin : gen_ifmt_insert_slots
          localparam int unsigned SLOT_LSB = slot * GROUP_BITS;
          localparam int unsigned SLOT_MSB = SLOT_LSB + GROUP_BITS;
          if ((GROUP_BITS <= Width) && (SLOT_MSB <= Width)) begin : gen_ifmt_insert_slot_valid
            always_comb begin
              ifmt_insert_result[ifmt][nidx][slot] = conv_target_q;
              ifmt_insert_result[ifmt][nidx][slot][SLOT_MSB-1:SLOT_LSB] =
                  ifmt_slice_result[ifmt][GROUP_BITS-1:0];
            end
          end else begin : gen_ifmt_insert_slot_invalid
            assign ifmt_insert_result[ifmt][nidx][slot] = conv_target_q;
          end
        end
      end
    end


    always_comb begin : select_insert_result
      insert_result = conv_target_q;
      unique case (result_insert_kind)
        INSERT_FP: insert_result = fmt_insert_result[result_fmt]
                                                   [result_insert_nlanes_idx]
                                                   [result_insert_slot];
        INSERT_INT: insert_result = ifmt_insert_result[result_fmt]
                                                       [result_insert_nlanes_idx]
                                                       [result_insert_slot];
        INSERT_BYTE: insert_result = byte_insert_result[result_insert_slot];

        default: begin
        end
      endcase
    end

  end else begin : gen_insert_slot0_only
    logic [NUM_FORMATS-1:0][fpnew_pkg::OP0_NUM_NLANES-1:0][Width-1:0]
          fmt_insert_result;
    logic [NUM_INT_FORMATS-1:0][fpnew_pkg::OP0_NUM_NLANES-1:0][Width-1:0]
          ifmt_insert_result;
    logic [Width-1:0] byte_insert_result;

    for (genvar fmt = 0; fmt < NUM_FORMATS; fmt++) begin : gen_fmt_insert_result
      localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
      for (genvar nidx = 0; nidx < fpnew_pkg::OP0_NUM_NLANES; nidx++) begin : gen_fmt_insert_nlanes
        localparam int unsigned NLANES = fpnew_pkg::op0_idx_to_nlanes(nidx);
        localparam int unsigned GROUP_BITS = NLANES * FP_WIDTH;
        if (GROUP_BITS <= Width) begin : gen_fmt_insert_slot0_valid
          always_comb begin
            fmt_insert_result[fmt][nidx] = conv_target_q;
            fmt_insert_result[fmt][nidx][GROUP_BITS-1:0] =
                fmt_slice_result[fmt][GROUP_BITS-1:0];
          end
        end else begin : gen_fmt_insert_slot0_invalid
          assign fmt_insert_result[fmt][nidx] = conv_target_q;
        end
      end
    end

    if (8 <= Width) begin : gen_byte_insert_valid
      always_comb begin
        byte_insert_result = conv_target_q;
        byte_insert_result[7:0] = mxscale_scale_byte;
      end
    end else begin : gen_byte_insert_invalid
      assign byte_insert_result = conv_target_q;
    end

    for (genvar ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin : gen_ifmt_insert_result
      localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));
      for (genvar nidx = 0; nidx < fpnew_pkg::OP0_NUM_NLANES; nidx++) begin : gen_ifmt_insert_nlanes
        localparam int unsigned NLANES = fpnew_pkg::op0_idx_to_nlanes(nidx);
        localparam int unsigned GROUP_BITS = NLANES * INT_WIDTH;
        if (GROUP_BITS <= Width) begin : gen_ifmt_insert_slot0_valid
          always_comb begin
            ifmt_insert_result[ifmt][nidx] = conv_target_q;
            ifmt_insert_result[ifmt][nidx][GROUP_BITS-1:0] =
                ifmt_slice_result[ifmt][GROUP_BITS-1:0];
          end
        end else begin : gen_ifmt_insert_slot0_invalid
          assign ifmt_insert_result[ifmt][nidx] = conv_target_q;
        end
      end
    end


    always_comb begin : select_insert_result
      insert_result = conv_target_q;
      unique case (result_insert_kind)
        INSERT_FP: insert_result = fmt_insert_result[result_fmt][result_insert_nlanes_idx];
        INSERT_INT: insert_result = ifmt_insert_result[result_fmt][result_insert_nlanes_idx];
        INSERT_BYTE: insert_result = byte_insert_result;
        default: begin
        end
      endcase

    end
  end

  assign result_o = result_is_insert  ? insert_result                                   :
                    result_fmt_is_int ? ifmt_slice_result[result_fmt]                   :
                    result_is_cpk     ? fmt_conv_cpk_result[result_fmt][result_vec_op]  :
                    (result_is_vsum  && (Width == 64)) ? {{(Width/2){1'b1}}, {fmt_slice_result[result_fmt][Width/2-1:0]}} :
                                        fmt_slice_result[result_fmt];

  assign extension_bit_o = lane_ext_bit[0]; // don't care about upper ones
  assign tag_o           = lane_tags[0];    // don't care about upper ones
  assign busy_o          = (| lane_busy);

  assign out_valid_o     = lane_out_valid[0]; // don't care about upper ones

  // Collapse the status
  always_comb begin : output_processing
    // Collapse the status
    automatic fpnew_pkg::status_t temp_status;
    temp_status = '0;
    for (int i = 0; i < int'(NUM_LANES); i++)
      temp_status |= lane_status[i] & {5{lane_masks[i]}};
    status_o = temp_status;
  end

endmodule
