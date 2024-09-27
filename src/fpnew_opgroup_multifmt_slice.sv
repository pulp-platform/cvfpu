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
  parameter fpnew_pkg::opgroup_e      OpGroup       = fpnew_pkg::CONV,
  parameter int unsigned              Width         = 64,
  // FPU configuration
  parameter fpnew_pkg::fmt_logic_t    FpFmtConfig   = '1,
  parameter fpnew_pkg::ifmt_logic_t   IntFmtConfig  = '1,
  parameter logic                     EnableVectors = 1'b1,
  parameter fpnew_pkg::divsqrt_unit_t DivSqrtSel    = fpnew_pkg::THMULTI,
  parameter int unsigned              NumPipeRegs   = 0,
  parameter fpnew_pkg::pipe_config_t  PipeConfig    = fpnew_pkg::BEFORE,
  parameter type                      TagType       = logic,
  parameter fpnew_pkg::rsr_impl_t     StochasticRndImplementation = fpnew_pkg::DEFAULT_NO_RSR,
  // Do not change
  localparam int unsigned NUM_OPERANDS = fpnew_pkg::num_operands(OpGroup),
  localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned NUM_SIMD_LANES = fpnew_pkg::max_num_lanes(Width, FpFmtConfig, EnableVectors),
  localparam type         MaskType     = logic [NUM_SIMD_LANES-1:0]
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

  if ((OpGroup == fpnew_pkg::DIVSQRT)) begin
    if ((DivSqrtSel == fpnew_pkg::TH32) && !((FpFmtConfig[0] == 1) && (FpFmtConfig[1:NUM_FORMATS-1] == '0))) begin
      $fatal(1, "T-Head-based DivSqrt unit supported only in FP32-only configurations. \
Set DivSqrtSel = THMULTI or DivSqrtSel = PULP to use a multi-format divider");
    end else if ((DivSqrtSel == fpnew_pkg::THMULTI) && (FpFmtConfig[3] == 1'b1 || FpFmtConfig[5] == 1'b1)) begin
      $warning("The DivSqrt unit of C910 (instantiated by DivSqrtSel = THMULTI) does not support \
FP8, FP8alt. Please use the PULP DivSqrt unit when in need of div/sqrt operations on FP8, FP8alt.");
    end
  end

  if ((OpGroup == fpnew_pkg::DOTP) &&
      !(FpFmtConfig[0] && (FpFmtConfig[2] || FpFmtConfig[4]) && (FpFmtConfig[3] || FpFmtConfig[5]))) begin
    $fatal(1, "SDOTP only supported on 32b and 64b CVFPU instances in which at \
least one 16b and one 8b format are supported. \
The SDOTP operations compute on 8b inputs producing 16b outputs \
or on 16b inputs producing 32b outputs");
  end

  localparam int unsigned MAX_FP_WIDTH   = fpnew_pkg::max_fp_width(FpFmtConfig);
  localparam int unsigned MAX_INT_WIDTH  = fpnew_pkg::max_int_width(IntFmtConfig);
  localparam int unsigned NUM_LANES = fpnew_pkg::max_num_lanes(Width, FpFmtConfig, 1'b1);
  localparam int unsigned NUM_DIVSQRT_LANES = fpnew_pkg::num_divsqrt_lanes(Width, FpFmtConfig, 1'b1, DivSqrtSel);
  localparam int unsigned NUM_DOTP_LANES = fpnew_pkg::num_dotp_lanes(Width, FpFmtConfig);
  localparam int unsigned NUM_INT_FORMATS = fpnew_pkg::NUM_INT_FORMATS;
  // We will send the format information along with the data
  localparam int unsigned FMT_BITS =
      fpnew_pkg::maximum($clog2(NUM_FORMATS), $clog2(NUM_INT_FORMATS));
  localparam int unsigned AUX_BITS = FMT_BITS + 3; // add integer flags

  logic                 vectorial_op;
  logic [FMT_BITS-1:0]  dst_fmt; // destination format to pass along with operation
  logic [AUX_BITS-1:0]  in_aux, out_aux; // aux signals to pass along with the operation

  // additional flags for CONV
  logic       dst_fmt_is_int, dst_is_cpk;
  logic [1:0] dst_vec_op; // info for vectorial results (for packing)
  logic [1:0] target_aux_d;
  logic       is_up_cast, is_down_cast;

  logic [NUM_FORMATS-1:0][Width-1:0]      fmt_slice_result;
  logic [NUM_INT_FORMATS-1:0][Width-1:0]  ifmt_slice_result;
  logic [NUM_FORMATS-1:0][3:0][Width-1:0] fmt_conv_cpk_result;


  logic [Width-1:0] conv_target_d, conv_target_q; // vectorial conversions update a register

  fpnew_pkg::status_t [NUM_LANES-1:0]   lane_status;
  logic   [NUM_LANES-1:0]               lane_ext_bit; // only the first one is actually used
  logic   [NUM_LANES-1:0]               lane_masks;

  logic                result_is_vsum, op_is_vsum;
  logic [FMT_BITS-1:0] result_fmt;
  logic                result_fmt_is_int, result_is_cpk;
  logic [1:0]          result_vec_op; // info for vectorial results (for packing)

  logic simd_synch_rdy, simd_synch_done;
  fpnew_pkg::roundmode_e rnd_mode;

  // -----------
  // Input Side
  // -----------
  // RSR supported only on SDOTP module
  assign rnd_mode = (rnd_mode_i == fpnew_pkg::RSR) ? fpnew_pkg::RNE : rnd_mode_i;

  assign vectorial_op = vectorial_op_i & EnableVectors; // only do vectorial stuff if enabled

  // Cast-and-Pack ops are encoded in operation and modifier
  assign dst_fmt_is_int = (OpGroup == fpnew_pkg::CONV) & (op_i == fpnew_pkg::F2I);
  assign dst_is_cpk     = (OpGroup == fpnew_pkg::CONV) & (op_i == fpnew_pkg::CPKAB ||
                                                          op_i == fpnew_pkg::CPKCD);
  assign dst_vec_op     = {2{(OpGroup == fpnew_pkg::CONV)}} & {(op_i == fpnew_pkg::CPKCD), op_mod_i};

  assign is_up_cast   = (fpnew_pkg::fp_width(dst_fmt_i) > fpnew_pkg::fp_width(src_fmt_i));
  assign is_down_cast = (fpnew_pkg::fp_width(dst_fmt_i) < fpnew_pkg::fp_width(src_fmt_i));
  assign op_is_vsum   = op_i == fpnew_pkg::VSUM ? 1'b1 : 1'b0;

  // The destination format is the int format for F2I casts
  assign dst_fmt    = dst_fmt_is_int ? int_fmt_i : dst_fmt_i;

  // The data sent along consists of the vectorial flag and format bits
  assign in_aux        = {dst_is_cpk, dst_fmt_is_int, dst_fmt, op_is_vsum};
  assign target_aux_d  = dst_vec_op;

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
  // Generate Aux Chain
  // ---------------
  // Signals to transmit reg enable to other modules
  logic [NumPipeRegs-1:0] vector_reg_enable;

  logic [NUM_LANES-1:0] in_lane_active, out_lane_active, lane_fsm_ready, lane_fsm_start;
  logic [NUM_LANES-1:0][NumPipeRegs-1:0] lane_reg_enabe;

  if (OpGroup == fpnew_pkg::DIVSQRT) begin: gen_fsm_aux
    fpnew_aux_fsm #(
      .NumPipeRegs( NumPipeRegs          ),
      .PipeConfig ( PipeConfig           ),
      .TagType    ( TagType              ),
      .AuxType    ( logic [AUX_BITS-1:0] ),
      .NumLanes   ( NUM_LANES            )
    ) i_aux_fsm (
      .clk_i,
      .rst_ni,
      .tag_i,
      .aux_i               ( in_aux             ),
      .is_vector_i         ( vectorial_op       ),
      .lane_active_i       ( in_lane_active     ),
      .in_valid_i,
      .in_ready_o,
      .flush_i,
      .tag_o,
      .aux_o               ( out_aux            ),
      .is_vector_o         ( /* Unused */       ),
      .lane_active_o       ( out_lane_active    ),
      .out_valid_o,
      .out_ready_i,
      .busy_o,
      .reg_enable_o        ( /* Unused */       ),
      .vector_reg_enable_o ( vector_reg_enable  ),
      .lane_reg_enable_o   ( lane_reg_enabe     ),
      .lane_fsm_start_o    ( lane_fsm_start     ),
      .lane_fsm_ready_i    ( lane_fsm_ready     )
    );
  end else begin: gen_direct_aux
    fpnew_aux #(
      .NumPipeRegs( NumPipeRegs          ),
      .TagType    ( TagType              ),
      .AuxType    ( logic [AUX_BITS-1:0] ),
      .NumLanes   ( NUM_LANES            )
    ) i_aux (
      .clk_i,
      .rst_ni,
      .tag_i,
      .aux_i               ( in_aux             ),
      .is_vector_i         ( vectorial_op       ),
      .lane_active_i       ( in_lane_active     ),
      .in_valid_i,
      .in_ready_o,
      .flush_i,
      .tag_o,
      .aux_o               ( out_aux            ),
      .is_vector_o         ( /* Unused */       ),
      .lane_active_o       ( out_lane_active    ),
      .out_valid_o,
      .out_ready_i,
      .busy_o,
      .reg_enable_o        ( /* Unused */       ),
      .vector_reg_enable_o ( vector_reg_enable  ),
      .lane_reg_enable_o   ( lane_reg_enabe     )
    );
  end

  // ---------------
  // Generate Lanes
  // ---------------
  for (genvar lane = 0; lane < int'(NUM_LANES); lane++) begin : gen_num_lanes
    localparam int unsigned LANE = unsigned'(lane); // unsigned to please the linter
    // Get a mask of active formats for this lane
    localparam fpnew_pkg::fmt_logic_t ACTIVE_FORMATS =
        fpnew_pkg::get_lane_formats(Width, FpFmtConfig, LANE);
    localparam fpnew_pkg::ifmt_logic_t ACTIVE_INT_FORMATS =
        fpnew_pkg::get_lane_int_formats(Width, FpFmtConfig, IntFmtConfig, LANE);
    localparam int unsigned MAX_WIDTH = fpnew_pkg::max_fp_width(ACTIVE_FORMATS);

    // Cast-specific parameters
    localparam fpnew_pkg::fmt_logic_t CONV_FORMATS =
        fpnew_pkg::get_conv_lane_formats(Width, FpFmtConfig, LANE);
    localparam fpnew_pkg::ifmt_logic_t CONV_INT_FORMATS =
        fpnew_pkg::get_conv_lane_int_formats(Width, FpFmtConfig, IntFmtConfig, LANE);
    localparam int unsigned CONV_WIDTH = fpnew_pkg::max_fp_width(CONV_FORMATS);

    // Dotp-specific parameters
    localparam fpnew_pkg::fmt_logic_t DOTP_FORMATS =
        fpnew_pkg::get_dotp_lane_formats(Width, FpFmtConfig, LANE);
    localparam int unsigned DOTP_MAX_FMT_WIDTH = fpnew_pkg::max_fp_width(DOTP_FORMATS);
    localparam int unsigned DOTP_WIDTH = fpnew_pkg::minimum(2*DOTP_MAX_FMT_WIDTH, Width);

    // Lane parameters from Opgroup
    localparam fpnew_pkg::fmt_logic_t LANE_FORMATS = (OpGroup == fpnew_pkg::CONV) ? CONV_FORMATS :
                                                     (OpGroup == fpnew_pkg::DOTP) ? DOTP_FORMATS :
                                                                                    ACTIVE_FORMATS;
    localparam int unsigned LANE_WIDTH = (OpGroup == fpnew_pkg::CONV) ? CONV_WIDTH :
                                         (OpGroup == fpnew_pkg::DOTP) ? DOTP_WIDTH : MAX_WIDTH;

    logic [LANE_WIDTH-1:0] local_result; // lane-local results

    // Generate instances only if needed, lane 0 always generated
    if ((lane == 0) || (EnableVectors & (!(OpGroup == fpnew_pkg::DOTP && (lane >= NUM_DOTP_LANES))
                                        && !(OpGroup == fpnew_pkg::DIVSQRT && (lane >= NUM_DIVSQRT_LANES))))) begin : active_lane

      logic [NUM_OPERANDS-1:0][LANE_WIDTH-1:0] local_operands;  // lane-local oprands
      logic [LANE_WIDTH-1:0]                   op_result;       // lane-local results
      fpnew_pkg::status_t                      op_status;

      // Figure out if lane is active e.g. should be used
      assign in_lane_active[lane] = (
        (LANE_FORMATS[src_fmt_i] & ~is_up_cast) | 
        (LANE_FORMATS[dst_fmt_i] &  is_up_cast) | 
        (OpGroup == fpnew_pkg::DIVSQRT)
      ) & ((lane == 0) | vectorial_op);

      // Slice out the operands for this lane, upper bits are ignored in the unit
      always_comb begin : prepare_input
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
        end else if (OpGroup == fpnew_pkg::CONV) begin // override operand 0 for some conversions
          // Source is an integer
          if (op_i == fpnew_pkg::I2F) begin
            local_operands[0] = operands_i[0] >> LANE*fpnew_pkg::int_width(int_fmt_i);
          // vectorial F2F up casts
          end else if (op_i == fpnew_pkg::F2F) begin
            if (vectorial_op && op_mod_i && is_up_cast) begin // up cast with upper half
              local_operands[0] = operands_i[0] >> LANE*fpnew_pkg::fp_width(src_fmt_i) +
                                                   MAX_FP_WIDTH/2;
            end
          // CPK
          end else if (dst_is_cpk) begin
            if (lane == 1) begin
              local_operands[0] = operands_i[1];
            end
          end
        end
      end

      // Instantiate the operation from the selected opgroup
      if (OpGroup == fpnew_pkg::ADDMUL) begin : lane_instance
        fpnew_fma_multi #(
          .FpFmtConfig ( LANE_FORMATS         ),
          .NumPipeRegs ( NumPipeRegs          ),
          .PipeConfig  ( PipeConfig           )
        ) i_fpnew_fma_multi (
          .clk_i,
          .rst_ni,
          .operands_i      ( local_operands  ),
          .is_boxed_i,
          .rnd_mode_i      ( rnd_mode        ),
          .op_i,
          .op_mod_i,
          .src_fmt_i,
          .dst_fmt_i,
          .mask_i          ( simd_mask_i[lane]    ),
          .result_o        ( op_result            ),
          .status_o        ( op_status            ),
          .extension_bit_o ( lane_ext_bit[lane]   ),
          .mask_o          ( lane_masks[lane]     ),
          .reg_enable_i    ( lane_reg_enabe[lane] )
        );
      end else if (OpGroup == fpnew_pkg::DOTP) begin : lane_instance
        fpnew_sdotp_multi_wrapper #(
          .LaneWidth                   ( LANE_WIDTH                  ),
          .FpFmtConfig                 ( LANE_FORMATS                ), // fp64 and fp32 not supported
          .NumPipeRegs                 ( NumPipeRegs                 ),
          .PipeConfig                  ( PipeConfig                  ),
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
          .mask_i          ( simd_mask_i[lane]    ),
          .result_o        ( op_result            ),
          .status_o        ( op_status            ),
          .extension_bit_o ( lane_ext_bit[lane]   ),
          .mask_o          ( lane_masks[lane]     ),
          .reg_enable_i    ( lane_reg_enabe[lane] )
        );
      end else if (OpGroup == fpnew_pkg::NONCOMP) begin : lane_instance

      end else if (OpGroup == fpnew_pkg::DIVSQRT) begin : lane_instance
        if (DivSqrtSel == fpnew_pkg::TH32 && LANE_FORMATS[0] && (LANE_FORMATS[1:fpnew_pkg::NUM_FP_FORMATS-1] == '0)) begin : gen_th32_e906_divsqrt
          // The T-head-based DivSqrt unit is supported only in FP32-only configurations
          fpnew_divsqrt_th_32 #(
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           )
          ) i_fpnew_divsqrt_multi_th (
            .clk_i,
            .rst_ni,
            .operands_i       ( local_operands[1:0]  ), // 2 operands
            .is_boxed_i       ( is_boxed_2op         ), // 2 operands
            .rnd_mode_i       ( rnd_mode             ),
            .op_i,
            .mask_i           ( simd_mask_i[lane]    ),
            .flush_i,
            .result_o         ( op_result            ),
            .status_o         ( op_status            ),
            .extension_bit_o  ( lane_ext_bit[lane]   ),
            .mask_o           ( lane_masks[lane]     ),
            .reg_enable_i     ( lane_reg_enabe[lane] ),
            .fsm_start_i      ( lane_fsm_start[lane] ),
            .fsm_ready_o      ( lane_fsm_ready[lane] )
          );
        end else if(DivSqrtSel == fpnew_pkg::THMULTI) begin : gen_thmulti_c910_divsqrt
          fpnew_divsqrt_th_64_multi #(
            .FpFmtConfig ( LANE_FORMATS         ),
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           )
          ) i_fpnew_divsqrt_th_64_c910 (
            .clk_i,
            .rst_ni,
            .operands_i       ( local_operands[1:0]  ), // 2 operands
            .is_boxed_i       ( is_boxed_2op         ), // 2 operands
            .rnd_mode_i       ( rnd_mode             ),
            .op_i,
            .dst_fmt_i,
            .mask_i           ( simd_mask_i[lane]    ),
            .flush_i,
            .result_o         ( op_result            ),
            .status_o         ( op_status            ),
            .extension_bit_o  ( lane_ext_bit[lane]   ),
            .mask_o           ( lane_masks[lane]     ),
            .reg_enable_i     ( lane_reg_enabe[lane] ),
            .fsm_start_i      ( lane_fsm_start[lane] ),
            .fsm_ready_o      ( lane_fsm_ready[lane] )
          );
        end else begin : gen_pulp_divsqrt
          fpnew_divsqrt_multi #(
            .FpFmtConfig ( LANE_FORMATS         ),
            .NumPipeRegs ( NumPipeRegs          ),
            .PipeConfig  ( PipeConfig           )
          ) i_fpnew_divsqrt_multi (
            .clk_i,
            .rst_ni,
            .operands_i       ( local_operands[1:0]  ), // 2 operands
            .is_boxed_i       ( is_boxed_2op         ), // 2 operands
            .rnd_mode_i       ( rnd_mode             ),
            .op_i,
            .dst_fmt_i,
            .mask_i           ( simd_mask_i[lane]    ),
            .flush_i,
            .result_o         ( op_result            ),
            .status_o         ( op_status            ),
            .extension_bit_o  ( lane_ext_bit[lane]   ),
            .mask_o           ( lane_masks[lane]     ),
            .reg_enable_i     ( lane_reg_enabe[lane] ),
            .fsm_start_i      ( lane_fsm_start[lane] ),
            .fsm_ready_o      ( lane_fsm_ready[lane] )
          );
        end
      end else if (OpGroup == fpnew_pkg::CONV) begin : lane_instance
        fpnew_cast_multi #(
          .FpFmtConfig  ( LANE_FORMATS         ),
          .IntFmtConfig ( CONV_INT_FORMATS     ),
          .NumPipeRegs  ( NumPipeRegs          ),
          .PipeConfig   ( PipeConfig           )
        ) i_fpnew_cast_multi (
          .clk_i,
          .rst_ni,
          .operands_i      ( local_operands[0]   ),
          .is_boxed_i      ( is_boxed_1op        ),
          .rnd_mode_i      ( rnd_mode            ),
          .op_i,
          .op_mod_i,
          .src_fmt_i,
          .dst_fmt_i,
          .int_fmt_i,
          .mask_i          ( simd_mask_i[lane]    ),
          .result_o        ( op_result            ),
          .status_o        ( op_status            ),
          .extension_bit_o ( lane_ext_bit[lane]   ),
          .mask_o          ( lane_masks[lane]     ),
          .reg_enable_i    ( lane_reg_enabe[lane] )
        );
      end // ADD OTHER OPTIONS HERE

      // Guard against accidentally using the wrong aux module
      if (OpGroup != fpnew_pkg::DIVSQRT) begin : lane_fsm_guard
        assign lane_fsm_ready[lane] = 1'b0; // Lane does not have a FSM, it can not be ready!
      end

      // Properly NaN-box or sign-extend the slice result if not in use
      assign local_result      = out_lane_active[lane] ? op_result: '{default: lane_ext_bit[0]};
      assign lane_status[lane] = out_lane_active[lane] ? op_status : '0;

    // Otherwise generate constant sign-extension
    end else begin : inactive_lane
      assign lane_masks[lane]     = 1'b1; // unused lane
      assign lane_ext_bit[lane]   = 1'b1; // NaN-box unused lane
      assign local_result         = {(LANE_WIDTH){lane_ext_bit[0]}}; // sign-extend/nan box
      assign lane_status[lane]    = '0;
      assign in_lane_active[lane] = 1'b0; // Lane does not exist, it can never be active
      assign lane_fsm_ready[lane] = 1'b1; // Lane does not exist, it is always ready just in case erronous data gets to the FSM in this slot
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
        // only for active formats within the lane
        if (ACTIVE_FORMATS[fmt]) begin
          assign fmt_slice_result[fmt][(LANE+1)*FP_WIDTH-1:LANE*FP_WIDTH] =
              local_result[FP_WIDTH-1:0];
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

  // Bypass lanes with target operand for vectorial casts
  if (OpGroup == fpnew_pkg::CONV) begin : target_regs
    // Bypass pipeline signals, index i holds signal after i register stages
    logic [0:NumPipeRegs][Width-1:0] byp_pipe_target_q;
    logic [0:NumPipeRegs][1:0]       byp_pipe_aux_q;

    // Input stage: First element of pipeline is taken from inputs
    assign byp_pipe_target_q[0]  = conv_target_d;
    assign byp_pipe_aux_q[0]     = target_aux_d;

    // Generate the register stages
    for (genvar i = 0; i < NumPipeRegs; i++) begin : gen_bypass_pipeline
        // Internal register enable for this stage
        logic reg_ena;
        // Enable register is set externally
        assign reg_ena = vector_reg_enable[i];
      // Generate the pipeline registers within the stages, use enable-registers
      `FFL(byp_pipe_target_q[i+1],  byp_pipe_target_q[i],  reg_ena, '0)
      `FFL(byp_pipe_aux_q[i+1],     byp_pipe_aux_q[i],     reg_ena, '0)
    end

    // Output stage: assign module outputs
    assign conv_target_q = byp_pipe_target_q[NumPipeRegs];

    // decode the aux data
    assign result_vec_op = byp_pipe_aux_q[NumPipeRegs];

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
    assign result_vec_op = '0;
    assign fmt_conv_cpk_result = '0;
    assign conv_target_q = '0;
  end

  // ------------
  // Output Side
  // ------------
  assign {result_is_cpk, result_fmt_is_int, result_fmt, result_is_vsum} = out_aux;

  assign result_o = result_fmt_is_int ? ifmt_slice_result[result_fmt]                   :
                    result_is_cpk     ? fmt_conv_cpk_result[result_fmt][result_vec_op]  :
                    (result_is_vsum  && (Width == 64)) ? {{(Width/2){1'b1}}, {fmt_slice_result[result_fmt][Width/2-1:0]}} :
                                        fmt_slice_result[result_fmt];

  assign extension_bit_o = lane_ext_bit[0]; // don't care about upper ones

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
