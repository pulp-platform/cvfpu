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

module fpnew_top #(
  // FPU configuration
  parameter fpnew_pkg::fpu_features_t       Features                    = fpnew_pkg::RV64D_Xsflt,
  parameter fpnew_pkg::fpu_implementation_t Implementation              = fpnew_pkg::DEFAULT_NOREGS,
  // DivSqrtSel chooses among PULP, TH32, or THMULTI (see documentation and fpnew_pkg.sv for further details)
  parameter fpnew_pkg::divsqrt_unit_t       DivSqrtSel                  = fpnew_pkg::THMULTI,
  parameter type                            TagType                     = logic,
  parameter logic                           TrueSIMDClass               = 1'b0,
  parameter logic                           EnableSIMDMask              = 1'b0,
  parameter logic                           CompressedVecCmpResult      = 1'b0, // conceived for RV32FD cores
  parameter fpnew_pkg::rsr_impl_t           StochasticRndImplementation = fpnew_pkg::DEFAULT_NO_RSR,
  parameter fpnew_pkg::redundancy_features_t RedundancyFeatures         = fpnew_pkg::DEFAULT_NO_REDUNDANCY,
  // Do not change
  localparam int unsigned NumLanes     = fpnew_pkg::max_num_lanes(Features.Width, Features.FpFmtMask, Features.EnableVectors),
  localparam type         MaskType     = logic [NumLanes-1:0],
  localparam int unsigned WIDTH        = Features.Width,
  localparam int unsigned NUM_OPERANDS = 3
) (
  input logic                               clk_i,
  input logic                               rst_ni,
  input logic [31:0]                        hart_id_i,
  input logic                               redundancy_enable_i,
  // Input signals
  input logic [NUM_OPERANDS-1:0][WIDTH-1:0] operands_i,
  input fpnew_pkg::roundmode_e              rnd_mode_i,
  input fpnew_pkg::operation_e              op_i,
  input logic                               op_mod_i,
  input fpnew_pkg::fp_format_e              src_fmt_i,
  input fpnew_pkg::fp_format_e              dst_fmt_i,
  input fpnew_pkg::int_format_e             int_fmt_i,
  input logic                               vectorial_op_i,
  input TagType                             tag_i,
  input MaskType                            simd_mask_i,
  // Input Handshake
  input  logic                              in_valid_i,
  output logic                              in_ready_o,
  input  logic                              flush_i,
  // Output signals
  output logic [WIDTH-1:0]                  result_o,
  output fpnew_pkg::status_t                status_o,
  output TagType                            tag_o,
  // Output handshake
  output logic                              out_valid_o,
  input  logic                              out_ready_i,
  // Indication of valid data in flight
  output logic                              busy_o,
  output logic                              fault_detected_o
);

  localparam int unsigned NUM_OPGROUPS = fpnew_pkg::NUM_OPGROUPS;
  localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS;
  localparam int LOCK_TIMEOUT = fpnew_pkg::division_enabled(Implementation.UnitTypes) ? 60: 5;

  localparam bit DIVISION_ENABLED = fpnew_pkg::division_enabled(Implementation.UnitTypes);

  localparam bit TTR_ENABLED = 
    RedundancyFeatures.RedundancyType == fpnew_pkg::TTR  || 
    RedundancyFeatures.RedundancyType == fpnew_pkg::TTR_FAST || 
    RedundancyFeatures.RedundancyType == fpnew_pkg::TTR_SMALL;
  
  localparam bit DTR_ENABLED = 
    RedundancyFeatures.RedundancyType == fpnew_pkg::DTR || 
    RedundancyFeatures.RedundancyType == fpnew_pkg::DTR_INORDER;

  localparam bit SELF_CHECKING = RedundancyFeatures.TripplicateRepetition;

  localparam int MAX_DELAY = 
    // Base formula for how long something can stay in chain
    2 * fpnew_pkg::longest_path(Implementation.PipeRegs, Implementation.PipeConfig)
    - fpnew_pkg::shortest_path(Implementation.PipeRegs, Implementation.PipeConfig)
    // In case of a DTR based approach the retry has another storage element that we need to account for
    + (DTR_ENABLED ? 1 : 0);
    // The ternary operator ? 1 : 0 is needed since True / False might not evaluate to 1 / 0 in all tools
    // For example in synopsys-2022.03-kgf dc_shell the True evaluates to 2 or 3 in this line

  // Based of the max delay we can not calculate how big of an ID is needed to ensure ids are locally unique
  localparam int unsigned ID_SIZE_BASE = fpnew_pkg::maximum(
    1, 
    $clog2(MAX_DELAY) + (DIVISION_ENABLED ? (TTR_ENABLED ? 4 : 1) : 0)
    // In case of a TTR approach we add extra ID Bits for the Division since it can take up to 12 cycles
    // For DTR we only need 1 bit extra as we split the storage
  );  

  // We have an extra bit for DMR methods to do error detection
  localparam int unsigned ID_SIZE = ID_SIZE_BASE + (DTR_ENABLED ? 3 : 0);

  // ----------------
  // Type Definition
  // ----------------
  typedef struct packed {
    logic [NUM_OPERANDS-1:0][WIDTH-1:0] operands;
    fpnew_pkg::roundmode_e              rnd_mode;
    fpnew_pkg::operation_e              op;
    logic                               op_mod;
    fpnew_pkg::fp_format_e              src_fmt;
    fpnew_pkg::fp_format_e              dst_fmt;
    fpnew_pkg::int_format_e             int_fmt;
    logic                               vectorial_op;
    TagType                             tag;
    MaskType                            simd_mask;
  } tmr_in_stacked_t;

  typedef struct packed {
    TagType                tag;
    logic [ID_SIZE-1:0]    opid;
  } submodules_stacked_t;

  typedef struct packed {
    logic [WIDTH-1:0]      result;
    fpnew_pkg::status_t    status;
    TagType                tag;
    logic [ID_SIZE-1:0]    opid;
  } rr_stacked_t;

  typedef struct packed {
    logic [WIDTH-1:0]      result;
    fpnew_pkg::status_t    status;
    TagType                tag;
  } tmr_out_stacked_t;

  // ----------------
  // Enable / Disable Redundancy
  // ----------------

  logic in_gated_valid, in_gated_ready;
  logic internal_busy, gated_redundancy_enable;

  if (RedundancyFeatures.RedundancyType == fpnew_pkg::NONE) begin : gen_no_redundandcy_controller
    assign in_gated_valid = in_valid_i;
    assign in_ready_o = in_gated_ready;
    assign busy_o = internal_busy;
    assign gated_redundancy_enable = 0;
  end else begin: gen_redundancy_controller
    redundancy_controller # (
        .InternalRedundancy ( SELF_CHECKING ),
        .LockTimeout        ( LOCK_TIMEOUT  )
    ) i_redundancy_controller (
       .clk_i,
       .rst_ni,
       .enable_i ( redundancy_enable_i     ),
       .busy_o   ( busy_o                  ),
       .busy_i   ( internal_busy           ),
       .enable_o ( gated_redundancy_enable ),
       .valid_i  ( in_valid_i              ),
       .ready_o  ( in_ready_o              ), 
       .valid_o  ( in_gated_valid          ),
       .ready_i  ( in_gated_ready          )
    );  
  end

  // -----------
  // Repeat Signals for Redundancy
  // -----------
  tmr_in_stacked_t in_data, in_redundant_data;
  logic [ID_SIZE-1:0] in_redundant_opid;
  logic in_redundant_valid, in_redundant_ready;

  assign in_data.operands     = operands_i;
  assign in_data.rnd_mode     = rnd_mode_i;
  assign in_data.op           = op_i;
  assign in_data.op_mod       = op_mod_i;
  assign in_data.src_fmt      = src_fmt_i;
  assign in_data.dst_fmt      = dst_fmt_i;
  assign in_data.int_fmt      = int_fmt_i;
  assign in_data.vectorial_op = vectorial_op_i;
  assign in_data.tag          = tag_i;
  assign in_data.simd_mask    = simd_mask_i | ~{NumLanes{EnableSIMDMask}}; // Filter out the mask if not used

  // Connection down to counterpart
  retry_interface #(
    .IDSize ( ID_SIZE )
  ) retry_connection ();

  if (TTR_ENABLED) begin: gen_in_ttr

    localparam bit SKIP_STORAGE = RedundancyFeatures.RedundancyType == fpnew_pkg::TTR_SMALL;

    TTR_start #(
        .DataType           ( tmr_in_stacked_t ),
        .IDSize             ( ID_SIZE          ),
        .InternalRedundancy ( SELF_CHECKING    ),
        .EarlyReadyEnable   ( !SKIP_STORAGE    )
    ) i_TTR_start (
        .clk_i,
        .rst_ni,
        .enable_i( gated_redundancy_enable ),
        .data_i  ( in_data                 ),
        .valid_i ( in_gated_valid          ),
        .ready_o ( in_gated_ready          ),
        .data_o  ( in_redundant_data       ),
        .id_o    ( in_redundant_opid       ),
        .valid_o ( in_redundant_valid      ),
        .ready_i ( in_redundant_ready      )
    );

  end else if (DTR_ENABLED) begin: gen_in_dtr
    // Connection directly to next module
    tmr_in_stacked_t retry2dmr_data;
    logic [ID_SIZE-1:0] retry2dmr_opid;
    logic retry2dmr_valid, retry2dmr_ready;

    logic op_is_div;
    assign op_is_div = in_data.op == fpnew_pkg::SQRT || in_data.op == fpnew_pkg::DIV;

    retry_start #(
        .DataType       ( tmr_in_stacked_t        ),
        .IDSize         ( ID_SIZE                 ),
        .ExternalIDBits ( DIVISION_ENABLED ? 1: 0 )
    ) i_retry_start (
        .clk_i,
        .rst_ni,
        .data_i        ( in_data              ),
        .ext_id_bits_i ( op_is_div            ),
        .valid_i       ( in_gated_valid       ),
        .ready_o       ( in_gated_ready       ),
        .data_o        ( retry2dmr_data       ),
        .id_o          ( retry2dmr_opid       ),
        .valid_o       ( retry2dmr_valid      ),
        .ready_i       ( retry2dmr_ready      ),
        .retry         ( retry_connection     )
    );

    DTR_start #(
        .DataType           ( tmr_in_stacked_t ),
        .IDSize             ( ID_SIZE          ),
        .InternalRedundancy ( SELF_CHECKING    ),
        .UseExternalId      ( 1                ),
        .EarlyReadyEnable   ( 1                )
    ) i_DTR_start (
        .clk_i,
        .rst_ni,
        .enable_i      ( gated_redundancy_enable ),
        .data_i        ( retry2dmr_data          ),
        .id_i          ( retry2dmr_opid          ),
        .valid_i       ( retry2dmr_valid         ),
        .ready_o       ( retry2dmr_ready         ),
        .data_o        ( in_redundant_data       ),  
        .id_o          ( in_redundant_opid       ),
        .valid_o       ( in_redundant_valid      ),
        .ready_i       ( in_redundant_ready      )
    );
  end else begin: gen_in_no_redundancy
    assign in_redundant_data = in_data;
    assign in_redundant_valid = in_gated_valid;
    assign in_gated_ready = in_redundant_ready;
    assign in_redundant_opid = 0;
  end

  // Handshake signals for the blocks
  logic [NUM_OPGROUPS-1:0] in_opgrp_ready, out_opgrp_valid, out_opgrp_ready, out_opgrp_ext, opgrp_busy;
  rr_stacked_t [NUM_OPGROUPS-1:0] out_opgrp_data;

  localparam int LockRepetition = RedundancyFeatures.TripplicateRepetition ? 3 : 1;
  logic [LockRepetition-1:0] out_rr_lock;

  logic [NUM_FORMATS-1:0][NUM_OPERANDS-1:0] is_boxed;

  // -----------
  // Input Side
  // -----------
  assign in_redundant_ready = in_redundant_valid & in_opgrp_ready[fpnew_pkg::get_opgroup(in_redundant_data.op)];
  assign internal_busy = (| opgrp_busy);

  // NaN-boxing check
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_nanbox_check
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    // NaN boxing is only generated if it's enabled and needed
    if (Features.EnableNanBox && (FP_WIDTH < WIDTH)) begin : check
      for (genvar op = 0; op < int'(NUM_OPERANDS); op++) begin : operands
        assign is_boxed[fmt][op] = (!in_redundant_data.vectorial_op)
                                   ? in_redundant_data.operands[op][WIDTH-1:FP_WIDTH] == '1
                                   : 1'b1;
      end
    end else begin : no_check
      assign is_boxed[fmt] = '1;
    end
  end

  // -------------------------
  // Generate Operation Blocks
  // -------------------------
  for (genvar opgrp = 0; opgrp < int'(NUM_OPGROUPS); opgrp++) begin : gen_operation_groups
    localparam int unsigned NUM_OPS = fpnew_pkg::num_operands(fpnew_pkg::opgroup_e'(opgrp));

    logic in_valid;
    logic [NUM_FORMATS-1:0][NUM_OPS-1:0] input_boxed;

    assign in_valid = in_redundant_valid & (fpnew_pkg::get_opgroup(in_redundant_data.op) == fpnew_pkg::opgroup_e'(opgrp));

    // slice out input boxing
    always_comb begin : slice_inputs
      for (int unsigned fmt = 0; fmt < NUM_FORMATS; fmt++)
        input_boxed[fmt] = is_boxed[fmt][NUM_OPS-1:0];
    end

    submodules_stacked_t in_tag, out_tag;

    assign in_tag.tag = in_redundant_data.tag;
    assign in_tag.opid  = in_redundant_opid;

    fpnew_opgroup_block #(
      .OpGroup                     ( fpnew_pkg::opgroup_e'(opgrp)    ),
      .Width                       ( WIDTH                           ),
      .EnableVectors               ( Features.EnableVectors          ),
      .DivSqrtSel                  ( DivSqrtSel                      ),
      .FpFmtMask                   ( Features.FpFmtMask              ),
      .IntFmtMask                  ( Features.IntFmtMask             ),
      .FmtPipeRegs                 ( Implementation.PipeRegs[opgrp]  ),
      .FmtUnitTypes                ( Implementation.UnitTypes[opgrp] ),
      .PipeConfig                  ( Implementation.PipeConfig       ),
      .TagType                     ( submodules_stacked_t            ),
      .TrueSIMDClass               ( TrueSIMDClass                   ),
      .CompressedVecCmpResult      ( CompressedVecCmpResult          ),
      .StochasticRndImplementation ( StochasticRndImplementation     ),
      .LockRepetition              ( LockRepetition                  )
    ) i_opgroup_block (
      .clk_i,
      .rst_ni,
      .hart_id_i       ( hart_id_i                               ),
      .operands_i      ( in_redundant_data.operands[NUM_OPS-1:0] ),
      .is_boxed_i      ( input_boxed                             ),
      .rnd_mode_i      ( in_redundant_data.rnd_mode              ),
      .op_i            ( in_redundant_data.op                    ),
      .op_mod_i        ( in_redundant_data.op_mod                ),
      .src_fmt_i       ( in_redundant_data.src_fmt               ),        
      .dst_fmt_i       ( in_redundant_data.dst_fmt               ),
      .int_fmt_i       ( in_redundant_data.int_fmt               ),
      .vectorial_op_i  ( in_redundant_data.vectorial_op          ),
      .tag_i           ( in_tag                                  ),
     .simd_mask_i      ( in_redundant_data.simd_mask             ),
      .in_valid_i      ( in_valid                                ),
      .in_ready_o      ( in_opgrp_ready[opgrp]                   ),
      .flush_i,
      .result_o        ( out_opgrp_data[opgrp].result            ),
      .status_o        ( out_opgrp_data[opgrp].status            ),
      .extension_bit_o ( out_opgrp_ext[opgrp]                    ),
      .tag_o           ( out_tag                                 ),
      .out_valid_o     ( out_opgrp_valid[opgrp]                  ),
      .out_lock_i      ( out_rr_lock                             ),
      .out_ready_i     ( out_opgrp_ready[opgrp]                  ),
      .busy_o          ( opgrp_busy[opgrp]                       )
    );

    assign out_opgrp_data[opgrp].tag = out_tag.tag;
    assign out_opgrp_data[opgrp].opid = out_tag.opid;

  end

  // ------------------
  // Arbitrate Outputs
  // ------------------
  logic out_redundant_valid, out_redundant_ready;
  rr_stacked_t out_redundant_data;

  logic [LockRepetition-1:0] flush;
  for (genvar r = 0; r < LockRepetition; r++) begin: gen_rr_flush
    assign flush[r] = flush_i;
  end

  // Round-Robin arbiter to decide which result to use
  rr_arb_tree_lock #(
    .NumIn              ( NUM_OPGROUPS  ),
    .DataType           ( rr_stacked_t  ),
    .AxiVldRdy          ( 1'b1          ),
    .FairArb            ( 1'b1          ),
    .InternalRedundancy ( SELF_CHECKING )
  ) i_arbiter (
    .clk_i,
    .rst_ni,
    .flush_i   ( flush               ),
    .rr_i      ( '0                  ),
    .lock_rr_i ( out_rr_lock         ),
    .req_i     ( out_opgrp_valid     ),
    .gnt_o     ( out_opgrp_ready     ),
    .data_i    ( out_opgrp_data      ),
    .gnt_i     ( out_redundant_ready ),
    .req_o     ( out_redundant_valid ),
    .data_o    ( out_redundant_data  ),
    .idx_o     ( /* Unused */        )
  );

  // ------------------
  // Unrepeat Outputs
  // ------------------

  tmr_out_stacked_t out_data, out_redundant_data_noid;
  assign out_redundant_data_noid.tag = out_redundant_data.tag;
  assign out_redundant_data_noid.status = out_redundant_data.status;
  assign out_redundant_data_noid.result = out_redundant_data.result;

  if (TTR_ENABLED) begin : gen_out_ttr
    localparam bit EARLY_RETURN = RedundancyFeatures.RedundancyType == fpnew_pkg::TTR_FAST;

    TTR_end #(
        .DataType           ( tmr_out_stacked_t ),
        .LockTimeout        ( LOCK_TIMEOUT      ),
        .IDSize             ( ID_SIZE           ),
        .InternalRedundancy ( SELF_CHECKING     ),
        .EarlyValidEnable   ( EARLY_RETURN      )
    ) i_TTR_end (
        .clk_i,
        .rst_ni,
        .enable_i         ( gated_redundancy_enable ),
        .data_i           ( out_redundant_data_noid ),
        .id_i             ( out_redundant_data.opid ),
        .valid_i          ( out_redundant_valid     ),
        .ready_o          ( out_redundant_ready     ),
        .lock_o           ( out_rr_lock             ),
        .data_o           ( out_data                ),
        .valid_o          ( out_valid_o             ),
        .ready_i          ( out_ready_i             ),
        .fault_detected_o ( fault_detected_o        )
    );

    assign retry_opid = fpnew_pkg::DONT_CARE;
    assign retry_valid = fpnew_pkg::DONT_CARE;
    assign retry_lock = fpnew_pkg::DONT_CARE;

  end else if (DTR_ENABLED) begin : gen_out_dmr
    tmr_out_stacked_t dmr2retry_data;
    logic [ID_SIZE-1:0] dmr2retry_opid;
    logic dmr2retry_valid, dmr2retry_ready, dmr2retry_needs_retry;

    DTR_end #(
        .DataType           ( tmr_out_stacked_t ),
        .LockTimeout        ( LOCK_TIMEOUT      ),
        .IDSize             ( ID_SIZE           ),
        .InternalRedundancy ( SELF_CHECKING     )
    ) i_DTR_end (
        .clk_i,
        .rst_ni,
        .enable_i         ( gated_redundancy_enable ),
        .data_i           ( out_redundant_data_noid ),
        .id_i             ( out_redundant_data.opid ),
        .valid_i          ( out_redundant_valid     ),
        .ready_o          ( out_redundant_ready     ),
        .lock_o           ( out_rr_lock             ),
        .data_o           ( dmr2retry_data          ),
        .id_o             ( dmr2retry_opid          ),
        .needs_retry_o    ( dmr2retry_needs_retry   ),
        .valid_o          ( dmr2retry_valid         ),
        .ready_i          ( dmr2retry_ready         ),
        .fault_detected_o ( fault_detected_o        )
    );

    retry_end #(
        .DataType ( tmr_out_stacked_t ),
        .IDSize   ( ID_SIZE           )
    ) i_retry_end (
        .clk_i,
        .rst_ni,
        .data_i        ( dmr2retry_data        ),
        .id_i          ( dmr2retry_opid        ),
        .needs_retry_i ( dmr2retry_needs_retry ),
        .valid_i       ( dmr2retry_valid       ),
        .ready_o       ( dmr2retry_ready       ),
        .data_o        ( out_data              ),
        .valid_o       ( out_valid_o           ),
        .ready_i       ( out_ready_i           ),
        .retry         ( retry_connection      )
    );
    assign retry_lock = fpnew_pkg::DONT_CARE;

  end else begin : gen_out_no_redundancy
    assign out_data = out_redundant_data_noid;
    assign out_valid_o = out_redundant_valid;
    assign out_redundant_ready = out_ready_i;
    assign out_rr_lock = 0;
    assign fault_detected_o = 0;

    assign retry_opid = fpnew_pkg::DONT_CARE;
    assign retry_valid = fpnew_pkg::DONT_CARE;
    assign retry_lock = fpnew_pkg::DONT_CARE;
  end

  // Unpack output
  assign result_o        = out_data.result;
  assign status_o        = out_data.status;
  assign tag_o           = out_data.tag;

endmodule
