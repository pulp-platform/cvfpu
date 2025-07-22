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

module pace_dataflow
  import pace_package::*;
#(
  parameter type           TagType       = logic,
  localparam int unsigned  Width         = 32,
  localparam int unsigned  MaxDegree     = pace_package::MaxSupportedDegree,
  localparam int unsigned  MaxPartitions = pace_package::MaxSupportedPartitions
) (
  // Global signals
  input  logic             clk_i,
  input  logic             rst_ni,

`ifdef SUPPORT_MORE_PARTITIONS
  input  logic [1:0][Width-1:0] data_i,
`else
  `ifdef SUPPORT_MORE_DEGREES
    input  logic [1:0][Width-1:0] data_i,
  `else
    input  logic [0:0][Width-1:0] data_i,
  `endif
`endif

`ifdef FPNEW_INTEGRATION 
  input  TagType tag_i,
  output TagType tag_o,
`endif

  input  logic             valid_i,
  output logic             ready_o,
  output logic [Width-1:0] data_o,
  output logic             valid_o,
  input  logic             ready_i,
  output logic             busy_o,

  input  pace_package::pace_cfg_t config_i
);

  // Constants
  localparam InpStreams      = 3;
  localparam CoeffMemIdx     = 0;
  localparam BpMemIdx        = 1;
  localparam InpIdx          = 2;
  localparam DegreeWidth     = $clog2(MaxDegree);
  localparam PartitionsWidth = $clog2(MaxPartitions);

  // Internal signals
  logic [DegreeWidth-1:0]     cfg_degree;
  logic [PartitionsWidth-1:0] cfg_partitions;

  logic [InpStreams-1:0]      inp_valid;
  logic [InpStreams-1:0]      inp_ready;

  logic                       fma_oup_valid;
  logic                       coeff_rvalid;

  logic [Width-1:0]           pwpa_out;

`ifdef FPNEW_INTEGRATION 
  TagType tag_o_debug;
  assign tag_o = (flags_partition.bp_mem.init_done) ? tag_o_debug : tag_i;
`endif

  assign data_o = (flags_partition.bp_mem.init_done) ? pwpa_out : data_i[0];


`ifdef SUPPORT_MORE_PARTITIONS
  typedef logic [msb(2 * Width + CoeffMemRdPorts):0] DataType;
`else  
  `ifdef SUPPORT_MORE_DEGREES
    typedef logic [msb(2 * Width):0] DataType;
  `else
    typedef logic [msb(Width):0] DataType;
  `endif
`endif 

`ifdef FPNEW_INTEGRATION
  typedef struct packed {
    TagType  tag;
    DataType data;
  } TagDataType;
  
  TagDataType fma_inp_data, fma_inp_data_q;
`else 
  typedef struct packed {
    DataType data;
  } TagDataType;

  TagDataType fma_inp_data, fma_inp_data_q;
`endif

  // Handshake and control signals
  logic             fma_inp_valid, fma_inp_valid_q;
  logic             fma_inp_ready, fma_inp_ready_q;
  logic             config_start_d, config_start_q;
  logic [msb(PolyDegree):0] fma_handshake;

  logic             fma_busy;


  ctrl_engine_t           ctrl_engine;
  ctrl_partition_t        ctrl_partition;
  flags_partition_t       flags_partition;
  ctrl_coeff_mem_t        ctrl_coeff;
  flags_coeff_mem_t       flags_coeff;

  fpnew_pkg::fp_format_e  fp_type;
  coeff_rd_addr_t         coeff_raddr;
  coeff_rd_data_t         coeff_rdata;
  coeff_bypass_mask_t     coeff_bypass;

  logic [msb(CoeffMemRdPorts):0] bypass;
  logic                          inp_handshake;

  // Busy signal aggregation
  assign busy_o = fma_busy | fma_inp_valid_q | inp_handshake;

  // Config field unpacking
  assign cfg_degree     = config_i.degree;
  assign cfg_partitions = config_i.partition;

  // Demultiplex input valid signals
  for (genvar streams = 0; streams < InpStreams; streams++) begin : demux_streams
    assign inp_valid[streams] = valid_i;
  end : demux_streams

  // Output ready is high when any stream is ready
  assign ready_o = |inp_ready;

  // Engine control
  assign ctrl_engine.fp_mode        = config_i.fp_mode;
  assign ctrl_coeff.fp_mode         = ctrl_engine.fp_mode;

  // Degree exceed control
  `ifdef SUPPORT_MORE_DEGREES
    assign ctrl_engine.degree_exceed = config_i.degree_exceed;
  `else
    assign ctrl_engine.degree_exceed = 1'b0;
  `endif

  // Partition exceed control
  `ifdef SUPPORT_MORE_PARTITIONS
    assign ctrl_engine.part_exceed     = config_i.part_exceed;
    assign ctrl_partition.part_exceed  = config_i.part_exceed;
  `else
    assign ctrl_engine.part_exceed     = 1'b0;
    assign ctrl_partition.part_exceed  = 1'b0;
  `endif

  // FP format conversion
  assign fp_type = (ctrl_engine.fp_mode == FP32)  ? fpnew_pkg::FP32 :
                  (ctrl_engine.fp_mode == FP16)  ? fpnew_pkg::FP16 :
                  (ctrl_engine.fp_mode == BFP16) ? fpnew_pkg::FP16ALT :
                                                  fpnew_pkg::FP8;

  // Coefficient memory control logic
  assign ctrl_coeff.write.start = !config_start_q && config_start_d;
  assign ctrl_coeff.read_done   = !config_start_d && config_start_q;
  assign ctrl_coeff.max_wenable = 1 << cfg_degree;
  assign ctrl_coeff.max_length  = (ctrl_engine.fp_mode == FP32)  ? cfg_partitions - 1 :
                                  (ctrl_engine.fp_mode == FP16)  ? cfg_partitions / 2 - 1 :
                                  (ctrl_engine.fp_mode == BFP16) ? cfg_partitions / 2 - 1 :
                                                                  cfg_partitions / 4 - 1;
  assign ctrl_coeff.clear       = config_start_q && !config_start_d;
  assign ctrl_coeff.renable     = '1;

  // Partition detector control logic
  assign ctrl_partition.bp_mem.write.start = flags_coeff.write_done;
  assign ctrl_partition.bp_mem.max_length  = cfg_partitions;
  assign ctrl_partition.bp_mem.clear       = config_start_q && !config_start_d;
  assign ctrl_partition.fp_mode            = ctrl_engine.fp_mode;

  assign ctrl_partition.part_enable_fp32 = config_start_q ? ((1 << (cfg_partitions + 1)) - 1) : '0;
  assign ctrl_partition.part_enable_fp16 = config_start_q ? ((1 << (cfg_partitions + 1)) - 1) : '0;
  assign ctrl_partition.part_enable_fp8  = config_start_q ? ((1 << (cfg_partitions + 1)) - 1) : '0;

  // Coefficient memory wrapper instantiation
  coeff_memory_wrap i_coeff_memory (
    .clk_i    ( clk_i                  ),
    .rst_ni   ( rst_ni                 ),
    .ctrl_i   ( ctrl_coeff             ),
    .flags_o  ( flags_coeff            ),
    .data_i   ( data_i[0]              ),
    .valid_i  ( inp_valid[CoeffMemIdx] ),
    .ready_o  ( inp_ready[CoeffMemIdx] ),
    .data_o   ( coeff_rdata            ),
    .valid_o  ( coeff_rvalid           ),
    .raddr_i  ( coeff_raddr            ),
    .bypass_i ( coeff_bypass           )
  );

  // FMA input data packing
  `ifdef SUPPORT_MORE_PARTITIONS
    assign fma_inp_data.data[msb(2*Width):Width] = data_i[1];
    assign fma_inp_data.data[msb(2*Width + CoeffMemRdPorts):2*Width] = bypass;
  `else  
    `ifdef SUPPORT_MORE_DEGREES
      assign fma_inp_data.data[msb(2*Width):Width] = data_i[1];
    `endif
  `endif 

  `ifdef FPNEW_INTEGRATION
    assign fma_inp_data.tag = tag_i;
  `endif

  spill_register_flushable #(
    .T( TagDataType )
  ) i_spill_register_input (
    .clk_i,      
    .rst_ni,     
    .flush_i   ( 1'b0            ),  
    .data_i    ( fma_inp_data    ),  
    .valid_i   ( fma_inp_valid   ),  
    .ready_o   ( fma_inp_ready   ),
    .data_o    ( fma_inp_data_q  ),
    .valid_o   ( fma_inp_valid_q ),
    .ready_i   ( fma_inp_ready_q ) 
  );

  coeff_bypass_addr_bank_t     coeff_raddr_bypass;

  partition_detector_multi i_partition_detector_multi (
    .clk_i               ( clk_i              ), 
    .rst_ni              ( rst_ni             ),
    .ctrl_i              ( ctrl_partition     ),
    .flags_o             ( flags_partition    ),
    .bp_data_i           ( data_i[0]          ),
    .bp_valid_i          ( inp_valid[BpMemIdx]),
    .bp_ready_o          ( inp_ready[BpMemIdx]),
    .feat_data_i         ( data_i[0]          ),
    .feat_valid_i        ( inp_valid[InpIdx]  ),
    .feat_ready_o        ( inp_ready[InpIdx]  ),
    .feat_data_o         ( fma_inp_data.data[msb(Width):0]),
    .feat_valid_o        ( fma_inp_valid      ),
    .feat_ready_i        ( fma_inp_ready      ),
    .bypass_o            ( bypass             ),
    .coeff_raddr_bypass_o( coeff_raddr_bypass )
  );

  assign inp_handshake = valid_i & inp_ready[InpIdx];
  

  coeff_addr_generator i_coeff_addr_generator (
    .clk_i,
    .rst_ni, 
    .fma_handshake_i     ( fma_handshake      ), 
    .inp_handshake_i     ( inp_handshake      ), 
    .coeff_raddr_bypass_i( coeff_raddr_bypass ),
    .coeff_raddr_o       ( coeff_raddr        ),
    .coeff_bypass_o      ( coeff_bypass       )
  );
  
  fma_cascaded_vectorial #(
    .TagDataType ( TagDataType ),
    .TagType     ( TagType     )
  ) i_fma_cascaded_vectorial (
    .clk_i        ( clk_i                        ),
    .rst_ni       ( rst_ni                       ),
    .ctrl_i       ( ctrl_engine                  ),
  `ifdef SUPPORT_MORE_PARTITIONS
    .input_i      ( fma_inp_data_q.data[msb(Width):0] ),
    .pres_i       ( fma_inp_data_q.data[msb(2*Width):Width] ),
    .bypass_i     ( fma_inp_data_q.data[msb(2*Width+CoeffMemRdPorts):2*Width] ),
  `else 
    `ifdef SUPPORT_MORE_DEGREES 
      .input_i    ( fma_inp_data_q.data[msb(Width):0] ),
      .pres_i     ( fma_inp_data_q.data[msb(2*Width):Width] ),
    `else 
      .input_i    ( fma_inp_data_q.data[msb(Width):0] ),
    `endif 
  `endif
  `ifdef FPNEW_INTEGRATION
    .tag_i        ( fma_inp_data_q.tag  ),
    .tag_o        ( tag_o_debug         ),
  `endif 
    .coeff_i      ( coeff_rdata         ),
    .fp_type_i    ( fp_type             ),
    .valid_i      ( fma_inp_valid_q     ),
    .ready_o      ( fma_inp_ready_q     ),
    .flush_i      ( 1'b0                ),
    .result_o     ( pwpa_out            ),
    .handshake_o  ( fma_handshake       ),
    .valid_o      ( fma_oup_valid       ),
    .ready_i      ( ready_i             ),
    .busy_o       ( fma_busy            )
  );

  // Output valid signal logic
  assign init_handshake_d = valid_i & ready_o;
  assign valid_o = (flags_partition.bp_mem.init_done) ? fma_oup_valid : init_handshake_d;

  // Config start tracking
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      config_start_q <= 1'b0;
    end else begin
      config_start_q <= config_start_d;
    end
  end

  assign config_start_d = config_i.start;


endmodule