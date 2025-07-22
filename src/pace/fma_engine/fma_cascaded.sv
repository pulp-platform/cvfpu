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

module fma_cascaded 
  import pace_package::*;
#(
  parameter int                      OpBits = 0,
  parameter int                      Width        = 0,
  parameter type                     FpDataType   = logic,
  parameter type                     CoeffDataType= logic,
  parameter fpnew_pkg::fmt_logic_t   FpFmtConfig  = '1,
  parameter int unsigned             NumPipeRegs  = 0,
  parameter fpnew_pkg::pipe_config_t PipeConfig   = fpnew_pkg::BEFORE,
  // parameter type                     TagDataType  = logic,
  parameter type                     TagType      = logic,
  parameter type                     AuxType      = logic
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  input  ctrl_engine_t                ctrl_i,
  // Input signals
  input  FpDataType                   input_i, // 3 operands
`ifdef SUPPORT_MORE_PARTITIONS 
  input  FpDataType                   pres_i, // 3 operands
  input logic                         bypass_i,
`else 
  `ifdef SUPPORT_MORE_DEGREES
    input  FpDataType                 pres_i, // 3 operands
  `endif
`endif
`ifdef FPNEW_INTEGRATION 
  input  TagType                      tag_i,
  output TagType                      tag_o,
`endif 
  input  CoeffDataType                coeffs_i, // 3 operands
  input  fpnew_pkg::fp_format_e       fp_type_i,
  // Input Handshake
  input  logic                        in_valid_i,
  output logic                        in_ready_o,
  input  logic                        flush_i,
  // Output signals
  output FpDataType                   result_o,
  output fpnew_pkg::status_t          status_o,
  output logic [msb(PolyDegree):0] handshake_o,
  // Output handshake
  output logic                        out_valid_o,
  input  logic                        out_ready_i,
  // Indication of valid data in flight
  output logic                        busy_o
);
  logic [msb(PolyDegree*3):0][msb(OpBits):0] operands;
  logic [msb(PolyDegree):0][msb(OpBits):0]   out_data;                    
  

  logic [msb(PolyDegree):0]                out_valid;
  logic [msb(PolyDegree):0]                out_ready;
  logic [msb(PolyDegree):0]                inp_valid;
  logic [msb(PolyDegree):0]                inp_ready;
  logic [msb(PolyDegree):0]                busy;
  fpnew_pkg::status_t [msb(PolyDegree):0]  status;

  logic [msb(PolyDegree):0][msb(OpBits):0] result;

`ifdef FPNEW_INTEGRATION
  typedef struct packed {
    TagType tag;
    logic [msb(OpBits):0] data;
  } TagDataType;
`else 
  typedef struct packed {
    logic [msb(OpBits):0] data;
  } TagDataType;
`endif

  TagDataType inp_tag [msb(PolyDegree):0];
  TagDataType oup_tag [msb(PolyDegree):0];


  genvar ii;
  // generate
    for (ii = 0;  ii  < PolyDegree; ii++) begin : gen_fma_cascaded
      if(ii==0) begin 
        `ifdef SUPPORT_MORE_DEGREES
          `ifdef SUPPORT_MORE_PARTITIONS
              assign operands[ii*3+1] = (ctrl_i.degree_exceed) |(ctrl_i.part_exceed && bypass_i) ? pres_i : coeffs_i[ii*2+0];
              assign operands[ii*3+0] = ~(ctrl_i.part_exceed && bypass_i) ? input_i : 
                                      (fp_type_i == fpnew_pkg::FP32) ? 32'h3f800000 :
                                      (fp_type_i == fpnew_pkg::FP16) ? 16'h3c00 :
                                      (fp_type_i == fpnew_pkg::FP16ALT) ? 16'h3f80 :
                                      8'h80;
              assign operands[ii*3+2] = coeffs_i[ii*2+1];
          `else 
              assign operands[ii*3+1] = ctrl_i.degree_exceed ? pres_i : coeffs_i[ii*2+0];
              assign operands[ii*3+0] = input_i;
              assign operands[ii*3+2] = coeffs_i[ii*2+1];
          `endif 
          assign inp_tag[ii].data = ctrl_i.degree_exceed ? input_i : operands[ii*3+0];
          `ifdef FPNEW_INTEGRATION
            assign inp_tag[ii].tag  = tag_i;
          `endif
        `else 
          `ifdef SUPPORT_MORE_PARTITIONS
            assign operands[ii*3+1] = ctrl_i.part_exceed && bypass_i ? pres_i : coeffs_i[ii*2+0];
            assign operands[ii*3+0] = ~(ctrl_i.part_exceed && bypass_i) ? input_i : 
                                      (fp_type_i == fpnew_pkg::FP32) ? 32'h3f800000 :
                                      (fp_type_i == fpnew_pkg::FP16) ? 16'h3c00 :
                                      (fp_type_i == fpnew_pkg::FP16ALT) ? 16'h3f80 :
                                      8'h80;
            assign operands[ii*3+2] = coeffs_i[ii*2+1];
            assign inp_tag[ii].data = operands[ii*3+0];

            `ifdef FPNEW_INTEGRATION
              assign inp_tag[ii].tag  = tag_i;
            `endif
          `else 
            assign operands[ii*3+1] = coeffs_i[ii*2+0];
            assign operands[ii*3+0] = input_i;
            assign operands[ii*3+2] = coeffs_i[ii*2+1];
            assign inp_tag[ii].data = input_i;

            `ifdef FPNEW_INTEGRATION
              assign inp_tag[ii].tag  = tag_i;
            `endif
          `endif
        `endif
          assign inp_valid[ii]    = in_valid_i;
          assign in_ready_o       = inp_ready[ii];
      end else begin 
          assign operands[ii*3+0] = result[ii-1];
          assign operands[ii*3+1] = oup_tag[ii-1].data;
          assign operands[ii*3+2] = coeffs_i[ii+1];
          assign inp_valid[ii]    = out_valid[ii-1];
          assign out_ready[ii-1]  = inp_ready[ii];
          assign inp_tag[ii].data = oup_tag[ii-1].data;

          `ifdef FPNEW_INTEGRATION
            assign inp_tag[ii].tag  = oup_tag[ii-1].tag;
          `endif

      end 
      assign handshake_o[ii] = inp_valid[ii] && inp_ready[ii];
        fpnew_fma_multi #(
         .FpFmtConfig ( FpFmtConfig       ),
         .NumPipeRegs ( FmaPipelineStages ),
         .PipeConfig  ( fpnew_pkg::BEFORE ),
         .TagType     ( TagDataType             ),
         .AuxType     ( logic             )
        ) i_fpnew_fma_multi(
            .clk_i           ( clk_i            ),
            .rst_ni          ( rst_ni           ),
            // Input signals
            .operands_i      ( operands[(ii+1)*3-1:ii*3]), // 3 operands
            .is_boxed_i      ( '1               ), // 3 operands
            .rnd_mode_i      ( fpnew_pkg::RNE   ),
            .op_i            ( fpnew_pkg::FMADD ),
            .op_mod_i        ( 1'b0             ),
            .src_fmt_i       ( fp_type_i        ), // format of the addend
            .dst_fmt_i       ( fp_type_i        ), // format of the addend
            .tag_i           ( inp_tag[ii]      ),
            .mask_i          ( '0               ),
            .aux_i           ( 1'b0             ),
            // Input Handshake
            .in_valid_i      ( inp_valid[ii]    ),
            .in_ready_o      ( inp_ready[ii]    ),
            .flush_i         ( flush_i          ),
            // Output signals
            .result_o        ( result[ii]       ),
            .status_o        ( status[ii]       ),
            .extension_bit_o (                  ),
            .tag_o           ( oup_tag[ii]      ),
            .mask_o          (                  ),
            .aux_o           (                  ),
            // Output handshake
            .out_valid_o     ( out_valid[ii]    ),
            .out_ready_i     ( out_ready[ii]    ),
            .busy_o          ( busy[ii]         )
            // External register enable override
          );
    end : gen_fma_cascaded
  // endgenerate
assign busy_o                = | busy;
assign out_valid_o           = out_valid[msb(PolyDegree)];
assign out_ready[msb(PolyDegree)] = out_ready_i;
assign status_o              = status[msb(PolyDegree)];
assign result_o              = result[msb(PolyDegree)];
`ifdef FPNEW_INTEGRATION
  assign tag_o = oup_tag[msb(PolyDegree)].tag;
`endif
endmodule