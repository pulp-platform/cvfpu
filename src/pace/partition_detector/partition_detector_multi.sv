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

module partition_detector_multi
  import pace_package::*;
(
  input  logic clk_i,
  input  logic rst_ni,

  input  ctrl_partition_t      ctrl_i,
  output flags_partition_t     flags_o,

  input  logic [msb(DataWordBits):0] bp_data_i,
  input  logic                       bp_valid_i,
  output logic                       bp_ready_o,

  input  logic [msb(DataWordBits):0] feat_data_i,
  input  logic                       feat_valid_i,
  output logic                       feat_ready_o,
  output logic [msb(DataWordBits):0] feat_data_o,
  output logic                       feat_valid_o,
  input  logic                       feat_ready_i,

  output logic [msb(CoeffMemRdPorts):0] bypass_o,
  output coeff_bypass_addr_bank_t       coeff_raddr_bypass_o
);

  fp32_partition_vector_t  fp32_vector;
  fp16_partition_vector_t  fp16_vector;
  fp16_partition_vector_t  bfp16_vector;
  fp8_partition_vector_t   fp8_vector;

  // Breakpoint Storage
  bp_rd_data_t bps;

  // Internal Handshake Signals
  logic bp_ready, bp_valid;
  logic partition_ready, partition_valid;

  assign feat_ready_o = flags_o.bp_mem.init_done ? feat_ready_i : 1'b0;
  assign feat_valid_o = flags_o.bp_mem.init_done ? feat_valid_i : 1'b0;
  assign feat_data_o  = feat_data_i;

  coeff_bypass_addr_bank_t coeff_raddr_bypass;

  for (genvar ii = 0; ii < CoeffMemRdPorts; ii++) begin
    assign coeff_raddr_bypass_o[msb((ii+1)*CoeffMemBankRdAddrBits) : ii*CoeffMemBankRdAddrBits] =
           (ctrl_i.fp_mode == FP32 ) ? fp32_vector.coeff_raddr[msb((ii+1)*CoeffMemBankRdAddrBits) : ii*CoeffMemBankRdAddrBits] :
           (ctrl_i.fp_mode == FP16 ) ? fp16_vector.coeff_raddr[msb((ii+1)*CoeffMemBankRdAddrBits) : ii*CoeffMemBankRdAddrBits] :
           (ctrl_i.fp_mode == BFP16) ? bfp16_vector.coeff_raddr[msb((ii+1)*CoeffMemBankRdAddrBits) : ii*CoeffMemBankRdAddrBits] :
                                       fp8_vector.coeff_raddr[msb((ii+1)*CoeffMemBankRdAddrBits) : ii*CoeffMemBankRdAddrBits];

    assign coeff_raddr_bypass_o[CoeffMemRdPorts*CoeffMemBankRdAddrBits + ii] =
           (ctrl_i.fp_mode == FP32 ) ? fp32_vector.out_bypass[ii] :
           (ctrl_i.fp_mode == FP16 ) ? fp16_vector.out_bypass[ii] :
           (ctrl_i.fp_mode == BFP16) ? bfp16_vector.out_bypass[ii] :
                                       fp8_vector.out_bypass[ii];

    assign bypass_o[ii] =
           (ctrl_i.fp_mode == FP32 ) ? fp32_vector.out_bypass[ii] :
           (ctrl_i.fp_mode == FP16 ) ? fp16_vector.out_bypass[ii] :
           (ctrl_i.fp_mode == BFP16) ? bfp16_vector.out_bypass[ii] :
                                       fp8_vector.out_bypass[ii];
  end


  for (genvar len = 0; len < DataScaleFromWord; len++) begin : fp32_len_map
    for (genvar width = 0; width < DataScaleFromByte; width++) begin : fp32_data_map
      localparam int index = len * DataScaleFromByte + width;

      assign fp32_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                    index * CoeffMemBankRdAddrBits] =
                                    DataScaleFromByte * fp32_vector.part_id[len] + width;

      assign fp32_vector.out_bypass[msb(index + 1) : index] = fp32_vector.bypass[len];
    end : fp32_data_map
  end : fp32_len_map

  for (genvar len = 0; len < DataScaleFromHalf; len++) begin : fp16_len_map  // Handles 2 data groups
    for (genvar width = 0; width < DataScaleFromHalf; width++) begin : fp16_data_map  // Each group contains 2 elements
      localparam int index = len * DataScaleFromHalf + width;

      if (len == 0) begin
        assign fp16_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                      index * CoeffMemBankRdAddrBits] =
                                      DataScaleFromHalf * fp16_vector.part_id[len] + width;

        assign bfp16_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                       index * CoeffMemBankRdAddrBits] =
                                       DataScaleFromHalf * fp16_vector.part_id[len] + width;

        assign fp16_vector.out_bypass[msb(index + 1) : index]  = fp16_vector.bypass[len];
        assign bfp16_vector.out_bypass[msb(index + 1) : index] = fp16_vector.bypass[len];

      end else begin
        assign fp16_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                      index * CoeffMemBankRdAddrBits] =
                                      DataScaleFromHalf * fp32_vector.part_id[0] + width;

        assign bfp16_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                       index * CoeffMemBankRdAddrBits] =
                                       DataScaleFromHalf * fp32_vector.part_id[0] + width;

        assign fp16_vector.out_bypass[msb(index + 1) : index]  = fp32_vector.bypass[0];
        assign bfp16_vector.out_bypass[msb(index + 1) : index] = fp32_vector.bypass[0];
      end
    end : fp16_data_map
  end : fp16_len_map

  for (genvar len = 0; len < DataScaleFromByte; len++) begin : fp8_len_map
    for (genvar width = 0; width < DataScaleFromWord; width++) begin : fp8_data_map
      localparam int index = len * DataScaleFromWord + width;

      if (len < 2) begin
        assign fp8_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                     index * CoeffMemBankRdAddrBits] =
                                     DataScaleFromWord * fp8_vector.part_id[len];

        assign fp8_vector.out_bypass[msb(len + 1) : len] = fp8_vector.bypass[len];

      end else if (len == 2) begin
        assign fp8_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                     index * CoeffMemBankRdAddrBits] =
                                     DataScaleFromWord * fp16_vector.part_id[0];

        assign fp8_vector.out_bypass[msb(len + 1) : len] = fp16_vector.bypass[0];

      end else if (len == 3) begin
        assign fp8_vector.coeff_raddr[msb((index + 1) * CoeffMemBankRdAddrBits) :
                                     index * CoeffMemBankRdAddrBits] =
                                     DataScaleFromWord * fp32_vector.part_id[0];

        assign fp8_vector.out_bypass[msb(len + 1) : len] = fp32_vector.bypass[0];
      end
    end : fp8_data_map
  end : fp8_len_map


  for (genvar bp = 0; bp < PartitionFP32Bps; bp++) begin : gen_fp32_bp_vec_map
    localparam int quo = bp / DataScaleFromWord;
    localparam int rem = bp % DataScaleFromWord;

    assign fp32_vector.bps[msb((bp + 1) * DataWordBits) : bp * DataWordBits] =
           bps[quo][msb((rem + 1) * DataWordBits) : rem * DataWordBits];

    assign fp16_vector.bps[msb((bp + 1) * DataHalfBits) : bp * DataHalfBits] =
           bps[quo][msb((rem + 1) * DataWordBits - DataHalfBits) :
                           rem * DataWordBits];

    assign fp8_vector.bps[msb((bp + 1) * DataByteBits) : bp * DataByteBits] =
           bps[quo][msb((rem + 1) * DataWordBits - DataHalfBits - DataByteBits) :
                           rem * DataWordBits];

    for (genvar len = 0; len < DataScaleFromWord; len++) begin : fp32_len_map
      assign fp32_vector.enable[len][bp] = 
        ((ctrl_i.fp_mode == FP32)  || 
         (ctrl_i.fp_mode == FP16)  || 
         (ctrl_i.fp_mode == BFP16) || 
         (ctrl_i.fp_mode == FP8)) ? ctrl_i.part_enable_fp32[bp] : 1'b0;

      assign fp16_vector.enable[len][bp] = 
        ((ctrl_i.fp_mode == FP16)  || 
         (ctrl_i.fp_mode == BFP16) || 
         (ctrl_i.fp_mode == FP8)) ? ctrl_i.part_enable_fp32[bp] : 1'b0;
    end : fp32_len_map  

    for (genvar len = 0; len < DataScaleFromHalf; len++) begin : fp8_len_map
      assign fp8_vector.enable[len][bp] =
        (ctrl_i.fp_mode == FP8) ? ctrl_i.part_enable_fp8[bp] : 1'b0;
    end : fp8_len_map
  end : gen_fp32_bp_vec_map

  for (genvar len = 0; len < DataScaleFromWord; len++) begin : fp32_data_map
    assign fp32_vector.data_in[len] = 
      (ctrl_i.fp_mode == pace_package::FP32)   ? feat_data_i[msb((len + 1) * DataWordBits) : len * DataWordBits] :
      (ctrl_i.fp_mode == pace_package::FP16)   ? feat_data_i[msb((len + 1) * DataWordBits) : DataHalfBits] :
      (ctrl_i.fp_mode == pace_package::BFP16)  ? feat_data_i[msb((len + 1) * DataWordBits) : DataHalfBits] :
                                                 feat_data_i[msb((len + 1) * DataWordBits) : (DataHalfBits + DataByteBits)];

    assign fp16_vector.data_in[len] = 
      (ctrl_i.fp_mode == pace_package::FP16)   ? feat_data_i[msb((len + 1) * DataHalfBits) : 0] :
      (ctrl_i.fp_mode == pace_package::BFP16)  ? feat_data_i[msb((len + 1) * DataHalfBits) : 0] :
                                                 feat_data_i[msb((len + 1) * (DataHalfBits + DataByteBits)) : DataHalfBits];
  end : fp32_data_map

  for (genvar len = 0; len < DataScaleFromHalf; len++) begin : fp8_data_map
    assign fp8_vector.data_in[len] = 
      feat_data_i[msb((len + 1) * DataByteBits) : len * DataByteBits];
  end : fp8_data_map

  // FP32 partition detectors
  for (genvar len = 0; len < DataScaleFromWord; len++) begin : partition_detector_fp32
    partition_detector #(
      .Param  ( ParamPartitionFP32 ),
      .FPMode ( pace_package::FP32 )
    ) i_fp32_detector (
      .fp_type_i      ( ctrl_i.fp_mode           ),
      .data_i         ( fp32_vector.data_in[len] ),
      .breakpoints_i  ( fp32_vector.bps          ),
      .enable_i       ( fp32_vector.enable[len]  ),
      .partition_id_o ( fp32_vector.part_id[len] ),
      .bypass_o       ( fp32_vector.bypass[len]  )
    );
  end : partition_detector_fp32

  // FP16/BFP16 partition detectors
  for (genvar len = 0; len < DataScaleFromWord; len++) begin : partition_detector_fp16
    partition_detector #(
      .Param  ( ParamPartitionFP16 ),
      .FPMode ( pace_package::FP16 )
    ) i_fp16_detector (
      .fp_type_i      ( ctrl_i.fp_mode           ),
      .data_i         ( fp16_vector.data_in[len] ),
      .breakpoints_i  ( fp16_vector.bps          ),
      .enable_i       ( fp16_vector.enable[len]  ),
      .partition_id_o ( fp16_vector.part_id[len] ),
      .bypass_o       ( fp16_vector.bypass[len]  )
    );
  end : partition_detector_fp16

  // FP8 partition detectors
  for (genvar len = 0; len < DataScaleFromHalf; len++) begin : partition_detector_fp8
    partition_detector #(
      .Param  ( ParamPartitionFP8 ),
      .FPMode ( pace_package::FP8 )
    ) i_fp8_detector (
      .fp_type_i      ( ctrl_i.fp_mode          ),
      .data_i         ( fp8_vector.data_in[len] ),
      .breakpoints_i  ( fp8_vector.bps          ),
      .enable_i       ( fp8_vector.enable[len]  ),
      .partition_id_o ( fp8_vector.part_id[len] ),
      .bypass_o       ( fp8_vector.bypass[len]  )
    );
  end : partition_detector_fp8

  logic bp_oup_valid;

  breakpoint_memory #(
    .Param ( BpMem )
  ) i_breakpoint_memory (
    .clk_i    ( clk_i           ),
    .rst_ni   ( rst_ni          ),
    .ctrl_i   ( ctrl_i.bp_mem   ),
    .flags_o  ( flags_o.bp_mem  ),
    .data_i   ( bp_data_i       ),
    .valid_i  ( bp_valid_i      ),
    .ready_o  ( bp_ready_o      ),
    .data_o   ( bps     ),
    .valid_o  ( bp_oup_valid    )
  );

endmodule 