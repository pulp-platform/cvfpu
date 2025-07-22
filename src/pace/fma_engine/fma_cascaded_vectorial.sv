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

module fma_cascaded_vectorial 
  import pace_package::*;
#(
  parameter type TagType      = logic,
  parameter type TagDataType  = logic
)(
  input  logic                      clk_i,
  input  logic                      rst_ni,
  input  fpnew_pkg::fp_format_e     fp_type_i,
  input  ctrl_engine_t              ctrl_i,
  input  data_word_t                input_i,
`ifdef SUPPORT_MORE_PARTITIONS
  input  data_word_t                pres_i,
  input  logic [msb(CoeffMemRdPorts):0] bypass_i,
`else 
  `ifdef SUPPORT_MORE_DEGREES 
    input  data_word_t              pres_i,
  `endif 
`endif
`ifdef FPNEW_INTEGRATION 
  input  TagType                    tag_i,
  output TagType                    tag_o,
`endif 
  input  logic                      valid_i,
  output logic                      ready_o,
  input  coeff_rd_data_t            coeff_i,
  output data_word_t                result_o,
  output logic                      valid_o,
  output logic [msb(PolyDegree):0]  handshake_o,
  input  logic                      ready_i,
  input  logic                      flush_i,
  output logic                      busy_o
);

  // Internal vectors for each precision
  fp32_fma_vector_t fp32_vector;
  fp16_fma_vector_t fp16_vector;
  fp8_fma_vector_t  fp8_vector[2];

  // Precision mode detection
  logic mode_8b, mode_16b, mode_32b;
  assign mode_8b  = (ctrl_i.fp_mode == FP8);
  assign mode_16b = (ctrl_i.fp_mode == FP16) | (ctrl_i.fp_mode == BFP16);
  assign mode_32b = (ctrl_i.fp_mode == FP32);

`ifdef SUPPORT_MORE_PARTITIONS
  assign fp32_vector.bypass = mode_8b  ? bypass_i[3] :
                              mode_16b ? bypass_i[3] :
                                         bypass_i[0];

  assign fp16_vector.bypass = mode_8b ? bypass_i[2] : bypass_i[0];

  assign fp8_vector[1].bypass = bypass_i[1];
  assign fp8_vector[0].bypass = bypass_i[0];
`endif

assign fp32_vector.data[msb(DataByteBits):0] = mode_8b  ? input_i[msb(DataWordBits)              : DataHalfBits + DataByteBits] :
                                               mode_16b ? input_i[msb(DataHalfBits + DataByteBits): DataHalfBits] :
                                                          input_i[msb(DataByteBits):0];

assign fp32_vector.data[msb(DataHalfBits):DataByteBits] = mode_16b ? input_i[msb(DataWordBits)              : DataHalfBits + DataByteBits] :
                                                                     input_i[msb(DataHalfBits):DataByteBits];

assign fp32_vector.data[msb(DataWordBits):DataHalfBits] = input_i[msb(DataWordBits):DataHalfBits];

assign fp16_vector.data[msb(DataByteBits):0] = mode_8b ? input_i[msb(DataHalfBits + DataByteBits): DataHalfBits] :
                                                         input_i[msb(DataByteBits):0];

assign fp16_vector.data[msb(DataHalfBits):DataByteBits] = input_i[msb(DataHalfBits):DataByteBits];

assign fp8_vector[1].data[msb(DataByteBits):0] = input_i[msb(DataHalfBits):DataByteBits];

assign fp8_vector[0].data[msb(DataByteBits):0] = input_i[msb(DataByteBits):0];
`ifdef SUPPORT_MORE_PARTITIONS
  assign fp32_vector.pres[msb(DataByteBits):0] = mode_8b  ? pres_i[msb(DataWordBits)              : DataHalfBits + DataByteBits] :
                                                 mode_16b ? pres_i[msb(DataHalfBits + DataByteBits): DataHalfBits] :
                                                            pres_i[msb(DataByteBits):0];

  assign fp32_vector.pres[msb(DataHalfBits):DataByteBits] = mode_16b ? pres_i[msb(DataWordBits)              : DataHalfBits + DataByteBits] :
                                                                       pres_i[msb(DataHalfBits):DataByteBits];

  assign fp32_vector.pres[msb(DataWordBits):DataHalfBits] = pres_i[msb(DataWordBits):DataHalfBits];

  assign fp16_vector.pres[msb(DataByteBits):0] = mode_8b ? pres_i[msb(DataHalfBits + DataByteBits): DataHalfBits] :
                                                           pres_i[msb(DataByteBits):0];

  assign fp16_vector.pres[msb(DataHalfBits):DataByteBits] = pres_i[msb(DataHalfBits):DataByteBits];

  assign fp8_vector[1].pres[msb(DataByteBits):0] = pres_i[msb(DataHalfBits):DataByteBits];
  assign fp8_vector[0].pres[msb(DataByteBits):0] = pres_i[msb(DataByteBits):0];

`else
  `ifdef SUPPORT_MORE_DEGREES
    assign fp32_vector.pres[msb(DataByteBits):0] = mode_8b  ? pres_i[msb(DataWordBits)              : DataHalfBits + DataByteBits] :
                                                   mode_16b ? pres_i[msb(DataHalfBits + DataByteBits): DataHalfBits] :
                                                              pres_i[msb(DataByteBits):0];

    assign fp32_vector.pres[msb(DataHalfBits):DataByteBits] = mode_16b ? pres_i[msb(DataWordBits)              : DataHalfBits + DataByteBits] :
                                                                            pres_i[msb(DataHalfBits):DataByteBits];

    assign fp32_vector.pres[msb(DataWordBits):DataHalfBits] = pres_i[msb(DataWordBits):DataHalfBits];

    assign fp16_vector.pres[msb(DataByteBits):0] = mode_8b ? pres_i[msb(DataHalfBits + DataByteBits): DataHalfBits] :
                                                             pres_i[msb(DataByteBits):0];

    assign fp16_vector.pres[msb(DataHalfBits):DataByteBits] = pres_i[msb(DataHalfBits):DataByteBits];

    assign fp8_vector[1].pres[msb(DataByteBits):0] = pres_i[msb(DataHalfBits):DataByteBits];
    assign fp8_vector[0].pres[msb(DataByteBits):0] = pres_i[msb(DataByteBits):0];
  `endif
`endif

assign result_o[msb(DataByteBits):0] = mode_8b  ? fp8_vector[0].result[msb(DataByteBits):0] :
                                       mode_32b ? fp32_vector.result[msb(DataByteBits):0]    :
                                                  fp16_vector.result[msb(DataByteBits):0];

assign result_o[msb(DataHalfBits):DataByteBits] = mode_8b  ? fp8_vector[1].result[msb(DataByteBits):0] :
                                                  mode_32b ? fp32_vector.result[msb(DataHalfBits):DataByteBits] :
                                                             fp16_vector.result[msb(DataHalfBits):DataByteBits];

assign result_o[msb(DataHalfBits + DataByteBits):DataHalfBits] = mode_8b  ? fp16_vector.result[msb(DataByteBits):0] :
                                                                 mode_32b ? fp32_vector.result[msb(DataHalfBits + DataByteBits):DataHalfBits] :
                                                                            fp32_vector.result[msb(DataByteBits):0];

assign result_o[msb(DataWordBits):DataHalfBits + DataByteBits] = mode_8b  ? fp32_vector.result[msb(DataByteBits):0] :
                                                                 mode_32b ? fp32_vector.result[msb(DataWordBits):DataHalfBits + DataByteBits] :
                                                                            fp32_vector.result[msb(DataHalfBits):DataByteBits];



for (genvar degree = 0; degree < PolyNumCoeffs; degree++) begin
  // fp32[7:0]
  assign fp32_vector.coeff_flat[msb(degree * DataWordBits + DataByteBits) : degree * DataWordBits] = 
           mode_32b ? coeff_i[degree][msb(DataByteBits):0] :
           mode_8b  ? coeff_i[degree][msb(DataWordBits) : DataHalfBits + DataByteBits] :
                      coeff_i[degree][msb(DataHalfBits + DataByteBits) : DataHalfBits];

  // fp32[15:8]
  assign fp32_vector.coeff_flat[msb(degree * DataWordBits + DataHalfBits) : degree * DataWordBits + DataByteBits] = 
           mode_32b ? coeff_i[degree][msb(DataHalfBits):DataByteBits] :
                      coeff_i[degree][msb(DataWordBits):DataHalfBits + DataByteBits];

  // fp32[31:16]
  assign fp32_vector.coeff_flat[msb(degree * DataWordBits + DataWordBits) : degree * DataWordBits + DataHalfBits] =
           coeff_i[degree][msb(DataWordBits):DataHalfBits];

  // fp16[7:0] 
  assign fp16_vector.coeff_flat[msb(degree * DataHalfBits + DataByteBits) : degree * DataHalfBits] =
           mode_8b ? coeff_i[degree][msb(DataHalfBits + DataByteBits):DataHalfBits] :
                     coeff_i[degree][msb(DataByteBits):0];

  // fp16[15:8]
  assign fp16_vector.coeff_flat[msb(degree * DataHalfBits + DataHalfBits) : degree * DataHalfBits + DataByteBits] =
           coeff_i[degree][msb(DataHalfBits):DataByteBits];

  // fp8 vectors
  assign fp8_vector[1].coeff_flat[msb(degree * DataByteBits + DataByteBits) : degree * DataByteBits] =
           coeff_i[degree][msb(DataHalfBits):DataByteBits];

  assign fp8_vector[0].coeff_flat[msb(degree * DataByteBits + DataByteBits) : degree * DataByteBits] =
           coeff_i[degree][msb(DataByteBits):0];
end

fma_cascaded #(
  .OpBits         ( DataWordBits           ),
  .Width          ( 0                      ),
  .FpDataType     ( fp32_data_t            ),
  .CoeffDataType  ( fp32_coeff_t           ),
  .FpFmtConfig    ( VectorFmtConfig[3]     ),
  .NumPipeRegs    ( 0                      ),
  .TagType        ( TagType                )
) i_fma_cascaded_fp32 (
  .clk_i          ( clk_i                  ),
  .rst_ni         ( rst_ni                 ),
  .ctrl_i         ( ctrl_i                 ),
  .input_i        ( fp32_vector.data       ),
`ifdef SUPPORT_MORE_PARTITIONS
  .pres_i         ( fp32_vector.pres       ),
  .bypass_i       ( fp32_vector.bypass     ),
`else
  `ifdef SUPPORT_MORE_DEGREES
    .pres_i       ( fp32_vector.pres       ),
  `endif
`endif
`ifdef FPNEW_INTEGRATION
  .tag_i          ( tag_i                  ),
  .tag_o          ( tag_o                  ),
`endif
  .coeffs_i       ( fp32_vector.coeff_flat ),
  .fp_type_i      ( fp_type_i              ),
  .in_valid_i     ( valid_i                ),
  .in_ready_o     ( ready_o                ),
  .flush_i        ( 1'b0                   ),
  .result_o       ( fp32_vector.result     ),
  .handshake_o    ( handshake_o            ),
  .status_o       (                        ),
  .out_valid_o    ( valid_o                ),
  .out_ready_i    ( ready_i                ),
  .busy_o         ( busy_o                 )
);

fma_cascaded #(
  .OpBits         ( DataHalfBits           ),
  .Width          ( 0                      ),
  .FpDataType     ( fp16_data_t            ),
  .CoeffDataType  ( fp16_coeff_t           ),
  .FpFmtConfig    ( VectorFmtConfig[2]     ),
  .NumPipeRegs    ( 0                      )
) i_fma_cascaded_fp16 (
  .clk_i          ( clk_i                  ),
  .rst_ni         ( rst_ni                 ),
  .ctrl_i         ( ctrl_i                 ),
  .input_i        ( fp16_vector.data       ),
`ifdef SUPPORT_MORE_PARTITIONS
  .pres_i         ( fp16_vector.pres       ),
  .bypass_i       ( fp16_vector.bypass     ),
`else
  `ifdef SUPPORT_MORE_DEGREES
    .pres_i       ( fp16_vector.pres       ),
  `endif
`endif
`ifdef FPNEW_INTEGRATION
  .tag_i          (                        ),
  .tag_o          (                        ),
`endif
  .coeffs_i       ( fp16_vector.coeff_flat ),
  .fp_type_i      ( fp_type_i              ),
  .in_valid_i     ( valid_i                ),
  .in_ready_o     (                        ),
  .flush_i        ( 1'b0                   ),
  .result_o       ( fp16_vector.result     ),
  .handshake_o    (                        ),
  .status_o       (                        ),
  .out_valid_o    (                        ),
  .out_ready_i    ( ready_i                ),
  .busy_o         (                        )
);

for (genvar len = 0; len < 2; len++) begin : gen_FP8_fma_cascaded
  fma_cascaded #(
    .OpBits         ( DataByteBits              ),
    .Width          ( 0                         ),
    .FpDataType     ( fp8_data_t                ),
    .CoeffDataType  ( fp8_coeff_t               ),
    .FpFmtConfig    ( VectorFmtConfig[len]      ),
    .NumPipeRegs    ( 0                         )
  ) i_fma_cascaded_fp8 (
    .clk_i          ( clk_i                     ),
    .rst_ni         ( rst_ni                    ),
    .ctrl_i         ( ctrl_i                    ),
    .input_i        ( fp8_vector[len].data      ),
  `ifdef SUPPORT_MORE_PARTITIONS
    .pres_i         ( fp8_vector[len].pres      ),
    .bypass_i       ( fp8_vector[len].bypass    ),
  `else
    `ifdef SUPPORT_MORE_DEGREES
      .pres_i       ( fp8_vector[len].pres      ),
    `endif
  `endif
  `ifdef FPNEW_INTEGRATION
    .tag_i          (                           ),
    .tag_o          (                           ),
  `endif
    .coeffs_i       ( fp8_vector[len].coeff_flat ),
    .fp_type_i      ( fp_type_i                 ),
    .in_valid_i     ( valid_i                   ),
    .in_ready_o     (                           ),
    .flush_i        ( 1'b0                      ),
    .result_o       ( fp8_vector[len].result    ),
    .handshake_o    (                           ),
    .status_o       (                           ),
    .out_valid_o    (                           ),
    .out_ready_i    ( ready_i                   ),
    .busy_o         (                           )
  );
end : gen_FP8_fma_cascaded

endmodule