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

module spill_register_pipeline 
  import pace_package::*;
#(
  parameter type T            = logic,
  parameter bit  Bypass       = 1'b1,
  parameter int  PipelineStages = 0
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic valid_i,
  output logic ready_o,
  input  T     data_i,
  output logic valid_o,
  input  logic ready_i,
  output T     data_o
);

generate 
  if (PipelineStages == 0) begin : gen_no_pipeline
    assign data_o  = data_i;
    assign valid_o = valid_i;
    assign ready_o = ready_i;
  end else begin : gen_with_pipeline
    T     inp_data_array [PipelineStages-1:0];
    logic inp_valid_array[PipelineStages-1:0];
    logic inp_ready_array[PipelineStages-1:0];

    T     oup_data_array [PipelineStages-1:0];
    logic oup_valid_array[PipelineStages-1:0];
    logic oup_ready_array[PipelineStages-1:0];

    for (genvar stage = 0; stage < PipelineStages; stage++) begin
      if (stage == 0) begin
        assign inp_data_array[stage]  = data_i;
        assign inp_valid_array[stage] = valid_i;
        assign ready_o                = inp_ready_array[stage];
      end else begin
        assign inp_data_array[stage]  = oup_data_array [stage-1];
        assign inp_valid_array[stage] = oup_valid_array[stage-1];
        assign oup_ready_array[stage-1] = inp_ready_array[stage];
      end

      spill_register #(
        .T     (T),
        .Bypass(Bypass)
      ) i_spill_register (
        .clk_i    ( clk_i  ),
        .rst_ni   ( rst_ni ),
        .valid_i  ( inp_valid_array[stage] ),
        .ready_o  ( inp_ready_array[stage] ),
        .data_i   ( inp_data_array[stage]  ),
        .valid_o  ( oup_valid_array[stage] ),
        .ready_i  ( oup_ready_array[stage] ),
        .data_o   ( oup_data_array[stage]  )
      );
    end

    assign data_o   = oup_data_array[PipelineStages-1];
    assign valid_o  = oup_valid_array[PipelineStages-1];
    assign oup_ready_array[PipelineStages-1] = ready_i;
  end
endgenerate

endmodule
