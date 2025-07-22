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

module partition_detector
  import pace_package::*;
#(
  parameter param_partition_fp_t Param,
  parameter pace_fp_mode_t       FPMode
)(
  input  logic [msb(Param.OpBits):0]         data_i,
  input  pace_fp_mode_t                      fp_type_i,
  input  logic [msb(Param.Bps*Param.OpBits):0] breakpoints_i,
  input  logic [Param.Bps-1:0]               enable_i,
  output logic [Param.PartBits-1:0]          partition_id_o,
  output logic                               bypass_o
);

  logic [Param.Bps-1:0] is_greater;

  generate
    if (FPMode == FP32) begin : gen_fp32
      for (genvar bp = 0; bp < Param.Bps; bp++) begin : gen_cmp
        fp_cmp_greater_than_multi_fp32 cmp_inst (
          .operand_a_i   ( data_i ),
          .operand_b_i   ( breakpoints_i[(bp+1)*Param.OpBits-1 -: Param.OpBits] ),
          .fp_type_i     ( fp_type_i ),
          .enable_i      ( enable_i[bp] ),
          .is_greater_o  ( is_greater[bp] )
        );
      end
    end else if (FPMode == FP16 || FPMode == BFP16) begin : gen_fp16
      for (genvar bp = 0; bp < Param.Bps; bp++) begin : gen_cmp
        fp_cmp_greater_than_multi_fp16 cmp_inst (
          .operand_a_i   ( data_i ),
          .operand_b_i   ( breakpoints_i[(bp+1)*Param.OpBits-1 -: Param.OpBits] ),
          .fp_type_i     ( fp_type_i ),
          .enable_i      ( enable_i[bp] ),
          .is_greater_o  ( is_greater[bp] )
        );
      end
    end else begin : gen_fp8
      for (genvar bp = 0; bp < Param.Bps; bp++) begin : gen_cmp
        fp_cmp_greater_than #(
          .ManBits ( Param.ManBits ),
          .ExpBits ( Param.ExpBits )
        ) cmp_inst (
          .operand_a_i   ( data_i ),
          .operand_b_i   ( breakpoints_i[(bp+1)*Param.OpBits-1 -: Param.OpBits] ),
          .enable_i      ( enable_i[bp] ),
          .is_greater_o  ( is_greater[bp] )
        );
      end
    end
  endgenerate

  logic [Param.PartBits:0] popcount_out;

  // Partition ID by popcount
  generate
    if (Param.Parts > 1) begin
      popcount #(
        .INPUT_WIDTH ( Param.Parts - 1 )
      ) i_popcount (
        .data_i     ( is_greater[Param.Parts-1:1] ),
        .popcount_o ( popcount_out )
      );
      assign partition_id_o = popcount_out[Param.PartBits-1:0];
    end else begin
      assign partition_id_o = '0;
    end
  endgenerate

  // Bypass detection
  assign bypass_o = ((is_greater == '0) && (data_i != breakpoints_i[Param.OpBits-1:0])) ||
                    (is_greater == {Param.Bps{1'b1}});

endmodule
