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

module coeff_memory
  import pace_package::*;
#(
  param_memory_t Param = CoeffMem
)(
  input  logic                clk_i,
  input  logic                rst_ni,
  input  coeff_rd_enable_t   renable_i,
  input  coeff_wr_enable_t   wenable_i,
  input  coeff_rd_addr_t     raddr_i,  // Degree x [4 x partitions]
  input  coeff_wr_addr_t     waddr_i,
  output coeff_rd_data_t     rdata_o,
  input  coeff_wr_data_t     wdata_i
);

  for (genvar bank_idx = 0; bank_idx < CoeffMem.NumBanks; bank_idx++) begin : gen_coeff_memory

    logic [msb(CoeffMem.NumRdataPort):0][msb(DataByteBits):0]             read_data;
    logic [msb(CoeffMem.NumRdataPort):0][msb(CoeffMem.BankRaddrWidth):0]  read_addr;

    for (genvar port_idx = 0; port_idx < DataScaleFromByte; port_idx++) begin
      assign rdata_o[bank_idx][msb((port_idx + 1) * DataByteBits) : port_idx * DataByteBits] = read_data[port_idx];
      assign read_addr[port_idx] = raddr_i[bank_idx][msb((port_idx + 1) * CoeffMem.BankRaddrWidth) : port_idx * CoeffMem.BankRaddrWidth];
    end

    register_file_1w_32b_multi_port_read_8b #(
      .WADDR_WIDTH ( CoeffMem.BankWaddrWidth ),
      .WDATA_WIDTH ( CoeffMem.WdataWidth     ),
      .RDATA_WIDTH ( CoeffMem.RdataWidth     )
    ) i_regfile (
      .clk         ( clk_i               ),
      .ReadEnable  ( renable_i[bank_idx] ),
      .ReadAddr    ( read_addr           ),
      .ReadData    ( read_data           ),
      .WriteEnable ( wenable_i[bank_idx] ),
      .WriteAddr   ( waddr_i             ),
      .WriteData   ( wdata_i             )
    );

  end

endmodule
