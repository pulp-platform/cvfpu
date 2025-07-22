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

module coeff_addr_generator
  import pace_package::*;
(
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  logic [msb(PolyDegree):0]     fma_handshake_i,
  input  logic                         inp_handshake_i,
  input  coeff_bypass_addr_bank_t      coeff_raddr_bypass_i,
  output coeff_rd_addr_t               coeff_raddr_o,
  output coeff_bypass_mask_t           coeff_bypass_o
);

  localparam DataWidth  = (CoeffMemBankRdAddrBits + 1) * CoeffMemRdPorts;
  localparam Depth      = PolyNumCoeffs;
  localparam AddrWidth  = $clog2(Depth);

  coeff_bypass_addr_bank_t coeff_raddr_bypass_array         [msb(PolyDegree):0];
  coeff_bypass_addr_bank_t next_coeff_raddr_bypass_array    [msb(PolyDegree):0];

  logic [msb(PolyDegree):0][msb(AddrWidth):0] n_elements;

  // FIFO for each polynomial degree
  for (genvar ii = 0; ii < PolyDegree; ii++) begin
    pace_stream_fifo #(
      .FALL_THROUGH ( 1'b1                    ),
      .DATA_WIDTH   ( DataWidth              ),
      .DEPTH        ( Depth                  ),
      .T            ( coeff_bypass_addr_bank_t )
    ) i_stream_fifo (
      .clk_i        ( clk_i                         ),
      .rst_ni       ( rst_ni                        ),
      .flush_i      ( 1'b0                          ),
      .testmode_i   ( 1'b0                          ),
      .data_i       ( coeff_raddr_bypass_i          ),
      .valid_i      ( inp_handshake_i               ),
      .ready_o      (                               ),
      .usage_o      ( n_elements[ii]                ),
      .next_data_o  ( next_coeff_raddr_bypass_array[ii] ),
      .data_o       ( coeff_raddr_bypass_array[ii]  ),
      .valid_o      (                               ),
      .ready_i      ( fma_handshake_i[ii]           )
    );
  end

  // Routing logic for coefficient address and bypass
  for (genvar ii = 0; ii < CoeffMemNumBanks; ii++) begin
    for (genvar jj = 0; jj < CoeffMemRdPorts; jj++) begin
      if (ii < 2) begin
        localparam kk = 0;
        assign coeff_raddr_o[ii][msb((jj+1)*CoeffMemBankRdAddrBits) : jj*CoeffMemBankRdAddrBits] =
               fma_handshake_i[kk] ?
               next_coeff_raddr_bypass_array[kk][msb((jj+1)*CoeffMemBankRdAddrBits) : jj*CoeffMemBankRdAddrBits] :
               coeff_raddr_bypass_array[kk][msb((jj+1)*CoeffMemBankRdAddrBits) : jj*CoeffMemBankRdAddrBits];

        assign coeff_bypass_o[ii][jj] =
               fma_handshake_i[kk] ?
               next_coeff_raddr_bypass_array[kk][CoeffMemBankRdAddrBits*CoeffMemRdPorts + jj] :
               coeff_raddr_bypass_array[kk][CoeffMemBankRdAddrBits*CoeffMemRdPorts + jj];
      end else begin
        localparam kk = ii - 1;
        assign coeff_raddr_o[ii][msb((jj+1)*CoeffMemBankRdAddrBits) : jj*CoeffMemBankRdAddrBits] =
               fma_handshake_i[kk] ?
               next_coeff_raddr_bypass_array[kk][msb((jj+1)*CoeffMemBankRdAddrBits) : jj*CoeffMemBankRdAddrBits] :
               coeff_raddr_bypass_array[kk][msb((jj+1)*CoeffMemBankRdAddrBits) : jj*CoeffMemBankRdAddrBits];

        assign coeff_bypass_o[ii][jj] =
               fma_handshake_i[kk] ?
               next_coeff_raddr_bypass_array[kk][CoeffMemBankRdAddrBits*CoeffMemRdPorts + jj] :
               coeff_raddr_bypass_array[kk][CoeffMemBankRdAddrBits*CoeffMemRdPorts + jj];
      end
    end
  end

endmodule
