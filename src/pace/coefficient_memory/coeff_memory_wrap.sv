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

module coeff_memory_wrap
  import pace_package::*;
(
  input  logic                  clk_i,
  input  logic                  rst_ni,

  // Control channel
  input  ctrl_coeff_mem_t       ctrl_i,
  output flags_coeff_mem_t      flags_o,

  // Write port
  input  coeff_wr_data_t        data_i,
  input  logic                  valid_i,
  output logic                  ready_o,

  // Read port
  input  coeff_rd_addr_t        raddr_i,
  output coeff_rd_data_t        data_o,
  output logic                  valid_o,
  input  coeff_bypass_mask_t    bypass_i
);

  // Internal registers and control
  logic                      wdone_d, wdone_q;
  logic                      write_handshake;
  state_mem_t                state_d, state_q;
  coeff_wr_addr_comb_t       waddr_d, waddr_q;
  coeff_wr_addr_t            waddr;
  coeff_wr_enable_t          wenable;
  coeff_wr_enable_comb_t     wenable_d, wenable_q;
  coeff_rd_enable_t          renable;
  coeff_bypass_mask_t        bypass_q;
  coeff_rd_data_t            buf_data;

  for (genvar degree = 0; degree < PolyNumCoeffs; degree++) begin : gen_coeff_bypass_degree
    for (genvar port = 0; port < CoeffMemRdPorts; port++) begin : gen_coeff_bypass_ports
      assign data_o[degree][msb((port+1)*DataByteBits) : port*DataByteBits] =
        ~bypass_q[degree][port] ?
        buf_data[degree][msb((port+1)*DataByteBits) : port*DataByteBits] :
        {DataByteBits{1'b0}};
    end
  end

  assign write_handshake = valid_i & ready_o;

  assign wenable_d = ctrl_i.clear                                       ? '0 :
                     (state_q == MemIdle && ctrl_i.write.start)         ? 1  :
                     (waddr_q == ctrl_i.max_length && write_handshake)  ? (wenable_q << 1) :
                                                                        wenable_q;

  assign waddr_d = ctrl_i.clear                                        ? '0 :
                   (waddr_q == ctrl_i.max_length && write_handshake)   ? '0 :
                                                                      waddr_q + write_handshake;

  assign wdone_d = ctrl_i.clear ? 1'b0 :
                   ((wenable_q == ctrl_i.max_wenable) &&
                    valid_i &&
                    waddr_q == ctrl_i.max_length) ? 1'b1 :
                                                    wdone_q;

  assign ready_o            = (state_d == MemInitialize);
  assign valid_o            = ctrl_i.clear ? 1'b0 : (state_q == MemRead);
  assign flags_o.write_done = ctrl_i.clear ? 1'b0 : wdone_q;

  // FSM for state transition
  always_comb begin
    state_d = state_q;
    case (state_q)
      MemIdle:
        if (ctrl_i.write.start) state_d = MemInitialize;
      MemInitialize:
        if (wdone_q) state_d = MemRead;
      MemRead:
        if (ctrl_i.read_done) state_d = MemIdle;
    endcase
    if (ctrl_i.clear) state_d = MemIdle;
  end

  // State register
  always_ff @(posedge clk_i or negedge rst_ni) begin : state_save
    if (!rst_ni)
      state_q <= MemIdle;
    else
      state_q <= state_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : ctrl_signals
    if (!rst_ni) begin
      wdone_q   <= 1'b0;
      waddr_q   <= '0;
      wenable_q <= '0;
      bypass_q  <= '0;
    end else begin
      wdone_q   <= wdone_d;
      waddr_q   <= waddr_d;
      wenable_q <= wenable_d;
      bypass_q  <= bypass_i;
    end
  end

  // Replicate read enable across ports
  for (genvar bank = 0; bank < CoeffMem.NumBanks; bank++) begin : gen_renable
    assign renable[bank] = {CoeffMem.NumRdataPort{ctrl_i.renable[bank]}};
  end

  assign waddr   = waddr_q[msb(CoeffMemBankWrAddrBits * CoeffMemWrPorts) : 0];
  assign wenable = wenable_q[msb(CoeffMemNumBanks) : 0] & {CoeffMemNumBanks{valid_i}};

  // Coefficient memory instantiation
  coeff_memory i_coeff_mem (
    .clk_i     ( clk_i     ),
    .rst_ni    ( rst_ni    ),
    .renable_i ( renable   ),
    .wenable_i ( wenable   ),
    .raddr_i   ( raddr_i   ),
    .waddr_i   ( waddr     ),
    .rdata_o   ( buf_data  ),
    .wdata_i   ( data_i    )
  );

endmodule
