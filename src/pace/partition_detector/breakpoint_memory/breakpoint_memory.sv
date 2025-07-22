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

module breakpoint_memory
  import pace_package::*;
#(
  param_memory_t Param = BpMem
)(
  input  logic              clk_i,
  input  logic              rst_ni,

  // Control channel
  input  ctrl_bp_mem_t      ctrl_i,
  output flags_bp_mem_t     flags_o,

  // Write port
  input  data_word_t        data_i,
  input  logic              valid_i,
  output logic              ready_o,

  // Read port
  output bp_rd_data_t       data_o,
  output logic              valid_o
);

  // Internal signals
  logic             wdone_d, wdone_q;
  state_mem_t       state_d, state_q;
  bp_wr_addr_t      waddr_d, waddr_q;
  logic             write_handshake;

  assign write_handshake = valid_i & ready_o;

  // Write address logic
  assign waddr_d = ctrl_i.clear ? '0 :
                   (waddr_q == ctrl_i.max_length && write_handshake) ? '0 :
                   waddr_q + write_handshake;

  // Write done flag logic
  assign wdone_d = ctrl_i.clear ? 1'b0 :
                   (valid_i && waddr_q == ctrl_i.max_length) ? 1'b1 :
                   wdone_q;

  // Ready/Valid outputs
  assign ready_o           = (state_d == MemInitialize);
  assign valid_o           = ctrl_i.clear ? 1'b0 : (state_q == MemRead);
  assign flags_o.init_done = ctrl_i.clear ? 1'b0 : wdone_q;

  // FSM next state logic
  always_comb begin
    state_d = state_q;
    case (state_q)
      MemIdle:
        if (ctrl_i.write.start) state_d = MemInitialize;
      MemInitialize:
        if (wdone_q) state_d = MemRead;
      MemRead:
        state_d = MemRead;
    endcase
    if (ctrl_i.clear) state_d = MemIdle;
  end

  // FSM state register
  always_ff @(posedge clk_i or negedge rst_ni) begin : state_save
    if (!rst_ni) begin
      state_q <= MemIdle;
    end else begin
      state_q <= state_d;
    end
  end

  // Write address and control signals
  always_ff @(posedge clk_i or negedge rst_ni) begin : ctrl_signals
    if (!rst_ni) begin
      wdone_q <= 1'b0;
      waddr_q <= '0;
    end else begin
      wdone_q <= wdone_d;
      waddr_q <= waddr_d;
    end
  end

  // Memory content for unpacked read
  logic [msb(BpMemWrLength * BpMemRdWidth):0] data_mem;

  for (genvar i = 0; i < BpMemWrLength; i++) begin : unpack_mem
    assign data_o[i] = data_mem[msb((i + 1) * BpMemRdWidth) : i * BpMemRdWidth];
  end

  // Memory instantiation
  register_file_bp #(
    .ADDR_WIDTH ( Param.WaddrWidth  ),
    .DATA_WIDTH ( Param.WdataWidth  ),
    .NUM_WORDS  ( Param.WriteLength )
  ) i_breakpoint_memory (
    .clk         ( clk_i           ),
    .WriteEnable ( write_handshake ),
    .WriteAddr   ( waddr_q         ),
    .WriteData   ( data_i          ),
    .WriteBE     ( '1              ),
    .ReadEnable  ( '0              ),
    .ReadAddr    ( '0              ),
    .ReadData    (                 ),
    .MemContent  ( data_mem        )
  );

endmodule
