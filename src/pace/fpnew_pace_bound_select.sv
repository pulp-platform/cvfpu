// Copyright 2025 ETH Zurich and University of Bologna.
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

// Selects the bound value used by one binary-search-tree stage.
module fpnew_pace_bound_select #(
  parameter int unsigned Bounds   = 4,
  parameter int unsigned Width    = 32,
  parameter int unsigned BoundSel = Bounds == 1 ? 1 : $clog2(Bounds)
) (
  input  logic [Bounds-1:0][Width-1:0] bounds_i,
  input  logic [BoundSel-1:0]          sel_i,
  output logic [Width-1:0]             result_o
);

// Avoid indexing with a zero-width selector when only one bound exists.
assign result_o     = Bounds == 1 ? bounds_i[0] : bounds_i[sel_i];

endmodule
