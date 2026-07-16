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

// Selects the Horner-ordered coefficients for one partition:
// coeffs_i[0] is the leading term and coeffs_i[degree_i] is the current addend.
module fpnew_pace_coeff_select #(
  parameter int unsigned Bounds      = 7,
  parameter int unsigned Degrees     = 2,
  parameter int unsigned Width       = 32,
  parameter int unsigned BoundStages = $clog2(Bounds),
  parameter int unsigned DegreesBits = $clog2(Degrees + 1)
) (
  input  logic [Degrees:0][Bounds-1:0][Width-1:0] coeffs_i,
  input  logic [BoundStages-1:0]                  bound_i,
  input  logic [DegreesBits-1:0]                  degree_i,
  output logic [1:0][Width-1:0]                   coeffs_o
);

  assign coeffs_o[0] = coeffs_i[0][bound_i];
  assign coeffs_o[1] = coeffs_i[degree_i][bound_i];

endmodule
