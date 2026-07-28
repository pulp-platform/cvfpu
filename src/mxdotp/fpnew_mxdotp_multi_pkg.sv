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

// Author: Gamze Islamoglu <gislamoglu@iis.ee.ethz.ch>

package fpnew_mxdotp_multi_pkg;
  // Configuration
  // One-hot config string: | FP32 | FP64 | FP16 | FP8 | FP16ALT | FP8ALT | FP6 | FP6ALT | FP4

  // Default format configuration (all MX formats enabled)
  // These define the maximum-width types and serve as defaults when not overridden by module parameters.
  localparam fpnew_pkg::fmt_logic_t   MxdotpSrcFpFmtConfig  = 9'b000101111; // FP8, FP8ALT, FP6, FP6ALT, FP4
  localparam fpnew_pkg::ifmt_logic_t  MxdotpSrcIntFmtConfig = 4'b1000;      // INT8
  localparam fpnew_pkg::fmt_logic_t   MxdotpDstFpFmtConfig  = 9'b100010000; // FP32, FP16ALT

  // Do not change
  localparam int unsigned SRC_WIDTH    = fpnew_pkg::max_fp_width(MxdotpSrcFpFmtConfig);
  localparam int unsigned DST_WIDTH    = fpnew_pkg::max_fp_width(MxdotpDstFpFmtConfig);
  localparam int unsigned SCALE_WIDTH  = 8;
  localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS;
  // ----------
  // Constants
  // ----------
  // The super-format that can hold all formats
  localparam fpnew_pkg::fp_encoding_t SUPER_FORMAT     = fpnew_pkg::super_format(MxdotpSrcFpFmtConfig);
  localparam fpnew_pkg::fp_encoding_t SUPER_DST_FORMAT = fpnew_pkg::super_format(MxdotpDstFpFmtConfig);

  localparam int unsigned SUPER_EXP_BITS     = SUPER_FORMAT.exp_bits;
  localparam int unsigned SUPER_MAN_BITS     = SUPER_FORMAT.man_bits;
  localparam int unsigned SUPER_DST_EXP_BITS = SUPER_DST_FORMAT.exp_bits;
  localparam int unsigned SUPER_DST_MAN_BITS = SUPER_DST_FORMAT.man_bits;

  // FP6 super format specific
  localparam fpnew_pkg::fp_encoding_t FP6_SUPER_FORMAT = fpnew_pkg::super_format(9'b000000110); // FP6 & FP6ALT
  localparam int unsigned FP6_EXP_BITS  = FP6_SUPER_FORMAT.exp_bits;
  localparam int unsigned FP6_MAN_BITS  = FP6_SUPER_FORMAT.man_bits;
  localparam int unsigned FP6_PREC_BITS = FP6_MAN_BITS + 1;

  // FP4 specific
  localparam int unsigned FP4_EXP_BITS  = fpnew_pkg::exp_bits(fpnew_pkg::FP4);
  localparam int unsigned FP4_MAN_BITS  = fpnew_pkg::man_bits(fpnew_pkg::FP4);
  localparam int unsigned FP4_PREC_BITS = FP4_MAN_BITS + 1;

  // Precision bits 'p' include the implicit bit
  localparam int unsigned PRECISION_BITS = SUPER_MAN_BITS + 1;
  // Destination precision bits 'p_dst' include the implicit bit
  localparam int unsigned DST_PRECISION_BITS = SUPER_DST_MAN_BITS + 1;

  // Algorithm constants
  localparam int unsigned ANCHOR               = 34; // Fractional point position
  localparam int unsigned INT_BITS             = 32;
  localparam int unsigned PROD_SHIFT_WIDTH     = 1 + INT_BITS + ANCHOR;
  localparam int unsigned SOP_SHIFT            = ANCHOR - 2*SUPER_MAN_BITS; // Constant left shift amount for the SOP to align the fractional point

  // FP6 specific
  localparam int unsigned FP6_PROD_WIDTH       = 2*FP6_PREC_BITS + 1; // 2p+1 for the product
  localparam int unsigned FP6_PROD_SHIFT_WIDTH = 2*(2**FP6_EXP_BITS-1-fpnew_pkg::bias(fpnew_pkg::FP6)) + FP6_PROD_WIDTH + 4; // 2*(2^e-1-bias) + 2p+1 + 4, (2^e-1-bias): max shift amount; +4 is due to the minimum value of the sum of exponents for FP6 (-4)

  // FP4 specific
  localparam int unsigned FP4_PROD_WIDTH       = 2*FP4_PREC_BITS + 1; // 2p+1 for the product
  localparam int unsigned FP4_PROD_SHIFT_WIDTH = 2*(2**FP4_EXP_BITS-1-fpnew_pkg::bias(fpnew_pkg::FP4)) + FP4_PROD_WIDTH; // 2*(2^e-1-bias) + 2p+1, (2^e-1-bias): max shift amount

  // Internal exponent width of FMA must accommodate all meaningful exponent values in order to avoid
  // datapath leakage. This is either given by the exponent bits or the width of the LZC result.
  // In most reasonable FP formats the internal exponent will be wider than the LZC result.
  localparam int unsigned EXP_WIDTH          = SUPER_EXP_BITS + 1;
  localparam int unsigned DST_EXP_WIDTH      = SUPER_DST_EXP_BITS + 2; // +2 for overflow handling

  // ----------------
  // Type definition
  // ----------------
  typedef struct packed {
    logic                      sign;
    logic [SUPER_EXP_BITS-1:0] exponent;
    logic [SUPER_MAN_BITS-1:0] mantissa;
  } fp_src_t;
  typedef struct packed {
    logic                    sign;
    logic [FP6_EXP_BITS-1:0] exponent;
    logic [FP6_MAN_BITS-1:0] mantissa;
  } fp6_src_t;
  typedef struct packed {
    logic                    sign;
    logic [FP4_EXP_BITS-1:0] exponent;
    logic [FP4_MAN_BITS-1:0] mantissa;
  } fp4_src_t;
  typedef struct packed {
    logic                          sign;
    logic [SUPER_DST_EXP_BITS-1:0] exponent;
    logic [SUPER_DST_MAN_BITS-1:0] mantissa;
  } fp_dst_t;

  // ----------
  // Functions
  // ----------

  // Returns the MXDOTP destination format config from the global FpFmtConfig.
  // Only FP32 and FP16ALT are valid destination formats for MXDOTP.
  function automatic fpnew_pkg::fmt_logic_t get_mxdotp_dst_fmts(fpnew_pkg::fmt_logic_t cfg);
    automatic fpnew_pkg::fmt_logic_t res;
    res = { cfg[fpnew_pkg::FP32],    // FP32
            1'b0,                    // FP64
            1'b0,                    // FP16
            1'b0,                    // FP8
            cfg[fpnew_pkg::FP16ALT], // FP16ALT
            1'b0,                    // FP8ALT
            1'b0,                    // FP6
            1'b0,                    // FP6ALT
            1'b0                     // FP4
    };
    return res;
  endfunction

  function automatic int unsigned bias_constant(fpnew_pkg::fp_format_e fmt);
    unique case (fmt)
      fpnew_pkg::FP32:    return 127; // 2^(8-1) - 1
      fpnew_pkg::FP16:    return 15;  // 2^(5-1) - 1
      fpnew_pkg::FP16ALT: return 127; // 2^(8-1) - 1,
      fpnew_pkg::FP8:     return 15;  // 2^(5-1) - 1
      fpnew_pkg::FP8ALT:  return 7;   // 2^(4-1) - 1
      fpnew_pkg::FP6:     return 3;   // 2^(3-1) - 1
      fpnew_pkg::FP6ALT:  return 1;   // 2^(2-1) - 1
      fpnew_pkg::FP4:     return 1;   // 2^(2-1) - 1
      default:            return fpnew_pkg::bias(fmt);
    endcase
  endfunction

endpackage
