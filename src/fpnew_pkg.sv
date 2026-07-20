// Copyright 2019 ETH Zurich and University of Bologna.
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

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

package fpnew_pkg;

  // ---------
  // FP TYPES
  // ---------
  // | Enumerator | Format           | Width  | EXP_BITS | MAN_BITS
  // |:----------:|------------------|-------:|:--------:|:--------:
  // | FP32       | IEEE binary32    | 32 bit | 8        | 23
  // | FP64       | IEEE binary64    | 64 bit | 11       | 52
  // | FP16       | IEEE binary16    | 16 bit | 5        | 10
  // | FP8        | binary8          |  8 bit | 5        | 2
  // | FP16ALT    | binary16alt      | 16 bit | 8        | 7
  // | FP8ALT     | binary8alt       |  8 bit | 4        | 3
  // | FP6        | binary6          |  6 bit | 3        | 2
  // | FP6ALT     | binary6alt       |  6 bit | 2        | 3
  // | FP4        | binary4          |  4 bit | 2        | 1
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  // Encoding for a format
  typedef struct packed {
    int unsigned exp_bits;
    int unsigned man_bits;
  } fp_encoding_t;

  localparam int unsigned NUM_FP_FORMATS = 9; // change me to add formats
  localparam int unsigned FP_FORMAT_BITS = $clog2(NUM_FP_FORMATS);

  // FP formats
  typedef enum logic [FP_FORMAT_BITS-1:0] {
    FP32    = 'd0,
    FP64    = 'd1,
    FP16    = 'd2,
    FP8     = 'd3,
    FP16ALT = 'd4,
    FP8ALT  = 'd5,
    FP6     = 'd6,
    FP6ALT  = 'd7,
    FP4     = 'd8
    // add new formats here
  } fp_format_e;

  // Encodings for supported FP formats
  localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
    '{8,  23}, // IEEE binary32 (single)
    '{11, 52}, // IEEE binary64 (double)
    '{5,  10}, // IEEE binary16 (half)
    '{5,  2},  // custom binary8
    '{8,  7},  // custom binary16alt
    '{4,  3},  // custom binary8alt
    '{3,  2},  // custom binary6
    '{2,  3},  // custom binary6alt
    '{2,  1}   // custom binary4
    // add new formats here
  };

  typedef logic [0:NUM_FP_FORMATS-1]       fmt_logic_t;    // Logic indexed by FP format (for masks)
  typedef logic [0:NUM_FP_FORMATS-1][31:0] fmt_unsigned_t; // Unsigned indexed by FP format

  localparam fmt_logic_t CPK_FORMATS  = 9'b110000000; // FP32 and FP64 can provide CPK only
  // FP32, FP64 cannot be provided for DOTP
  // Small hack: FP32 only enabled for wide enough wrapper input widths for vsum.s instruction
  localparam fmt_logic_t DOTP_FORMATS = 9'b101111000;

  // ---------
  // INT TYPES
  // ---------
  // | Enumerator | Width  |
  // |:----------:|-------:|
  // | INT8       |  8 bit |
  // | INT16      | 16 bit |
  // | INT32      | 32 bit |
  // | INT64      | 64 bit |
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  localparam int unsigned NUM_INT_FORMATS = 4; // change me to add formats
  localparam int unsigned INT_FORMAT_BITS = $clog2(NUM_INT_FORMATS);

  // Int formats
  typedef enum logic [INT_FORMAT_BITS-1:0] {
    INT8,
    INT16,
    INT32,
    INT64
    // add new formats here
  } int_format_e;

  // Returns the width of an INT format by index
  function automatic int unsigned int_width(int_format_e ifmt);
    unique case (ifmt)
      INT8:  return 8;
      INT16: return 16;
      INT32: return 32;
      INT64: return 64;
      default: begin
        // pragma translate_off
        $fatal(1, "Invalid INT format supplied");
        // pragma translate_on
        // just return any integer to avoid any latches
        // hopefully this error is caught by simulation
        return INT8;
      end
    endcase
  endfunction

  typedef logic [0:NUM_INT_FORMATS-1] ifmt_logic_t; // Logic indexed by INT format (for masks)

  // Combined format struct for operations that need FP, INT, and destination formats
  typedef struct packed {
    fmt_logic_t  src_fp_formats;
    ifmt_logic_t src_int_formats;
    fmt_logic_t  dst_fp_formats;
  } lane_formats_t;

  // MXDOTP format masks
  localparam lane_formats_t MXDOTP_FORMATS_MASK = '{
    src_fp_formats:  9'b000101111,  // FP8, FP8ALT, FP6, FP6ALT, FP4
    src_int_formats: 4'b1000,       // INT8
    dst_fp_formats:  9'b100010000   // FP32, FP16ALT
  };

  // --------------
  // FP OPERATIONS
  // --------------
  localparam int unsigned NUM_OPGROUPS = 6;

  // Each FP operation belongs to an operation group
  typedef enum logic [2:0] {
    ADDMUL, DIVSQRT, NONCOMP, CONV, DOTP, MXDOTP
  } opgroup_e;

  localparam int unsigned OP_BITS = 5;

  typedef enum logic [OP_BITS-1:0] {
    FMADD, FNMSUB, ADD, MUL, PWPA, PACE_INV, PACE_SQRT, PACE_RSQRT, // ADDMUL operation group
    DIV, SQRT,                   // DIVSQRT operation group
    SGNJ, MINMAX, CMP, CLASSIFY, // NONCOMP operation group
    F2F, F2I, I2F, CPKAB, CPKCD, // CONV operation group
    SDOTP, EXVSUM, VSUM,         // DOTP operation group
    MXDOTPF, MXDOTPI             // MXDOTP operation group
  } operation_e;

  // -------------
  // DIVSQRT UNIT
  // -------------
  typedef enum logic[1:0] {
    PULP,    // "PULP" instantiates the PULP DivSqrt unit supports FP64, FP32, FP16, FP16ALT, FP8 and SIMD operations
    TH32,    // "TH32" instantiates the E906 DivSqrt unit supports only FP32 (no SIMD support)
    THMULTI  // "THMULTI" instantiates the C910 DivSqrt unit supports FP64, FP32, FP16, FP16ALT and SIMD operations
  } divsqrt_unit_t;

  // -------------------
  // RISC-V FP-SPECIFIC
  // -------------------
  // Rounding modes
  typedef enum logic [2:0] {
    RNE = 3'b000,
    RTZ = 3'b001,
    RDN = 3'b010,
    RUP = 3'b011,
    RMM = 3'b100,
    ROD = 3'b101,  // This mode is not defined in RISC-V FP-SPEC
    RSR = 3'b110,  // This mode is not defined in RISC-V FP-SPEC
    DYN = 3'b111
  } roundmode_e;

  // Status flags
  typedef struct packed {
    logic NV; // Invalid
    logic DZ; // Divide by zero
    logic OF; // Overflow
    logic UF; // Underflow
    logic NX; // Inexact
  } status_t;

  // CSR encoded alternate fp formats
  typedef struct packed {
    logic src; // Source format selection
    logic dst; // Destination format selection
  } fmt_mode_t;

  // Information about a floating point value
  typedef struct packed {
    logic is_normal;     // is the value normal
    logic is_subnormal;  // is the value subnormal
    logic is_zero;       // is the value zero
    logic is_inf;        // is the value infinity
    logic is_nan;        // is the value NaN
    logic is_signalling; // is the value a signalling NaN
    logic is_quiet;      // is the value a quiet NaN
    logic is_boxed;      // is the value properly NaN-boxed (RISC-V specific)
  } fp_info_t;

  // Classification mask
  typedef enum logic [9:0] {
    NEGINF     = 10'b00_0000_0001,
    NEGNORM    = 10'b00_0000_0010,
    NEGSUBNORM = 10'b00_0000_0100,
    NEGZERO    = 10'b00_0000_1000,
    POSZERO    = 10'b00_0001_0000,
    POSSUBNORM = 10'b00_0010_0000,
    POSNORM    = 10'b00_0100_0000,
    POSINF     = 10'b00_1000_0000,
    SNAN       = 10'b01_0000_0000,
    QNAN       = 10'b10_0000_0000
  } classmask_e;

  // ------------------
  // FPU configuration
  // ------------------
  // Pipelining registers can be inserted (at elaboration time) into operational units
  typedef enum logic [1:0] {
    BEFORE,     // registers are inserted at the inputs of the unit
    AFTER,      // registers are inserted at the outputs of the unit
    INSIDE,     // registers are inserted at predetermined (suboptimal) locations in the unit
    DISTRIBUTED // registers are evenly distributed, INSIDE >= AFTER >= BEFORE
  } pipe_config_t;

  // Arithmetic units can be arranged in parallel (per format), merged (multi-format) or not at all.
  typedef enum logic [1:0] {
    DISABLED, // arithmetic units are not generated
    PARALLEL, // arithmetic units are generated in prallel slices, one for each format
    MERGED    // arithmetic units are contained within a merged unit holding multiple formats
  } unit_type_t;

  // Array of unit types indexed by format
  typedef unit_type_t [0:NUM_FP_FORMATS-1] fmt_unit_types_t;

  // Array of format-specific unit types by opgroup
  typedef fmt_unit_types_t [0:NUM_OPGROUPS-1] opgrp_fmt_unit_types_t;
  // same with unsigned
  typedef fmt_unsigned_t [0:NUM_OPGROUPS-1] opgrp_fmt_unsigned_t;

  localparam int unsigned MAX_PACE_PARTS = 64;
  localparam int unsigned MAX_PACE_DEGREE = 4;
  localparam int unsigned MAX_PACE_DEGREE_BITS   = $clog2(MAX_PACE_DEGREE+1);
  localparam int unsigned MAX_NUM_BST_STAGE = $clog2(MAX_PACE_PARTS);

  typedef logic [MAX_NUM_BST_STAGE-1:0] pace_pipe_t;
  typedef logic [MAX_PACE_DEGREE_BITS-1:0] pace_deg_t;

  typedef struct packed {
    int unsigned PaceDegree;      // polynomial degree for Horner evaluation
    int unsigned PaceParts;       // number of piecewise partitions
    logic        PaceEps;         // enable epsilon thresholding
    int unsigned PaceDataWidth;   // coefficient/bound data width in bits
    int unsigned PaceParamWidth;  // total parameter bus width in bits
    pace_pipe_t  PaceBstPipeRegs; // per-stage pipeline register bitmask for BST partition detector
    fmt_logic_t  FmtConfig;       // FP formats enabled for PACE
  } pace_features_t;

  typedef struct packed {
    logic extend;      // extend evaluation using partial result from previous iteration
    logic enable;      // enable PACE polynomial evaluation mode
    pace_deg_t degree; // polynomial degree
  } pace_mode_t;

  // Reference PACE configuration: degree-2 piecewise polynomial over 16 intervals on FP32/FP16/FP16ALT.
  // PaceParamWidth = ((PaceDegree+1)*PaceParts + (PaceParts-1) + 2*PaceEps) entries * PaceDataWidth bits.
  localparam pace_features_t DEFAULT_PACE_FEATURES = '{
    PaceDegree      : 2,
    PaceParts       : 16,
    PaceEps         : 1'b1,
    PaceDataWidth   : 32,
    PaceParamWidth  : 2080,
    PaceBstPipeRegs : 4'b0100, // register after BST stage 2 (3rd of 4 stages for 16 parts)
    FmtConfig       : 9'b101010000
  };

  // FPU configuration: features
  typedef struct packed {
    int unsigned    Width;
    logic           EnableVectors;
    logic           EnableNanBox;
    fmt_logic_t     FpFmtMask;    // Standard FP formats for all opgroups
    ifmt_logic_t    IntFmtMask;   // Standard INT formats for all opgroups
    fmt_logic_t     MxFpFmtMask;  // MX-specific FP formats (FP6, FP6ALT, FP4, plus FP8/FP8ALT)
    ifmt_logic_t    MxIntFmtMask; // MX-specific INT formats (INT8)
    pace_features_t PaceFeatures;
  } fpu_features_t;

  localparam fpu_features_t RV64D = '{
    Width:         64,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     9'b110000000,
    IntFmtMask:    4'b0011,
    MxFpFmtMask:   9'b0,         // No MX support
    MxIntFmtMask:  4'b0,
    PaceFeatures: '{default: 0}
  };

  localparam fpu_features_t RV32D = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     9'b110000000,
    IntFmtMask:    4'b0010,
    MxFpFmtMask:   9'b0,         // No MX support
    MxIntFmtMask:  4'b0,
    PaceFeatures: '{default: 0}
  };

  localparam fpu_features_t RV32F = '{
    Width:         32,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     9'b100000000,
    IntFmtMask:    4'b0010,
    MxFpFmtMask:   9'b0,         // No MX support
    MxIntFmtMask:  4'b0,
    PaceFeatures: '{default: 0}
  };

  localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     9'b111111000,  // Standard formats (not including FP6, FP6ALT, FP4)
    IntFmtMask:    4'b1111,
    MxFpFmtMask:   9'b000101111,  // MX formats: FP8, FP8ALT, FP6, FP6ALT, FP4
    MxIntFmtMask:  4'b1000,       // INT8 for MX operations
    PaceFeatures:  DEFAULT_PACE_FEATURES
  };

  localparam fpu_features_t RV32F_Xsflt = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     9'b101111000,
    IntFmtMask:    4'b1110,
    MxFpFmtMask:   9'b0,         // No MX support (32-bit width insufficient)
    MxIntFmtMask:  4'b0,
    PaceFeatures: '{default: 0}
  };

  localparam fpu_features_t RV32F_Xf16alt_Xfvec = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     9'b100010000,
    IntFmtMask:    4'b0110,
    MxFpFmtMask:   9'b0,         // No MX support
    MxIntFmtMask:  4'b0,
    PaceFeatures: '{default: 0}
  };


  // FPU configuraion: implementation
  typedef struct packed {
    opgrp_fmt_unsigned_t   PipeRegs;
    opgrp_fmt_unit_types_t UnitTypes;
    pipe_config_t          PipeConfig;
  } fpu_implementation_t;

  localparam fpu_implementation_t DEFAULT_NOREGS = '{
    PipeRegs:   '{default: 0},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: MERGED},   // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED},   // CONV
                  '{default: DISABLED},  // DOTP
                  '{default: DISABLED}}, // MXDOTP
    PipeConfig: BEFORE
  };

  localparam fpu_implementation_t DEFAULT_SNITCH = '{
    PipeRegs:   '{default: 1},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: DISABLED}, // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED},   // CONV
                  '{default: MERGED},   // DOTP
                  '{default: MERGED}},  // MXDOTP
    PipeConfig: BEFORE
  };

  localparam fpu_implementation_t DEFAULT_SNITCH_PIPE = '{
    PipeRegs:   '{'{default: 3},  // ADDMUL
                  '{default: 0},  // DIVSQRT
                  '{default: 0},  // NONCOMP
                  '{default: 2},  // CONV
                  '{default: 3},  // DOTP
                  '{default: 3}}, // MXDOTP
    UnitTypes:  '{'{default: MERGED},   // ADDMUL
                  '{default: MERGED},   // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED},   // CONV
                  '{default: MERGED},   // DOTP
                  '{default: MERGED}},  // MXDOTP
    PipeConfig: INSIDE
  };

  // Stochastic rounding only supported by DOTP operation group block
  typedef struct packed {
    logic        EnableRSR;             // Enable RSR adding an LFSR in the SDOTP rounding modules
    int unsigned RsrPrecision;          // Number of bits considered for the stochastic rounding decision
    int unsigned LfsrInternalPrecision; // LFSR internal bitwidth setting the pseudorandom number periodicity
  } rsr_impl_t;

  localparam rsr_impl_t DEFAULT_NO_RSR = '{
    EnableRSR:           1'b0,
    RsrPrecision:          12,
    LfsrInternalPrecision: 32
  };

  localparam rsr_impl_t DEFAULT_RSR = '{
    EnableRSR:           1'b1,
    RsrPrecision:          12,
    LfsrInternalPrecision: 32
  };

  // -----------------------
  // Synthesis optimization
  // -----------------------
  localparam logic DONT_CARE = 1'b1; // the value to assign as don't care

  // -------------------------
  // General helper functions
  // -------------------------
  function automatic int minimum(int a, int b);
    return (a < b) ? a : b;
  endfunction

  function automatic int maximum(int a, int b);
    return (a > b) ? a : b;
  endfunction

  // -------------------------------------------
  // Helper functions for FP formats and values
  // -------------------------------------------
  // Returns the width of a FP format
  function automatic int unsigned fp_width(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
  endfunction

  // Returns the widest FP format present
  function automatic int unsigned max_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(maximum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction


  function automatic int unsigned max_dotp_dst_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(maximum(res, fp_format_e'(i)));
    return res;
  endfunction

  // Returns the narrowest FP format present
  function automatic int unsigned min_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = max_fp_width(cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(minimum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction

  // Returns the number of expoent bits for a format
  function automatic int unsigned exp_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits;
  endfunction

  // Returns the number of mantissa bits for a format
  function automatic int unsigned man_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].man_bits;
  endfunction

  // Returns the bias value for a given format (as per IEEE 754-2008)
  function automatic int unsigned bias(fp_format_e fmt);
    return unsigned'(2**(FP_ENCODINGS[fmt].exp_bits-1)-1); // symmetrical bias
  endfunction

  function automatic fp_encoding_t super_format(fmt_logic_t cfg);
    automatic fp_encoding_t res;
    res = '0;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      if (cfg[fmt]) begin // only active format
        res.exp_bits = unsigned'(maximum(res.exp_bits, exp_bits(fp_format_e'(fmt))));
        res.man_bits = unsigned'(maximum(res.man_bits, man_bits(fp_format_e'(fmt))));
      end
    return res;
  endfunction

  // -------------------------------------------
  // Helper functions for INT formats and values
  // -------------------------------------------
  // Returns the widest INT format present
  function automatic int unsigned max_int_width(ifmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin
      if (cfg[ifmt]) res = maximum(res, int_width(int_format_e'(ifmt)));
    end
    return res;
  endfunction

  // --------------------------------------------------
  // Helper functions for operations and FPU structure
  // --------------------------------------------------
  // Returns the operation group of the given operation
  function automatic opgroup_e get_opgroup(operation_e op);
    unique case (op)
      FMADD, FNMSUB, ADD, MUL, PWPA, PACE_INV, PACE_SQRT, PACE_RSQRT: return ADDMUL;
      DIV, SQRT:                                                      return DIVSQRT;
      SGNJ, MINMAX, CMP, CLASSIFY:                                    return NONCOMP;
      F2F, F2I, I2F, CPKAB, CPKCD:                                    return CONV;
      SDOTP, EXVSUM, VSUM:                                            return DOTP;
      MXDOTPF, MXDOTPI:                                               return MXDOTP;
      default:                                                        return NONCOMP;
    endcase
  endfunction

  // Returns the number of operands by operation group
  function automatic int unsigned num_operands(opgroup_e grp);
    unique case (grp)
      ADDMUL:  return 3;
      DIVSQRT: return 2;
      NONCOMP: return 2;
      CONV:    return 3; // vectorial casts use 3 operands
      DOTP:    return 3; // splitting into 5 operands done in wrapper
      MXDOTP:  return 3; // splitting into 4 operands done in wrapper
      default: return 0;
    endcase
  endfunction

  // Returns the number of lanes according to width, format and vectors
  function automatic int unsigned num_lanes(int unsigned width, fp_format_e fmt, logic vec);
    return vec ? width / fp_width(fmt) : 1; // if no vectors, only one lane
  endfunction

  // Returns the maximum number of lanes in the FPU according to width, format config and vectors
  function automatic int unsigned max_num_lanes(int unsigned width, fmt_logic_t cfg, logic vec);
    return vec ? width / min_fp_width(cfg) : 1; // if no vectors, only one lane
  endfunction

    // Returns the maximum number of lanes in the FPU according to width, format config and vectors
  function automatic int unsigned num_divsqrt_lanes(int unsigned width, fmt_logic_t cfg, logic vec, divsqrt_unit_t DivSqrtSel);
    automatic fmt_logic_t cfg_tmp;
    cfg_tmp = (DivSqrtSel == THMULTI) ? cfg & 9'b111010000 : cfg;
    return vec ? width / min_fp_width(cfg_tmp) : 1; // if no vectors, only one lane
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a multiformat slice
  function automatic fmt_logic_t get_lane_formats(int unsigned width,
                                                  fmt_logic_t cfg,
                                                  int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format
      res[fmt] = cfg[fmt] & (width / fp_width(fp_format_e'(fmt)) > lane_no);
    return res;
  endfunction

  // Returns the intersection of FPU-enabled formats and PACE-enabled formats for a given lane
  function automatic fmt_logic_t get_pace_lane_formats( fmt_logic_t cfg_fpu, fmt_logic_t cfg_pace);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format
      res[fmt] = cfg_fpu[fmt] & cfg_pace[fmt];
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a multiformat slice
  function automatic ifmt_logic_t get_lane_int_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       ifmt_logic_t icfg,
                                                       int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        if ((fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt))))
          res[ifmt] |= icfg[ifmt] && lanefmts[fmt];
    return res;
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a CONV slice
  function automatic fmt_logic_t get_conv_lane_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format, CPK at least twice
      res[fmt] = cfg[fmt] && ((width / fp_width(fp_format_e'(fmt)) > lane_no) ||
                             (CPK_FORMATS[fmt] && (lane_no < 2)));
    return res;
  endfunction

  //Returns how many DOTP lanes should be generated
  function automatic int num_dotp_lanes(int unsigned width,
                                        fmt_logic_t cfg);
    return (cfg[FP16] || cfg[FP16ALT]) && (cfg[FP32] || cfg[FP8] || cfg[FP8ALT]) ?
               (width / (2*min_fp_width(cfg))) : 0;
  endfunction

  // Returns a mask of active FP formats that are currenlty supported for DOTP operations
  function automatic fmt_logic_t get_dotp_lane_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       int unsigned lane_no);
    automatic fmt_logic_t res;
    automatic fmt_logic_t mask;
    int unsigned nr_16to32bit_lanes = (cfg[FP32]) ? (width / 32) : 0;
    if (lane_no < nr_16to32bit_lanes)
      mask = 9'b101111000;  //lane should be 16-bit -> 32-bit
    else
      mask = 9'b001111000;  //lane should be  8-bit -> 16-bit
    res = cfg & mask;
    return res;
  endfunction

  // Returns how many MXDOTP lanes should be generated
  function automatic int num_mxdotp_lanes(int unsigned width,
                                          fmt_logic_t mx_fp_cfg,
                                          ifmt_logic_t mx_int_cfg);
    // MXDOTP is single-lane, non-vectorial
    // Check if any MX source format is enabled (FP8, FP8ALT, FP6, FP6ALT, FP4) or INT8
    return (width == 64 && (|(mx_fp_cfg & MXDOTP_FORMATS_MASK.src_fp_formats) ||
                            |(mx_int_cfg & MXDOTP_FORMATS_MASK.src_int_formats))) ? 1 : 0;
  endfunction

  // Returns all format masks for MXDOTP operations
  // Note: Assumes width == 64 (validated at instantiation)
  function automatic lane_formats_t get_mxdotp_formats(int unsigned width,
                                                       fmt_logic_t fp_cfg,
                                                       fmt_logic_t mx_fp_cfg,
                                                       ifmt_logic_t mx_int_cfg,
                                                       int unsigned lane_no);
    automatic lane_formats_t res;

    // Source FP formats from MX config: FP8, FP8ALT, FP6, FP6ALT, FP4
    res.src_fp_formats = mx_fp_cfg & MXDOTP_FORMATS_MASK.src_fp_formats;

    // Source INT formats from MX config: INT8 only
    res.src_int_formats = mx_int_cfg & MXDOTP_FORMATS_MASK.src_int_formats;

    // Destination formats from standard FP config: FP32 and FP16ALT
    res.dst_fp_formats = fp_cfg & MXDOTP_FORMATS_MASK.dst_fp_formats;
    return res;
  endfunction

  // Returns the dotp dest FP format string
  function automatic fmt_logic_t get_dotp_dst_fmts(fmt_logic_t cfg, fmt_logic_t src_cfg);
    automatic fmt_logic_t res;
    res = { cfg[FP32] && (src_cfg[FP16] || src_cfg[FP16ALT] || src_cfg[FP8] || src_cfg[FP8ALT]),
            1'b0,                                               // FP64 not supported as dstFmt
            cfg[FP16] && (src_cfg[FP8] || src_cfg[FP8ALT]),
            cfg[FP8],                                           // FP8 supported as dstFmt for VSUM
            cfg[FP16ALT] && (src_cfg[FP8] || src_cfg[FP8ALT]),
            cfg[FP8ALT],                                        // FP8ALT supported as dstFmt for VSUM
            1'b0,                                               // FP6 not supported as dstFmt
            1'b0,                                               // FP6ALT not supported as dstFmt
            1'b0                                                // FP4 not supported as dstFmt
    };
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a CONV slice
  function automatic ifmt_logic_t get_conv_lane_int_formats(int unsigned width,
                                                            fmt_logic_t cfg,
                                                            ifmt_logic_t icfg,
                                                            int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_conv_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        res[ifmt] |= icfg[ifmt] && lanefmts[fmt] &&
                     (fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt)));
    return res;
  endfunction

  // Return whether any active format is set as MERGED
  function automatic logic any_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return 1'b1;
      return 1'b0;
  endfunction

  // Return whether the given format is the first active one set as MERGED
  function automatic logic is_first_enabled_multi(fp_format_e fmt,
                                                  fmt_unit_types_t types,
                                                  fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) return (fp_format_e'(i) == fmt);
    end
    return 1'b0;
  endfunction

  // Returns the first format that is active and is set as MERGED
  function automatic fp_format_e get_first_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return fp_format_e'(i);
      return fp_format_e'(0);
  endfunction

  // Returns the largest number of regs that is active and is set as MERGED
  function automatic int unsigned get_num_regs_multi(fmt_unsigned_t regs,
                                                     fmt_unit_types_t types,
                                                     fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) res = maximum(res, regs[i]);
    end
    return res;
  endfunction

endpackage
