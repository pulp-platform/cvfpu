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

package pace_package;

  // Basic data type parameters

  function automatic integer unsigned msb(input integer unsigned width);
    return (width != 32'd0) ? unsigned'(width - 1) : 32'd0;
  endfunction

  // Bit widths for basic data types
  localparam DataByteBits  = 8;
  localparam DataHalfBits  = 16;  // “Half” is clearer than “Short”
  localparam DataWordBits  = 32;  // “Word” retained as preferred

  // Scaling factors relative to word size (32-bit)
  localparam DataScaleFromByte = DataWordBits / DataByteBits;  // 4
  localparam DataScaleFromHalf = DataWordBits / DataHalfBits;  // 2
  localparam DataScaleFromWord = DataWordBits / DataWordBits;  // 1
  
  // Polynomial configuration
  `ifdef OVERRIDE_PARAM_DEGREE
    localparam PolyDegree        = `OVERRIDE_PARAM_DEGREE;
  `else 
    localparam PolyDegree        = 2;
  `endif
  localparam PolyNumCoeffs       = PolyDegree + 1;

  `ifdef OVERRIDE_PARAM_PARTITION
    localparam PolyPartitions    = `OVERRIDE_PARAM_PARTITION;
  `else
    localparam PolyPartitions    = 16;
  `endif
  localparam PolyBreakpoints     = PolyPartitions + 1;

  // Coefficient memory configuration
  localparam CoeffMemWrWidth     = DataWordBits;
  localparam CoeffMemWrPorts     = 1;
  localparam CoeffMemRdWidth     = DataByteBits;
  localparam CoeffMemRdPorts     = DataScaleFromByte;
  localparam CoeffMemWrLength    = PolyPartitions;
  localparam CoeffMemRdLength    = DataScaleFromByte * PolyPartitions;
  localparam CoeffMemNumBanks    = PolyNumCoeffs;

  localparam CoeffMemBankWrAddrBits = $clog2(PolyPartitions);
  localparam CoeffMemBankRdAddrBits = $clog2(CoeffMemRdLength);

  localparam CoeffMemWrAddrBits     = $clog2(PolyDegree) + $clog2(PolyPartitions);
  localparam CoeffMemRdAddrBits     = $clog2(PolyDegree) + $clog2(CoeffMemRdLength);

  // Breakpoint memory configuration
  localparam BpMemWrWidth        = DataWordBits;
  localparam BpMemWrPorts        = 1;
  localparam BpMemRdWidth        = DataWordBits;
  localparam BpMemRdPorts        = 1 + PolyPartitions;
  localparam BpMemWrLength       = 1 + PolyPartitions;
  localparam BpMemRdLength       = DataScaleFromWord * PolyBreakpoints;
  localparam BpMemNumBanks       = 1;

  localparam BpMemBankWrAddrBits = $clog2(1) + $clog2(PolyBreakpoints);
  localparam BpMemWrAddrBits     = $clog2(1) + $clog2(PolyBreakpoints);

  localparam BpMemBankRdAddrBits = $clog2(1) + $clog2(DataScaleFromWord * PolyBreakpoints);
  localparam BpMemRdAddrBits     = $clog2(1) + $clog2(DataScaleFromWord * PolyBreakpoints);

  // Floating-point 32-bit (fp32) partition parameters
  localparam PartitionFP32ManBits   = 23;
  localparam PartitionFP32ExpBits   = 8;
  localparam PartitionFP32Scale     = DataScaleFromWord;
  localparam PartitionFP32Parts     = PolyPartitions;                  // 4
  localparam PartitionFP32PartBits  = $clog2(PartitionFP32Parts);      // 2
  localparam PartitionFP32Bps       = PolyBreakpoints;                 // 5
  localparam PartitionFP32BpsBits   = $clog2(PartitionFP32Bps);        // 3
  localparam PartitionFP32OpBits    = 23 + 8 + 1;

  // Floating-point 16-bit (fp16)
  localparam PartitionFP16ManBits   = 10;
  localparam PartitionFP16ExpBits   = 5;
  localparam PartitionFP16Scale     = DataScaleFromHalf;
  localparam PartitionFP16Parts     = DataScaleFromWord * PolyPartitions;       // 8
  localparam PartitionFP16PartBits  = $clog2(PartitionFP16Parts);               // 3
  localparam PartitionFP16Bps       = 1 + PartitionFP16Parts;                   // 9
  localparam PartitionFP16BpsBits   = $clog2(PartitionFP16Bps);                 // 4
  localparam PartitionFP16OpBits    = 10 + 5 + 1;

  // Brain-floating-point 16-bit (bfp16)
  localparam PartitionBFP16ManBits  = 7;
  localparam PartitionBFP16ExpBits  = 8;
  localparam PartitionBFP16Scale    = DataScaleFromHalf;
  localparam PartitionBFP16Parts    = DataScaleFromWord * PolyPartitions;
  localparam PartitionBFP16PartBits = $clog2(PartitionBFP16Parts);
  localparam PartitionBFP16Bps      = 1 + PartitionBFP16Parts;
  localparam PartitionBFP16BpsBits  = $clog2(PartitionBFP16Bps);
  localparam PartitionBFP16OpBits   = 7 + 8 + 1;

  // Floating-point 8-bit (fp8)
  localparam PartitionFP8ManBits    = 3;
  localparam PartitionFP8ExpBits    = 4;
  localparam PartitionFP8Scale      = DataScaleFromByte;
  localparam PartitionFP8Parts      = DataScaleFromWord * PolyPartitions;      // 16
  localparam PartitionFP8PartBits   = $clog2(PartitionFP8Parts);               // 4
  localparam PartitionFP8Bps        = 1 + PartitionFP8Parts;                   // 17
  localparam PartitionFP8BpsBits    = $clog2(PartitionFP8Bps);                 // 5
  localparam PartitionFP8OpBits     = 3 + 4 + 1;

  typedef struct packed {
    int unsigned ManBits;    // Mantissa bit width
    int unsigned ExpBits;    // Exponent bit width
    int unsigned OpBits;     // Operand total width
    int unsigned Parts;      // Number of partitions
    int unsigned PartBits;   // Partition address bits
    int unsigned Bps;        // Number of bps
    int unsigned BpsBits;    // Breakpoint address bits
    int unsigned Scale;      // Scaling factor (relative to base word size)
  } PartitionFpCfg_t;

  typedef struct packed {
    int unsigned ManBits;
    int unsigned ExpBits;
    int unsigned OpBits;
    int unsigned Parts;
    int unsigned PartBits;
    int unsigned Bps;
    int unsigned BpsBits;
    int unsigned Scale;
  } param_partition_fp_t;



  `define DEFINE_PARAM_PARTITION(name) \
    localparam param_partition_fp_t ParamPartition``name = '{ \
      ManBits  : Partition``name``ManBits, \
      ExpBits  : Partition``name``ExpBits, \
      Scale    : Partition``name``Scale, \
      Parts    : Partition``name``Parts, \
      PartBits : Partition``name``PartBits, \
      Bps      : Partition``name``Bps, \
      BpsBits  : Partition``name``BpsBits, \
      OpBits   : Partition``name``OpBits \
    };
  `DEFINE_PARAM_PARTITION(FP32)
  `DEFINE_PARAM_PARTITION(FP16)
  `DEFINE_PARAM_PARTITION(BFP16)
  `DEFINE_PARAM_PARTITION(FP8)

  typedef struct packed {
    int unsigned WdataWidth;
    int unsigned NumWdataPort;
    int unsigned RdataWidth;
    int unsigned NumRdataPort;
    int unsigned WriteLength;
    int unsigned ReadLength;
    int unsigned NumBanks;
    int unsigned BankWaddrWidth;
    int unsigned WaddrWidth;
    int unsigned RaddrWidth;
    int unsigned BankRaddrWidth;
  } param_memory_t;


  `define DEFINE_PARAM_MEMORY(name, prefix) \
    localparam param_memory_t name = '{ \
      WdataWidth     : ``prefix``WrWidth, \
      NumWdataPort   : ``prefix``WrPorts, \
      RdataWidth     : ``prefix``RdWidth, \
      NumRdataPort   : ``prefix``RdPorts, \
      WriteLength    : ``prefix``WrLength, \
      ReadLength     : ``prefix``RdLength, \
      NumBanks       : ``prefix``NumBanks, \
      BankWaddrWidth : ``prefix``BankWrAddrBits, \
      WaddrWidth     : ``prefix``WrAddrBits, \
      RaddrWidth     : ``prefix``RdAddrBits, \
      BankRaddrWidth : ``prefix``BankRdAddrBits \
    };
  `DEFINE_PARAM_MEMORY(BpMem, BpMem)
  `DEFINE_PARAM_MEMORY(CoeffMem, CoeffMem)


  // Define typedefs for widths based on data bit-widths
  typedef logic [msb(DataWordBits):0]              data_word_t;
  typedef logic [msb(DataWordBits):0]              fp32_data_t;
  typedef logic [msb(DataHalfBits):0]              fp16_data_t;
  typedef logic [msb(DataHalfBits):0]              bfp16_data_t;
  typedef logic [msb(DataByteBits):0]              fp8_data_t;

  // Coefficient memory address/data control types
  typedef logic [msb(CoeffMemNumBanks):0][msb(CoeffMemBankRdAddrBits*CoeffMemRdPorts):0]  coeff_rd_addr_t;
  typedef logic [msb(CoeffMemNumBanks):0][msb(CoeffMemRdPorts):0]                         coeff_bypass_mask_t;
  typedef logic [msb(CoeffMemBankWrAddrBits*CoeffMemWrPorts):0]                           coeff_wr_addr_t;
  typedef logic [(CoeffMemBankWrAddrBits*CoeffMemWrPorts):0]                              coeff_wr_addr_comb_t;
  typedef logic [msb(CoeffMemNumBanks):0][msb(CoeffMemRdPorts):0]                         coeff_rd_enable_t;
  typedef logic [msb(CoeffMemNumBanks):0]                                                 coeff_wr_enable_t;
  typedef logic [(CoeffMemNumBanks):0]                                                    coeff_wr_enable_comb_t;
  typedef logic [msb(DataWordBits):0]                                                     coeff_wr_data_t;
  typedef logic [msb(CoeffMemNumBanks):0][msb(CoeffMemRdPorts*DataByteBits):0]            coeff_rd_data_t;

  typedef logic [msb(CoeffMemBankRdAddrBits*CoeffMemRdPorts):0]                           coeff_rd_addr_bank_t;
  typedef logic [msb((CoeffMemBankRdAddrBits+1)*CoeffMemRdPorts):0]                       coeff_bypass_addr_bank_t;
  typedef logic [msb(CoeffMemNumBanks):0][msb((CoeffMemBankRdAddrBits+1)*CoeffMemRdPorts):0] coeff_bypass_addr_t;

  // Breakpoint memory types
  typedef logic [msb(BpMemRdAddrBits*BpMemRdPorts):0]       bp_rd_addr_t;
  typedef logic [msb(BpMemBankWrAddrBits*BpMemWrPorts):0]   bp_wr_addr_t;
  typedef logic [msb(BpMemWrLength):0][msb(BpMemRdWidth):0] bp_rd_data_t;
  typedef logic [msb(BpMemRdPorts):0]                       bp_rd_enable_t;
  typedef logic [msb(BpMemWrPorts):0]                       bp_wr_enable_t;


  typedef struct packed {
    logic [msb(DataScaleFromWord):0][msb(DataWordBits):0]                 data_in;
    logic [msb(DataScaleFromWord):0][msb(PartitionFP32PartBits):0]        part_id;
    logic [msb(PartitionFP32Bps * PartitionFP32OpBits):0]                 bps;
    coeff_rd_addr_bank_t                                                  coeff_raddr;
    coeff_bypass_addr_bank_t                                              coeff_raddr_bypass;
    logic [msb(DataScaleFromWord):0][msb(PartitionFP32Bps):0]             enable;
    logic [msb(DataScaleFromWord):0]                                      valid;
    logic [msb(DataScaleFromWord):0]                                      ready;
    logic [msb(DataScaleFromWord):0]                                      bypass;
    logic [msb(CoeffMemRdPorts):0][msb(DataScaleFromByte):0]              out_bypass;
  } fp32_partition_vector_t;


  typedef struct packed {
    logic [msb(DataScaleFromHalf):0][msb(DataHalfBits):0]                 data_in;
    logic [msb(DataScaleFromHalf):0][msb(PartitionFP16PartBits):0]        part_id;
    logic [msb(PartitionFP16Bps * PartitionFP16OpBits):0]                 bps;
    coeff_rd_addr_bank_t                                                  coeff_raddr;
    coeff_bypass_addr_bank_t                                              coeff_raddr_bypass;
    logic [msb(DataScaleFromHalf):0][msb(PartitionFP16Bps):0]             enable;
    logic [msb(DataScaleFromHalf):0]                                      valid;
    logic [msb(DataScaleFromHalf):0]                                      ready;
    logic [msb(DataScaleFromHalf):0]                                      bypass;
    logic [msb(CoeffMemRdPorts):0][msb(DataScaleFromByte):0]              out_bypass;
  } fp16_partition_vector_t;


  typedef struct packed {
    logic [msb(DataScaleFromByte):0][msb(DataByteBits):0]                 data_in;
    logic [msb(DataScaleFromByte):0][msb(PartitionFP8PartBits):0]         part_id;
    logic [msb(PartitionFP8Bps * PartitionFP8OpBits):0]                   bps;
    coeff_rd_addr_bank_t                                                  coeff_raddr;
    coeff_bypass_addr_bank_t                                              coeff_raddr_bypass;
    logic [msb(DataScaleFromByte):0][msb(PartitionFP8Bps):0]              enable;
    logic [msb(DataScaleFromByte):0]                                      valid;
    logic [msb(DataScaleFromByte):0]                                      ready;
    logic [msb(DataScaleFromByte):0]                                      bypass;
    logic [msb(CoeffMemRdPorts):0][msb(DataScaleFromByte):0]              out_bypass;
  } fp8_partition_vector_t;


  typedef logic [msb(PolyNumCoeffs):0][msb(DataWordBits):0] fp32_coeff_t;
  typedef logic [msb(PolyNumCoeffs):0][msb(DataHalfBits):0] fp16_coeff_t;
  typedef logic [msb(PolyNumCoeffs):0][msb(DataByteBits):0] fp8_coeff_t;

  typedef struct packed {
    logic [msb(DataWordBits):0]                             data;
    logic [msb(DataWordBits):0]                             pres;
    logic [msb(DataWordBits):0]                             result;
    logic [msb(PolyNumCoeffs * DataWordBits):0]             coeff_flat;
    logic [msb(PolyDegree):0][msb(DataWordBits):0]          coeff_vec;
    logic                                                   bypass;
  } fp32_fma_vector_t;


  typedef struct packed {
    logic [msb(DataHalfBits):0]                             data;
    logic [msb(DataHalfBits):0]                             pres;
    logic [msb(DataHalfBits):0]                             result;
    logic [msb(PolyNumCoeffs * DataHalfBits):0]             coeff_flat;
    logic                                                   bypass;
  } fp16_fma_vector_t;


  typedef struct packed {
    logic [msb(DataByteBits):0]                             data;
    logic [msb(DataByteBits):0]                             pres;
    logic [msb(DataByteBits):0]                             result;
    logic [msb(PolyNumCoeffs * DataByteBits):0]             coeff_flat;
    logic                                                   bypass;
  } fp8_fma_vector_t;


  typedef enum logic [1:0] {
    FP8   = 2'd0,
    FP16  = 2'd1,
    BFP16 = 2'd2,
    FP32  = 2'd3
  } pace_fp_mode_t;

  localparam FmaPipelineStages = 1;

  // Basic memory control struct
  typedef struct packed {
    logic start;
  } ctrl_mem_t;

  // Engine control flags
  typedef struct packed {
    logic            part_exceed;
    logic            degree_exceed;
    pace_fp_mode_t   fp_mode;
  } ctrl_engine_t;

  // Coefficient memory controller
  typedef struct packed {
    ctrl_mem_t                      write;
    logic                           clear;
    logic [msb(CoeffMemNumBanks):0] renable;
    coeff_wr_enable_t               max_wenable;
    coeff_wr_addr_comb_t            max_length;
    pace_fp_mode_t                  fp_mode;
    logic                           read_done;
  } ctrl_coeff_mem_t;

  // Breakpoint memory controller
  typedef struct packed {
    ctrl_mem_t      write;
    logic           clear;
    bp_rd_enable_t  max_length;
  } ctrl_bp_mem_t;

  // Flag registers
  typedef struct packed {
    logic init_done;
  } flags_bp_mem_t;

  typedef struct packed {
    logic write_done;
  } flags_coeff_mem_t;

  // Partition controller
  typedef struct packed {
    ctrl_bp_mem_t                   bp_mem;
    pace_fp_mode_t                  fp_mode;
    logic [msb(PartitionFP32Bps):0] part_enable_fp32;
    logic [msb(PartitionFP16Bps):0] part_enable_fp16;
    logic [msb(PartitionFP8Bps):0]  part_enable_fp8;
    logic                           part_exceed;
  } ctrl_partition_t;

  // Partition flags
  typedef struct packed {
    flags_bp_mem_t bp_mem;
  } flags_partition_t;

  typedef enum logic [1:0] {
    MemIdle,
    MemInitialize,
    MemRead
  } state_mem_t;

  typedef struct packed {
    ctrl_partition_t     partition;
    ctrl_bp_mem_t        bp_mem;
    ctrl_coeff_mem_t     coeff_mem;
    ctrl_engine_t        engine;
  } ctrl_pace_t;

  typedef struct packed {
    flags_partition_t     partition;
    flags_bp_mem_t        bp_mem;
    flags_coeff_mem_t     coeff_mem;
  } flags_pace_t;


  // Format configuration per FP mode (fp32, fp16, bfp16, fp8)
  localparam logic [3:0][5:0] VectorFmtConfig = '{
    6'b101110,  // fp32
    6'b001110,  // fp16
    6'b000100,  // bfp16
    6'b000100   // fp8
  };

  // Vector width in bits per FP mode (as integers, not 6-bit logic!)
  localparam int VectorFmtWidth [3:0] = '{
    32,  // fp32
    16,  // fp16
    8,  // bfp16
    8   // fp8
  };

  // Limits for degree and partitions
  parameter int MaxSupportedDegree     = 8;
  parameter int MaxSupportedPartitions = 64;

  // Widths for encoding degree and partition index
  localparam int PACEDegreeWidth    = $clog2(MaxSupportedDegree);
  localparam int PACEPartitionWidth = $clog2(MaxSupportedPartitions);

  // Polynomial configuration structure
  typedef struct packed {
    logic                          start;
    logic                          part_exceed;
    logic                          degree_exceed;
    pace_package::pace_fp_mode_t   fp_mode;
    logic [PACEDegreeWidth-1:0]    degree;
    logic [PACEPartitionWidth-1:0] partition;
  } pace_cfg_t;

endpackage
