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

// Author: Arpan Suravi Prasad <prasadar@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

// Wrapper around the FMA engine that also handles PACE polynomial evaluation.
module fpnew_pace_fma_multi #(
  parameter fpnew_pkg::fmt_logic_t      FpFmtConfig   = '1,
  parameter int unsigned                NumPipeRegs   = 0,
  parameter fpnew_pkg::pipe_config_t    PipeConfig    = fpnew_pkg::BEFORE,
  parameter fpnew_pkg::pace_features_t  PaceFeat      = '{default: 0},
  parameter fpnew_pkg::fmt_logic_t      PaceFmtCfg    = PaceFeat.FmtConfig,
  parameter int unsigned                PaceDataW     = 0,
  parameter int unsigned                PaceManOff    = 0,
  parameter type                        TagType       = logic,
  parameter type                        AuxType       = logic,
  localparam int unsigned               Parts         = PaceFeat.PaceParts,
  localparam int unsigned               Degrees       = PaceFeat.PaceDegree,
  localparam int unsigned               Eps           = PaceFeat.PaceEps,
  localparam int unsigned               Bounds        = Parts - 1,
  localparam int unsigned               BoundStages   = $clog2(Bounds),
  localparam fpnew_pkg::pace_pipe_t     BstPipeRegs   = PaceFeat.PaceBstPipeRegs,
  localparam int unsigned               CoeffDegreeBits = $clog2(Degrees + 1),
  localparam int unsigned               DegreesBits   = fpnew_pkg::MAX_PACE_DEGREE_BITS,
  localparam int unsigned               ParamWidth    = PaceFeat.PaceParamWidth,
  localparam int unsigned               ParamMsb      = (ParamWidth > 0) ? (ParamWidth - 1) : 0,
  localparam int unsigned               FmaScoreboardDepth =
      NumPipeRegs > 0 ? NumPipeRegs : 1,
  // Do not change
  localparam int unsigned               Width         = fpnew_pkg::max_fp_width(FpFmtConfig),
  localparam int unsigned               NumFormats    = fpnew_pkg::NUM_FP_FORMATS,
  localparam fpnew_pkg::fp_encoding_t   SuperFormat   = fpnew_pkg::super_format(FpFmtConfig),
  localparam int unsigned               SuperExpBits  = SuperFormat.exp_bits,
  localparam int unsigned               SuperManBits  = SuperFormat.man_bits,
  localparam int unsigned               SuperWidth    =
      1 + SuperFormat.man_bits + SuperFormat.exp_bits
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Input signals
  input  logic [2:0][Width-1:0]       operands_i,
  input  logic [NumFormats-1:0][2:0]  is_boxed_i,
  input  fpnew_pkg::roundmode_e       rnd_mode_i,
  input  fpnew_pkg::operation_e       op_i,
  input  logic                        op_mod_i,
  input  fpnew_pkg::fp_format_e       src_fmt_i,
  input  fpnew_pkg::fp_format_e       dst_fmt_i,
  input  logic [ParamMsb:0]           pace_param_i,
  input  fpnew_pkg::pace_mode_t       pace_mode_i,
  input  TagType                      tag_i,
  input  logic                        mask_i,
  input  AuxType                      aux_i,
  // Input Handshake
  input  logic                        in_valid_i,
  output logic                        in_ready_o,
  input  logic                        flush_i,
  // Output signals
  output logic [Width-1:0]            result_o,
  output fpnew_pkg::status_t          status_o,
  output logic                        extension_bit_o,
  output TagType                      tag_o,
  output logic                        mask_o,
  output AuxType                      aux_o,
  // Output handshake
  output logic                        out_valid_o,
  input  logic                        out_ready_i,
  // Indication of valid data in flight
  output logic                        busy_o
);

  localparam int unsigned NumCoeffs = (Degrees + 1) * Parts;
  localparam fpnew_pkg::fp_encoding_t PaceFmt = fpnew_pkg::super_format(PaceFmtCfg);
  localparam int unsigned PaceW = fpnew_pkg::max_fp_width(PaceFmtCfg);
  localparam int unsigned PaceFmtW = 1 + PaceFmt.man_bits + PaceFmt.exp_bits;
  localparam int unsigned PaceExpBits = PaceFmt.exp_bits;
  localparam int unsigned PaceManBits = PaceFmt.man_bits;
  // Limit the local datapath width if FPNew supports formats wider than PACE needs.
  localparam int unsigned LocalW = (Width > PaceDataW) ? PaceDataW : Width;

  // The Horner loopback feeds the FMA result back into the FMA input. At least one
  // pipeline register inside the FMA is required to break this otherwise-combinational loop.
  if (NumPipeRegs == 0) begin : gen_check_pace_pipe
    $fatal(1, "fpnew_pace_fma_multi: PACE requires at least one ADDMUL pipeline register (NumPipeRegs >= 1) to break the Horner feedback loop.");
  end

  logic [LocalW-1:0] red_in;

  typedef struct packed {
    logic sign;
    logic lt_eps;
    logic [PaceExpBits-1:0] exponent;
    logic sqrt;
    logic inv;
    logic rsqrt;
  } inv_tag_t;

  typedef struct packed {
    TagType user_tag;
    inv_tag_t inv_tag;
    logic mask;
    AuxType aux;
    fpnew_pkg::fp_format_e src_fmt;
  } part_tag_t;

  typedef struct packed {
    TagType user_tag;
    inv_tag_t inv_tag;
    logic [DegreesBits-1:0] degree;
    logic [BoundStages-1:0] part_id;
    logic active;
  } fma_tag_t;

  // ----------------
  // Datapath Signals
  // ----------------
  logic [2:0][Width-1:0] fma_ops_in;
  logic [2:0][Width-1:0] horn_ops;

  logic [Width-1:0] fma_bypass_op;
  logic [LocalW-1:0] part_in_op;
  logic [LocalW-1:0] part_op;
  logic [LocalW-1:0] fr_in_op;
  logic [1:0][LocalW-1:0] coeff_pair;
  logic [NumFormats-1:0][2:0] fma_is_boxed;
  fpnew_pkg::roundmode_e fma_round_mode;
  fpnew_pkg::operation_e fma_op;
  logic fma_op_mod;
  fpnew_pkg::fp_format_e fma_src_fmt;
  fpnew_pkg::fp_format_e fma_dst_fmt;
  fpnew_pkg::fp_format_e pace_fmt;
  fpnew_pkg::fp_format_e part_fmt;
  fma_tag_t in_tag;
  logic fma_in_mask;
  AuxType fma_in_aux;
  // Input Handshake
  logic fma_in_valid;
  logic fma_in_ready;
  logic fma_flush;
  // Output signals
  logic [Width-1:0] fma_res;
  fpnew_pkg::status_t fma_status_flags;
  logic fma_extension_bit;
  fma_tag_t out_tag;
  logic fma_output_mask;
  AuxType fma_output_aux;
  // Output handshake
  logic fma_vld;
  logic fma_rdy;
  // Indication of valid data in flight
  logic fma_busy;
  logic part_busy;
  logic part_inflight;
  logic [BoundStages-1:0] part_idx;

  logic [PaceW-1:0] scaled_result;
  logic [PaceW-1:0] ld_in_op;

  // Polynomial coefficients are packed in Horner order:
  // coeff_table[0] is the leading term and coeff_table[Degrees] is the constant term.
  // The remaining PACE parameters are optional inverse/sqrt metadata.
  logic [Degrees:0][Bounds:0][LocalW-1:0] coeff_table;
  logic [Bounds-1:0][PaceFmtW-1:0]        partition_bounds;
  logic [PaceFmtW-1:0]                    eps_th;
  logic [PaceW-1:0]                       eps_out;

  // ----------------
  // Control Signals
  // ----------------
  part_tag_t ptag_in, ptag_out;
  logic horn_fb;
  logic horn_act;
  logic pace_op;
  logic pwpa_op;
  logic inv_op;
  logic sqrt_op;
  logic rsqrt_op;
  logic do_inv;
  logic [FmaScoreboardDepth-1:0] inflight_q;
  logic [FmaScoreboardDepth-1:0] inflight_d;
  logic pin_vld, pin_rdy;
  logic pout_vld, pout_rdy;
  inv_tag_t inv_info;
  inv_tag_t out_inv;

  for (genvar deg = 0; deg <= Degrees; deg++) begin : gen_coeffs
    for (genvar part = 0; part < Parts; part++) begin : gen_coeff
      localparam int unsigned ParamIdx = deg * Parts + part;
      localparam int unsigned ParamOff = ParamIdx * PaceDataW;
      assign coeff_table[deg][part] = pace_param_i[ParamOff +: LocalW];
    end
  end

  if (Parts > 1) begin : gen_partition_bounds
    for (genvar partition = 0; partition < Bounds; partition++) begin : gen_bound_entry
      localparam int unsigned BoundIdx = NumCoeffs + partition;
      localparam int unsigned BoundOff = BoundIdx * PaceDataW;
      assign partition_bounds[partition] = {
        pace_param_i[BoundOff + PaceDataW - 1],
        pace_param_i[BoundOff + PaceManOff +: PaceExpBits],
        pace_param_i[BoundOff +: PaceManBits]
      };
    end
  end

  if (Eps == 1) begin : gen_eps_params
    localparam int unsigned EpsIdx    = NumCoeffs + Bounds;
    localparam int unsigned EpsOff    = EpsIdx * PaceDataW;
    localparam int unsigned EpsOutIdx = NumCoeffs + Bounds + 1;
    localparam int unsigned EpsOutOff = EpsOutIdx * PaceDataW;
    assign eps_th = {
      pace_param_i[EpsOff + PaceDataW - 1],
      pace_param_i[EpsOff + PaceManOff +: PaceExpBits],
      pace_param_i[EpsOff +: PaceManBits]
    };
    assign eps_out = pace_param_i[EpsOutOff +: LocalW];
  end else begin : gen_no_eps_params
    assign eps_th = '0;
    assign eps_out    = '0;
  end

  // Partition-stage tag payload.
  assign ptag_in.user_tag    = tag_i;
  assign ptag_in.inv_tag     = inv_info;
  assign ptag_in.mask        = mask_i;
  assign ptag_in.aux         = aux_i;
  assign ptag_in.src_fmt     = src_fmt_i;

  assign pwpa_op = (op_i == fpnew_pkg::PWPA);
  assign inv_op = (op_i == fpnew_pkg::PACE_INV);
  assign sqrt_op = (op_i == fpnew_pkg::PACE_SQRT);
  assign rsqrt_op = (op_i == fpnew_pkg::PACE_RSQRT);
  assign pace_op = pwpa_op | rsqrt_op | inv_op | sqrt_op;
  assign do_inv = inv_op | sqrt_op | rsqrt_op;
  assign horn_act = horn_fb ? 1'b1 : pout_vld;

  assign fma_flush       = flush_i;
  assign status_o        = fma_status_flags;
  assign extension_bit_o = fma_extension_bit;
  assign tag_o           = out_tag.user_tag;
  assign mask_o          = fma_output_mask;
  assign aux_o           = fma_output_aux;
  assign busy_o          = fma_busy | horn_fb | part_busy;
  assign out_inv = out_tag.inv_tag;

  always_comb begin
    inflight_d = inflight_q;

    if (fma_vld & fma_rdy & out_tag.active) begin
      if (FmaScoreboardDepth == 1) begin
        inflight_d = '0;
      end else begin
        inflight_d = {1'b0, inflight_d[FmaScoreboardDepth-1:1]};
      end
    end

    if (pout_vld & pout_rdy) begin
      inflight_d[0] = 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      inflight_q <= '0;
    end else begin
      inflight_q <= inflight_d;
    end
  end

  always_comb begin
    in_tag = '0;
    in_tag.user_tag = tag_i;
    in_tag.degree = 1;
    in_tag.part_id = part_idx;
    in_tag.active = horn_act;

    if (horn_act) begin
      in_tag.user_tag = ptag_out.user_tag;
      in_tag.inv_tag = ptag_out.inv_tag;
      in_tag.part_id = part_idx;
    end

    if (horn_fb) begin
      in_tag.user_tag = out_tag.user_tag;
      in_tag.inv_tag = out_tag.inv_tag;
      in_tag.degree = out_tag.degree + 1;
      in_tag.part_id = out_tag.part_id;
    end
  end

  always_comb begin
    fma_round_mode = rnd_mode_i;
    fma_op         = op_i;
    fma_op_mod     = op_mod_i;
    fma_ops_in     = operands_i;
    fma_src_fmt    = src_fmt_i;
    fma_dst_fmt    = dst_fmt_i;
    fma_in_mask    = mask_i;
    fma_in_aux     = aux_i;
    fma_is_boxed   = is_boxed_i;
    fma_in_valid   = pace_op ? 1'b0 : in_valid_i;
    fma_rdy        = out_ready_i;
    in_ready_o     = fma_in_ready;
    out_valid_o    = fma_vld;
    pin_vld        = 1'b0;
    pout_rdy       = 1'b0;

    if (pace_op) begin
      in_ready_o = pin_rdy;
      pin_vld = in_valid_i;
    end

    if (horn_act) begin
      fma_round_mode = fpnew_pkg::RNE;
      fma_op = fpnew_pkg::FMADD;
      fma_op_mod = 1'b0;
      fma_ops_in = horn_ops;
      fma_src_fmt = part_fmt;
      fma_dst_fmt = part_fmt;
      fma_in_mask = ptag_out.mask;
      fma_in_aux = ptag_out.aux;
      fma_is_boxed = '1;
      fma_in_valid = pout_vld;
      pout_rdy = fma_in_ready;
    end

    if (horn_fb) begin
      fma_ops_in = horn_ops;
      fma_src_fmt = pace_fmt;
      fma_dst_fmt = pace_fmt;
      fma_in_mask = fma_output_mask;
      fma_in_aux = fma_output_aux;
      fma_in_valid = fma_vld;
      fma_rdy = 1'b1;
      in_ready_o = 1'b0;
      out_valid_o = 1'b0;
      pin_vld = 1'b0;
      pout_rdy = 1'b0;
    end

    if (!pace_op && (part_inflight | (|inflight_q) | horn_fb)) begin
      in_ready_o = 1'b0;
    end
  end

  assign result_o = out_tag.active
                  ? {{(Width - PaceW){fma_res[Width-1]}}, scaled_result}
                  : fma_res;

  // Horner evaluation uses a*b + c with the selected coefficient pair.
  always_comb begin
    horn_ops = '0;
    horn_ops[2][LocalW-1:0] = coeff_pair[1];
    horn_ops[1][LocalW-1:0] = horn_fb ? fma_bypass_op[LocalW-1:0] : part_op;
    horn_ops[0][LocalW-1:0] = horn_fb ? fma_res[LocalW-1:0] : coeff_pair[0];
  end

  assign horn_fb =
      fma_vld & out_tag.active & (out_tag.degree < pace_mode_i.degree);

`ifndef VERILATOR
  pace_degree_in_range: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
      (in_valid_i && pace_op) |-> (pace_mode_i.degree <= fpnew_pkg::pace_deg_t'(Degrees))
  ) else $fatal(1,
      "fpnew_pace_fma_multi: pace_mode_i.degree exceeds configured PaceFeat.PaceDegree.");
`endif

  // Decompose and rescale data for inverse/sqrt-style PACE modes.
  assign fr_in_op = operands_i[0][LocalW-1:0];
  assign ld_in_op = fma_res[PaceW-1:0];

  fpnew_pace_frexp #(
    .FpFmtConfig(PaceFmtCfg),
    .FrexpInfoType(inv_tag_t)
  ) i_pace_frexp (
    .clk_i,
    .rst_ni,
    .src_fmt_i(src_fmt_i),
    .op_i(op_i),
    .eps_i(eps_th),
    .operand_i(fr_in_op),
    .operand_o(red_in),
    .frexp_info_o(inv_info)
  );

  fpnew_pace_ldexp #(
    .FpFmtConfig(PaceFmtCfg)
  ) i_pace_ldexp (
    .op_inv_i(out_inv.inv),
    .op_sqrt_i(out_inv.sqrt),
    .op_rsqrt_i(out_inv.rsqrt),
    .pace_op_i(out_tag.active),
    .src_fmt_i(pace_fmt),
    .eps_val_i(eps_out),
    .operand_i(ld_in_op),
    .sign_i(out_inv.sign),
    .lt_eps_i(out_inv.lt_eps),
    .exponent_i(out_inv.exponent),
    .operand_o(scaled_result)
  );

  assign part_in_op = do_inv ? red_in : operands_i[0][LocalW-1:0];

  if (Parts > 1) begin : gen_part_detect
    fpnew_pace_partition #(
      .FpFmtConfig(PaceFmtCfg),
      .PipeConfig (PipeConfig),
      .Bounds(Bounds),
      .PipeRegs(BstPipeRegs),
      .NumCmpStages(BoundStages),
      .TagType(part_tag_t)
    ) i_partition_detector (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .flush_i(flush_i),
      .bounds_i(partition_bounds),
      .operand_i(part_in_op),
      .operand_o(part_op),
      .src_fmt_i(src_fmt_i),
      .dst_fmt_o(part_fmt),
      .tag_i(ptag_in),
      .in_valid_i(pin_vld),
      .in_ready_o(pin_rdy),
      .bound_id_o(part_idx),
      .tag_o(ptag_out),
      .out_valid_o(pout_vld),
      .out_ready_i(pout_rdy),
      .inflight_o(part_inflight),
      .busy_o(part_busy)
    );
  end else begin : gen_no_part_detect
    assign part_idx = '0;
    assign pout_vld = pin_vld;
    assign pin_rdy  = pout_rdy;
    assign ptag_out = ptag_in;
    assign part_inflight = 1'b0;
    assign part_op = part_in_op;
    assign part_fmt = src_fmt_i;
    assign part_busy = 1'b0;
  end

  fpnew_pace_coeff_select #(
    .Bounds      ( Bounds + 1     ),
    .Degrees     ( Degrees        ),
    .Width       ( LocalW         ),
    .BoundStages ( BoundStages    )
  ) i_coeff_selector (
    .coeffs_i ( coeff_table ),
    .bound_i  ( in_tag.part_id ),
    .degree_i ( in_tag.degree[CoeffDegreeBits-1:0] ),
    .coeffs_o ( coeff_pair )
  );

  fpnew_fma_multi #(
    .FpFmtConfig (FpFmtConfig),
    .NumPipeRegs (NumPipeRegs),
    .PipeConfig  (PipeConfig),
    .TagType     (fma_tag_t),
    .AuxType     (AuxType)
  ) i_fma_multi (
    .clk_i,
    .rst_ni,
    // Input signals
    .operands_i       ( fma_ops_in ),
    .is_boxed_i       ( fma_is_boxed ),
    .rnd_mode_i       ( fma_round_mode ),
    .op_i             ( fma_op ),
    .op_mod_i         ( fma_op_mod ),
    .src_fmt_i        ( fma_src_fmt ),
    .dst_fmt_i        ( fma_dst_fmt ),
    .tag_i            ( in_tag ),
    .mask_i           ( fma_in_mask ),
    .aux_i            ( fma_in_aux ),
    // Input Handshake
    .in_valid_i       ( fma_in_valid ),
    .in_ready_o       ( fma_in_ready ),
    .flush_i          ( fma_flush ),
    // Output signals
    .result_o         ( fma_res ),
    .status_o         ( fma_status_flags ),
    .extension_bit_o  ( fma_extension_bit ),
    .tag_o            ( out_tag ),
    .mask_o           ( fma_output_mask ),
    .aux_o            ( fma_output_aux ),
    // PACE bypass outputs
    .pace_operand_o   ( fma_bypass_op ),
    .pace_fmt_o       ( pace_fmt ),
    // Output handshake
    .out_valid_o      ( fma_vld ),
    .out_ready_i      ( fma_rdy ),
    // Indication of valid data in flight
    .busy_o           ( fma_busy )
  );

endmodule
