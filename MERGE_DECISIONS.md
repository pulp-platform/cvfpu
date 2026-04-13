# Merge decisions: `pulp` ← `openhwgroup/develop`

Merge target: bring upstream openhwgroup updates into the pulp branch.

**Guiding principle (user-stated): pulp features are layered on top of the
verified openhw implementation.** Whenever a conflict pits "openhw's new
implementation" against "pulp's older implementation of the same thing",
prefer the openhw version; whenever pulp added an orthogonal feature, keep
it as an addition.

## Trivial resolutions

| File | Decision | Rationale |
|---|---|---|
| `docs/CODEOWNERS` | Keep pulp version (upstream deleted) | pulp fork has its own maintainer |
| `vendor/openc910/.../gated_clk_cell.v` | Take upstream | Trailing newline only |
| `vendor/openc910/.../ct_vfdsu_pack.v` | Take upstream | Contains upstream PR #150 subnormal/normal underflow fix |
| `README.md` | Keep pulp maintainer info | pulp fork |
| `docs/README.md` | Merge both | keep pulp's Stochastic Rounding section and DOTP/MXDOTP opgroup rows, keep upstream's `ADDS` in ADDMUL row |

## `src/fpnew_pkg.sv`

- **`operation_e`**: pulp ops kept at existing encodings (`SDOTP, EXVSUM, VSUM, MXDOTPF, MXDOTPI` after `CPKCD`); upstream's `ADDS` appended **after** `MXDOTPI`.
  Rationale: pulp's op encoding is already deployed; upstream's encoding stability
  concern was internal to upstream. Added a comment noting this.
- **`get_opgroup()`**: merged both tables. `FMADD, FNMSUB, ADD, ADDS, MUL → ADDMUL`, and DOTP/MXDOTP rows retained.
- **`num_divsqrt_lanes()`**: kept pulp's 9-bit mask `9'b111010000`. Upstream's `5'b11101` is stale relative to pulp's extended format list.

## `src/fpnew_top.sv`

- Kept pulp's inline `Features.X` / `Implementation.X[opgrp]` parameter passing to `fpnew_opgroup_block`. This carries the pulp-only params
  (`MxFpFmtMask`, `MxIntFmtMask`, `CompressedVecCmpResult`, `StochasticRndImplementation`)
  without needing to declare new localparams for each.
- Upstream's `early_valid_o` output port, `opgrp_early_valid` signal, and `assign early_valid_o = |opgrp_early_valid;` merged automatically — kept.
- Upstream's localparam refactor (`localparam OpGroup = ...; localparam FpFmtMask = ...;`) was dropped; functionally equivalent to pulp's style.

## `src/fpnew_opgroup_block.sv`

- Two conflicts, both in child-module instantiations (`fpnew_opgroup_fmt_slice` and `fpnew_opgroup_multifmt_slice`).
- Kept pulp's parameter set (adds `CompressedVecCmpResult`, `MxFpFmtMask`, `MxIntFmtMask`, `StochasticRndImplementation`). These are a pulp superset; upstream didn't add any parameters here.
- `early_valid_o` port merged automatically outside the conflict.

## `src/fpnew_opgroup_fmt_slice.sv`

- **`lane_aux[AUX_BITS-1:0]`**: kept pulp's wider aux bus. It carries `{vectorial_op, cmp_op}` for `CompressedVecCmpResult`. Upstream's narrower `lane_vectorial` would drop this.
- **`lane_early_out_valid` signal**: added (from upstream).
- **`fpnew_fma` instance**: kept pulp's `rnd_mode`/`local_aux_data_input`/`lane_aux[lane]` bindings; added upstream's `.reg_ena_i` and `.early_out_valid_o( lane_early_out_valid[lane] )`.
- **`fpnew_noncomp` instance**: same treatment.

## `src/fpnew_divsqrt_multi.sv`

- Took upstream's `div_valid`/`sqrt_valid`/`op_starting` formulation (with `ext_op_start_q` gating) and the `unit_done_clear = simd_synch_done | reg_ena_i[NUM_INP_REGS-1]` FF handling.
- Rationale: upstream PR #102 was originally a pulp contribution that evolved further; upstream's is the more mature form.
- Removed a duplicated block below the conflict that HEAD carried.

## `src/fpnew_divsqrt_th_64_multi.sv`

- **Took upstream's file wholesale** (`git checkout --theirs`).
- Reasoning: pulp's only unique addition was a local NaN-boxing `always_comb` block (~50 lines) plus a `srcf0/srcf1` signal pair routed into the T-Head unit. Upstream PR #160 explicitly **removed** this exact block as a fix (NaN-boxing is now done by the caller). Layering pulp's removed code back on top of upstream's fix would re-introduce the bug.
- Net effect: gain `reg_ena_i`, `early_out_valid_o`, FP16ALT support, verilator `split_var` pragma, NaN-boxing fix; lose nothing pulp-unique.

## `src/fpnew_opgroup_multifmt_slice.sv`

11 conflict blocks resolved as follows:

1. **Module parameter list**: kept all pulp params (`MxFpFmtConfig`, `MxIntFmtConfig`, `StochasticRndImplementation`) **and** added upstream's new `ExtRegEna`. Result is a strict superset.
2. **`OpGroup == DIVSQRT` config check**: kept pulp's THMULTI warning that mentions both FP8 and FP8alt (vs upstream's FP8-only warning) — pulp has FP8alt as a format, so the broader warning is correct.
3. **Pulp-only DOTP and MXDOTP config asserts**: preserved (upstream had no equivalent).
4. **`NUM_DOTP_LANES` / `NUM_MX_LANES` localparams**: preserved (pulp-only).
5. **Active-lane `if` gating**: kept pulp's superset (gates DIVSQRT, DOTP, MXDOTP).
6. **`local_operands` in `prepare_input`**: **took upstream's** `i==2 ? (op_i==ADDS ? src_fmt_i : dst_fmt_i)` formulation. This is required for the new `ADDS` op semantics. The pulp DOTP-specific overwrite block right below this remains untouched and continues to override the operand[2] indexing for DOTP.
7. **DivSqrt unit instantiations (TH32, THMULTI, PULP)**:
   - Kept pulp's `.rnd_mode_i ( rnd_mode )` connection (sanitized rnd_mode that maps `RSR → RNE`); upstream's `.rnd_mode_i,` (passing the unsanitized `rnd_mode_i`) would forward `RSR` to a unit that doesn't support it.
   - Added upstream's `.reg_ena_i` and `.early_out_valid_o( lane_early_out_valid[lane] )` port bindings to all three divsqrt units.
8. **`local_result` / `lane_status` assigns**: combined — kept pulp's `{(LANE_WIDTH){lane_ext_bit[0]}}` width-explicit form (upstream used array-pattern `'{default: ...}`), and added upstream's `| ExtRegEna` gating.
9. **`no_conv` else-branch**: kept pulp's explicit `assign fmt_conv_cpk_result = '0;` (it's a pulp-only signal); kept pulp's `assign result_vec_op = '0;` instead of upstream's combined `{result_vec_op, result_is_cpk} = '0;`.
10. **SIMD synch generate condition**: combined — `(DivSqrtSel != TH32) && (OpGroup == DIVSQRT) && !ExtRegEna`. Pulp's opgroup gate is necessary because pulp generates this slice for non-DIVSQRT opgroups too; upstream's `!ExtRegEna` gate disables synch when external reg enable is in use.

## Things to verify before merging upstream

(High-confidence items I'd still want a pulp HW engineer to eyeball.)

- `fpnew_opgroup_multifmt_slice.sv` line ~262 (`local_operands` assignment): the merged version now uses `dst_fmt_i` for operand 2 (default case). Pulp previously used `src_fmt_i` for all operands here. **Behavioral change** — should be confirmed harmless against pulp's MXDOTP/SDOTP paths (those have their own override blocks below).
- `fpnew_top.sv`: I kept pulp's inline `Features.X` parameter style instead of upstream's localparam refactor. Functionally equivalent but stylistically diverges from upstream — could be cleaned up later.
- `fpnew_pkg.sv` `operation_e`: appended `ADDS` after pulp's `MXDOTPI` (encoding 20). Upstream's `ADDS` was at encoding 15. If anything outside the FPU hard-codes `ADDS=15`, that needs adjustment. Pulp's existing op codes (`SDOTP=15`, etc.) preserved as the priority.
- THMULTI wrapper: pulp's prior local NaN-boxing logic is gone. Caller (this file) must NaN-box operands before passing them in. Confirm pulp's instantiation site does this — upstream's PR #160 commit message implies the caller does. Worth grepping for `srcf0_q`/`srcf1_q` consumers in the openC910 unit to be sure.

## Files that auto-merged (no manual decisions, listed for completeness)

`Bender.yml`, `docs/CHANGELOG.md`, `src/fpnew_cast_multi.sv`, `src/fpnew_divsqrt_th_32.sv`, `src/fpnew_fma.sv`, `src/fpnew_fma_multi.sv`, `src/fpnew_noncomp.sv`, `vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_pack_single.v`, plus three `vendor/patches/...` files added by upstream.
