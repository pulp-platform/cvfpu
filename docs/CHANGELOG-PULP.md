# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/) and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

In this sense, we interpret the "Public API" of a hardware module as its port/parameter list.
Versions of the IP in the same major relase are "pin-compatible" with each other. Minor relases are permitted to add new parameters as long as their default bindings ensure backwards compatibility.

## [Unreleased]

### Added
- Add MX conversion operations to the `CONV` opgroup: `M2F`/`F2M` (MX FP <-> FP with a shared E8M0 scale), `MI2F`/`F2MI` (MX INT8 <-> FP), `MXSCALE`/`MXISCALE` (E8M0 scale computation) and `FNF` (FP -> FP conversion between formats whose widths are not a power-of-two multiple apart)
- Add slot insert mechanism to `fpnew_opgroup_multifmt_slice`: the converted group of a `CONV` insert operation is written into a slot of the target operand (`operands_i[1]`), the slot being selected by `operands_i[2][11:8]`
- Add `EnableSlotSelect` and `EnableMXConv` fields to `fpu_features_t` to enable the slot insert mechanism and the MX conversion datapath
- `MINMAX` with `op_mod_i` set compares and returns the magnitudes of `op[0]` and `op[1]` (absolute minimum / maximum); `op_mod_i` was previously ignored by `MINMAX`

### Changed
- **Breaking**: `fpu_features_t` gains the `EnableSlotSelect` and `EnableMXConv` fields; existing feature literals must add both (set them to `1'b0` to keep the previous behaviour)
- `fpnew_cast_multi` takes three operands (`operands_i[0]` source, `[1]` insert target, `[2]` MX scale) and gains the `MxFpFmtConfig`, `MxIntFmtConfig` and `EnableMXScale` parameters
- `fpnew_classifier` replaces the `MX` parameter with a runtime `src_is_mx` input; FP6, FP6ALT and FP4 are always classified as finite-only (they have no Inf/NaN encodings)
- `FNF` between two MX-only formats (FP6, FP6ALT, FP4 on both sides) requires both formats in `FpFmtMask`; every other MX conversion only needs them in `MxFpFmtMask` (the `CONV` opgroup block routes the MX element formats to its merged slice). The predefined `RV64D_Xsflt` keeps them out of `FpFmtMask`, so `NumLanes` and `simd_mask_i` are unchanged
- `DEFAULT_SNITCH_PIPE` is now specified per format: FP6, FP6ALT and FP4 are enabled for `CONV` only and `DISABLED` elsewhere, `ADDMUL` is `MERGED` for FP32/FP64/FP16/FP16ALT only (no FP8/FP8ALT FMA), `DIVSQRT` is `MERGED` for FP32/FP16/FP16ALT only, and the pipeline depths are ADDMUL 2 (FP32/FP64) / 1 (FP16/FP16ALT), DIVSQRT 1, NONCOMP 0, CONV 2, DOTP 3, MXDOTP 3
- Merged opgroup slices only build lanes for formats whose unit type is `MERGED` for that opgroup

### Fixed
- Fix upper-half operand selection of vectorial F2F up-casts in `fpnew_opgroup_multifmt_slice` (`MAX_FP_WIDTH/2` -> `Width/2`)

## [pulp-v0.3.0] - 2026-07-20

### Added
- Add FP6(E3M2), FP6ALT(E2M3), and FP4(E2M1) floating-point formats
- Add MXDOTP Microscaling dot product multi-format operation group
  - Supports source formats: FP8, FP8ALT, FP6, FP6ALT, FP4, INT8
  - Supports destination formats: FP32, FP16ALT
  - Scaled dot-product and accumulation support with two 8-bit exponent scale factors
- Add PACE (Polynomial Approximation Compute Engine) support in the `ADDMUL` group
  - Evaluates transcendental functions (reciprocal, square root, reciprocal square root) via piecewise polynomial approximation using Horner's method on the FMA unit
  - Requires `ADDMUL` to use the `MERGED` unit type
  - Configurable degree, number of intervals, and target FP formats via `pace_features_t` in `fpu_features_t`
  - Runtime control through new top-level ports `pace_param_i` (packed coefficient/bound bus) and `pace_mode_i`
  - `DEFAULT_PACE_FEATURES` provided as a reference configuration (degree-2, 16 intervals, FP32/FP16/FP16ALT)

### Changed
- Extend classifier to support MX-specific special cases for FP6, FP6ALT, FP4 formats
- Increase number of supported FP formats from 6 to 9
- Increase number of opgroups from 5 to 6
- `fpu_features_t` extended with `MxFpFmtMask`, `MxIntFmtMask`, and `PaceFeatures` fields
- **Breaking**: `fpnew_top` gains two mandatory input ports, `pace_param_i` and `pace_mode_i`; existing integrations must connect them. Tie both to `'0` when PACE is unused (a zeroed `pace_mode_t` clears the `enable` bit).

### Notes
- MXDOTP implementation tested with all element formats enabled, but not yet exhaustively tested with all possible combinations of enabled formats.
- Known limitations documented in TODO comments (see source files for details)

## [pulp-v0.2.3] - 2024-09-27

### Fix
- Fix illegal Verilog `'0`

## [pulp-v0.2.2] - 2024-06-24

### Added
- Add FP16ALT support to THMULTI DivSqrt

## [pulp-v0.2.1] - 2024-06-07

### Fix
- Fix synchronization of THMULTI DivSqrt lanes when FP16ALT, FP8, or FP8ALT are enabled.

## [pulp-v0.2.0] - 2024-05-29

### Added
- Add support for alternative multi-format DivSqrt unit (from openC910), supporting FP64, FP32, FP16 and SIMD operations
- Replace `PulpDivsqrt` top-level parameter with `DivSqrtSel` to choose among the legacy PULP DivSqrt unit (`PULP`), the openE906 DivSqrt (`TH32`), and the openC910 DivSqrt (`THMULTI`). The default choice is set to `THMULTI`

## [pulp-v0.1.3] - 2023-07-19

### Fixed
- Fix `lane_valid` generation for SIMD CAST involving the largest precision available
- Tie some potentially unused (depending on the FPU configuration) bits in `opgroup_multifmt_slice` to zero

## [pulp-v0.1.2] - 2023-06-12

### Fixed
- Fix synchronization scheme for SIMD DivSqrt

## [pulp-v0.1.1] - 2023-05-05

### Fixed
- Fix various tool compatibility issues

## [pulp-v0.1.0] - 2023-05-04

### Added
- Add low and mixed-precision SDOTP with support for stochastic rounding
- Add `FP8alt (1,4,3)` format
- Add support for compressed vector compare results (one bit per comparison in the LSBs)
