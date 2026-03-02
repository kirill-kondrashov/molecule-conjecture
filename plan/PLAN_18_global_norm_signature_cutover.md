# PLAN 18 - Global Norm Signature Cutover

Status: DONE
Progress: [##########] 100%
Scope: Replace global `h_norm` parameters in conjecture-level theorem signatures with localized normalization contracts and compatibility bridges.
Acceptance: One full conjecture-layer theorem chain compiles without requiring the global `h_norm` type in its public signature.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/HyperbolicityTheorems.lean`
Stuck Rule: STUCK if cutover cannot be staged incrementally with a compiling intermediate bridge.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Identify minimal signature chain for first cutover slice.
- [x] Implement bridge theorem from old signature to localized signature.
- [x] Switch one caller chain to localized signature.
- [x] Route Problem4_3 conjecture theorem through localized fixed-point-data bridge.
- [x] Route conjecture-level hyperbolicity through localized spectral-data contract.
- [x] Remove unused legacy `h_norm`-era fields from packed top-level route.

## Current Outcome

- Added `molecule_conjecture_refined_with_localized_slice_data` in `Molecule/Conjecture.lean`.
- This removes explicit `h_exists` from that theorem's signature via localized slice-data contract.
- Top-level theorem route has now switched to the cutover theorem.
- Added localized Problem4_3 cutover entry in `Molecule/Conjecture.lean`:
  - `problem_4_3_bounds_established_conjecture_localized`
- Added localized hyperbolicity cutover entry in `Molecule/Conjecture.lean`:
  - `Rfast_hyperbolicity_conjecture_localized`
- `molecule_conjecture_refined_with_localized_slice_data` now takes:
  - `FixedPointNormalizationData`
  - localized spectral-data contract
  instead of the explicit global `h_norm` argument.
- `MoleculeHypothesisPack` was minimized to fields used by the localized route.
