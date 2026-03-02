# PLAN 17 - Signature Migration to Local Norm Contracts

Status: ACTIVE
Progress: [########--] 80%
Scope: Migrate theorem interfaces from global `h_norm` assumptions to localized normalization packages.
Acceptance: At least one conjecture-layer theorem path compiles with localized norm contract in signature.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`
Stuck Rule: STUCK if migration requires atomic rewrite of all dependent modules without intermediate compilable bridge.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Add an explicit `InvariantSliceDataWithNormalization` contract in code.
- [x] Add first theorem with localized signature and compatibility bridge.
- [x] Extend migration into the Problem4_3 fixed-point-data theorem path.
- [x] Extend migration into conjecture-level localized hyperbolicity signatures.
- [x] Remove unused legacy fields from packed localized theorem route.

## Current Outcome

- Added in `Molecule/Conjecture.lean`:
  - `InvariantSliceDataWithNormalization`
  - `invariant_slice_data_with_normalization_of_global`
  - `problem_4_3_bounds_established_conjecture_localized`
- Added localized signature chain entries:
  - `Rfast_hyperbolicity_conjecture_localized`
  - `molecule_h_fixed_data`
  - `molecule_h_spectral_data`
- Updated `MoleculeHypothesisPack` to keep only fields used by localized route.
