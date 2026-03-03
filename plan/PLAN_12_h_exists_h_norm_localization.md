# PLAN 12 - h_exists/h_norm Localization

Status: DONE
Progress: [##########] 100%
Scope: Replace broad global normalization dependencies with local invariant-set normalization in theorem interfaces.
Acceptance: First theorem family consumes localized normalization package instead of global `h_norm` where possible.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`
Stuck Rule: STUCK if localization cannot be threaded without full cross-module signature rewrite in one step.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Add local invariant slice-data bundle and migration theorem.
- [x] Rewire first conjecture-level theorem to consume localized contract.

## Current Outcome

- Added in `Molecule/Conjecture.lean`:
  - `HasInvariantSliceData`
  - `has_invariant_slice_data_of_exists`
  - `has_invariant_slice_data_with_normalization_of_global`
  - `InvariantSliceDataWithNormalization`
  - `problem_4_3_fixed_point_data_of_global`
  - `problem_4_3_bounds_established_conjecture_localized`
