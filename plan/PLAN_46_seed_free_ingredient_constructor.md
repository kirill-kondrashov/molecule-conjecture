# PLAN 46 - Seed-Free Ingredient Constructor

Status: ACTIVE
Progress: [###-------] 30%
Scope: Replace the body of `molecule_residual_fixed_point_normalization_ingredients` with a seed-free theorem-level construction, so the fixed-data source no longer depends on `molecule_h_norm`.
Acceptance: `#print axioms Molecule.molecule_residual_fixed_point_normalization_ingredients` does not include `Molecule.molecule_h_norm`, and this removal propagates to `molecule_residual_bounds_seed_free` and `molecule_conjecture_refined`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/HyperbolicityTheorems.lean`, `plan/PLAN_45_local_fixed_point_normalization_source.md`
Stuck Rule: STUCK if both ingredient subtargets below require reintroducing a project axiom or force weakening exported theorem signatures.
Last Updated: 2026-03-03

## Goal Decomposition

- Ingredient target:
  - `MoleculeResidualFixedPointNormalizationIngredients`
- Subtarget A:
  - `∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f`
- Subtarget B:
  - `FixedPointLocalNormalizationTransfer`

## Work Plan

- [x] Isolate the replacement point to one theorem:
  - `molecule_residual_fixed_point_normalization_ingredients`
- [x] Split ingredient source into two explicit theorem targets:
  - `molecule_residual_fixed_point_existence_source` (Subtarget A seam)
  - `molecule_residual_fixed_point_transfer_source` (Subtarget B seam)
- [ ] Build a seed-free proof route for Subtarget A from existing theorem infrastructure (not via `molecule_h_norm`).
- [ ] Build a seed-free proof route for Subtarget B from existing theorem infrastructure (not via `molecule_h_norm`).
- [ ] Replace the body of `molecule_residual_fixed_point_normalization_ingredients` with the seed-free constructor.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms`:
  - `Molecule.molecule_residual_fixed_point_normalization_ingredients`
  - `Molecule.molecule_residual_bounds_seed_free`
  - `Molecule.molecule_conjecture_refined`

## Notes

- This plan intentionally targets the ingredient theorem first; downstream theorems are already routed through this seam.
