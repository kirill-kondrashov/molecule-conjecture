# PLAN 46 - Seed-Free Ingredient Constructor

Status: ACTIVE
Progress: [#########-] 93%
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
- [x] Add non-`h_norm` Subtarget A bridges from assumption-level contracts:
  - `residual_fixed_point_existence_of_canonical_fast_fixed_point_data`
  - `residual_fixed_point_existence_of_refined_contract`
- [x] Add generic Subtarget B bridge skeleton:
  - `fixed_point_local_normalization_transfer_of_fixed_data_and_unique`
  - `residual_fixed_point_normalization_ingredients_of_fixed_data_and_unique`
  (still requires proving/feeding uniqueness and fixed-data sources seed-free).
- [x] Build an assumption-level Subtarget A route not using `molecule_h_norm`:
  - `residual_fixed_point_normalization_ingredients_of_canonical_and_transfer`
  - `residual_fixed_point_normalization_ingredients_of_refined_and_transfer`
- [x] Build an assumption-level Subtarget B route not using `molecule_h_norm`:
  - `fixed_point_local_normalization_transfer_of_fixed_data_and_unique`
  - `residual_fixed_point_normalization_ingredients_of_refined_fixed_data_and_unique`
- [x] Rewire zero-arg ingredient source assembly through the fixed-data/uniqueness
  bridge (non-circular architecture step):
  - `molecule_h_fixed_data_direct`
  - `molecule_residual_fixed_point_existence_source := ...of_fixed_point_normalization_data`
  - `molecule_residual_fixed_point_transfer_source := ...of_fixed_data_and_unique`
  - `molecule_residual_fixed_point_normalization_ingredients := ...of_fixed_data_and_unique`
- [x] Isolate residual orbit-transport dependency behind an explicit replacement seam:
  - `MoleculeResidualOrbitTransportSource`
  - `molecule_residual_orbit_transport_source`
  - `molecule_residual_bounds_from_fixed_data := ... molecule_residual_orbit_transport_source`
- [x] Split residual orbit-transport seam into explicit sub-sources:
  - `MoleculeResidualPseudoSiegelSource`
  - `MoleculeResidualOrbitClauseSource`
  - `molecule_residual_orbit_transport_source_of_sources`
  to isolate the remaining non-ground dependency to orbit-clause source.
- [x] Split fixed-point ingredient seam further with explicit uniqueness source:
  - `MoleculeResidualFixedPointUniquenessSource`
  - `molecule_residual_fixed_point_transfer_source_of_fixed_data_and_unique`
  - `molecule_residual_fixed_point_normalization_ingredients_of_sources`
- [x] Add explicit fixed-point-data source seam:
  - `MoleculeResidualFixedPointDataSource`
  - `molecule_residual_fixed_point_data_source`
  and route residual existence/transfer sources through it.
- [ ] Replace the body of `molecule_residual_fixed_point_normalization_ingredients` with the seed-free constructor.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms`:
  - `Molecule.molecule_residual_fixed_point_normalization_ingredients`
  - `Molecule.molecule_residual_bounds_seed_free`
  - `Molecule.molecule_conjecture_refined`

## Notes

- This plan intentionally targets the ingredient theorem first; downstream theorems are already routed through this seam.
- `molecule_h_norm` currently enters residual bounds through two explicit source
  seams: fixed-point ingredients and orbit-transport source.
