# PLAN 53 - Fixed-Point Model Bottleneck Refactor

Status: ACTIVE
Progress: [#####-----] 50%
Scope: Resolve the model-level bottleneck exposed by `no_fixed_point_implies_renormalizable` so the fixed-point ingredient route can be rebuilt without `molecule_h_norm` and without relying on the false bridge contract.
Acceptance:
1. The fixed-point ingredient route no longer depends on `FixedPointImpliesRenormalizable`.
2. A non-circular theorem-level source provides
   `MoleculeResidualFixedPointExistenceSource` (or stronger ingredient data)
   without `molecule_h_norm`.
3. `molecule_residual_fixed_point_normalization_ingredients` can be rebuilt from
   the new source path.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FixedPointExistence.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationTheorem.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
Stuck Rule: STUCK if every non-circular witness candidate still forces the default fixed-point trap (`defaultBMol` fixed but non-renormalizable) without a model-level refactor path.
Last Updated: 2026-03-04

## Work Plan

- [x] Record feasibility gate theorem:
  - `no_fixed_point_implies_renormalizable`.
- [x] Identify minimal theorem/interface changes needed so fixed-point existence
  witness is not forced through the default fixed-point trap.
- [x] Introduce a replacement source seam for renormalizable fixed-point
  existence that does not require the false global bridge contract.
- [x] Route `molecule_residual_fixed_point_normalization_ingredients` through
  the replacement seam.
- [x] Re-run `make build`, `make check`, and targeted `#print axioms` probes.
- [ ] Replace `molecule_residual_fixed_point_data_source` with a non-circular
  non-`molecule_h_norm` theorem-level source.
- [ ] Re-run fixed-point and top-level axiom probes after replacing
  `molecule_residual_fixed_point_data_source`.

## Notes

- This plan supersedes PLAN_52, which is stuck because
  `FixedPointImpliesRenormalizable` is false in the current model.
- Implemented bridge-free ingredient routing in `Molecule/Conjecture.lean`:
  - `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`
  - `molecule_residual_fixed_point_normalization_ingredients` now routes through
    fixed-data + transfer, not through `FixedPointImpliesRenormalizable`.
- Probe checkpoint:
  - `#print axioms Molecule.molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`
    is ground-axiom-only.
