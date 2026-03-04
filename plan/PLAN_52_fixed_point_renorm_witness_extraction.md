# PLAN 52 - Fixed-Point Renormalizability Witness Extraction

Status: ACTIVE
Progress: [#######---] 70%
Scope: Provide a non-circular theorem-level route to produce a renormalizable fixed-point witness for `Rfast` that can feed `MoleculeResidualFixedPointNormalizationIngredients` without using `molecule_h_norm`.
Acceptance:
1. A theorem in `Molecule/Conjecture.lean` (or upstream module) yields
   `∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f` from non-axiomatic
   contracts already on the active path.
2. The theorem is not derived from `molecule_residual_bounds`/`molecule_residual_non_ground_sources` (no circularity).
3. The resulting witness is usable to rebuild
   `molecule_residual_fixed_point_normalization_ingredients` without
   `molecule_h_norm` on the fixed-point side.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FixedPointExistence.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationTheorem.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`
Stuck Rule: STUCK if every available witness candidate either requires `molecule_h_norm` or depends on bounds/non-ground outputs that already consume the target ingredient theorem.
Last Updated: 2026-03-04

## Work Plan

- [x] Isolate the exact missing fixed-point ingredient sub-goal:
  `∃ f, IsFastRenormalizable f ∧ Rfast f = f`.
- [x] Inventory upstream witness candidates and classify circular vs non-circular routes.
- [x] Add a theorem-level non-circular witness constructor (if found):
  - `FixedPointImpliesRenormalizable`
  - `renormalizable_fixed_exists_of_fixed_point_exists_and_bridge`
- [x] Thread witness constructor into
  `molecule_residual_fixed_point_normalization_ingredients` replacement path.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- This plan is a focused sub-plan of PLAN_49.
- Current blocker: `molecule_residual_fixed_point_normalization_ingredients`
  still carries `Molecule.molecule_h_norm`.
- Inventory result (2026-03-04):
  - `feigenbaum_fixed_point_existence`, `exists_rfast_fixed_point_data`, and
    `renormalizable_fixed_point_exists` all require `h_norm`.
  - `fixed_point_exists` is available without `h_norm` but does not provide
    `IsFastRenormalizable`, so it is insufficient by itself for the ingredient
    witness target.
- New checkpoint (2026-03-04):
  - bridge-based witness constructor theorem is now in place and axiom-clean
    modulo ground axioms; remaining work is to connect a constructive proof of
    `FixedPointImpliesRenormalizable` on the active path.
  - `molecule_residual_fixed_point_existence_source` and
    `molecule_residual_fixed_point_normalization_ingredients` are now routed
    through explicit `bridge + transfer` seams.
