# PLAN 49 - Constructive Fixed-Point Source Route

Status: ACTIVE
Progress: [##--------] 20%
Scope: Eliminate `molecule_h_norm` from the fixed-point side of the residual source pipeline by replacing the current fixed-data/uniqueness seeds with constructive theorem-level sources.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_data_source` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source` does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_non_ground_sources` no longer carries `Molecule.molecule_h_norm` from the fixed-point side.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`
Stuck Rule: STUCK if the only available fixed-point data/uniqueness constructors in current infrastructure require reintroducing a project axiom.
Last Updated: 2026-03-04

## Work Plan

- [x] Split fixed-point assembly from orbit source in residual bounds pipeline:
  - `MoleculeResidualFixedPointAssemblySources`
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
- [x] Verify narrowed fixed-point assembly seam theorems are axiom-clean modulo ground axioms.
- [ ] Add constructive replacement theorem for `molecule_residual_fixed_point_data_source`.
- [ ] Add constructive replacement theorem for `molecule_residual_fixed_point_uniqueness_source`.
- [ ] Rebuild `molecule_residual_non_ground_sources` with constructive fixed-point source theorems.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- Current fixed-point source route is still global-norm/ex-falso backed.
- This plan runs in parallel with PLAN_48 (orbit clause route).
