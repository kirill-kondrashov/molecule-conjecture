# PLAN 49 - Constructive Fixed-Point Source Route

Status: ACTIVE
Progress: [#########-] 90%
Scope: Eliminate `molecule_h_norm` from the fixed-point side of the residual source pipeline by replacing the current fixed-point ingredient seed with a constructive theorem-level source.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_normalization_ingredients` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_non_ground_sources` no longer carries `Molecule.molecule_h_norm` from the fixed-point side.
3. `#print axioms Molecule.molecule_conjecture_refined` does not include `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_52_fixed_point_renorm_witness_extraction.md`
Stuck Rule: STUCK if the only available fixed-point data/uniqueness constructors in current infrastructure require reintroducing a project axiom.
Last Updated: 2026-03-04

## Work Plan

- [x] Split fixed-point assembly from orbit source in residual bounds pipeline:
  - `MoleculeResidualFixedPointAssemblySources`
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
- [x] Verify narrowed fixed-point assembly seam theorems are axiom-clean modulo ground axioms.
- [x] Inventory current constructors for fixed-point data/uniqueness and isolate
  residual `molecule_h_norm` entry points.
- [x] Re-orient non-ground source assembly to forward constructor form:
  - `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources`.
- [x] Narrow fixed-point assembly to carry transfer directly (instead of
  uniqueness), reducing the constructive replacement surface:
  - `MoleculeResidualFixedPointAssemblySources.fixedTransfer`
  - `MoleculeResidualNonGroundSources.fixedTransfer`
- [x] Add explicit fixed-point assembly constructor from source seams:
  - `molecule_residual_fixed_point_assembly_sources_of_sources`
  and route current assembly theorem through it.
- [x] Narrow non-ground source pack to carry fixed-point ingredients directly:
  - `MoleculeResidualNonGroundSources.fixedIngredients`.
- [x] Add explicit non-ground constructor from ingredient + local orbit sources:
  - `molecule_residual_non_ground_sources_of_ingredients_and_orbit`
  and route `molecule_residual_non_ground_sources` through it.
- [ ] Add constructive replacement theorem for
  `molecule_residual_fixed_point_normalization_ingredients`.
- [ ] Rebuild `molecule_residual_non_ground_sources` with constructive
  fixed-point ingredient source theorem.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- Current fixed-point source route is still global-norm/ex-falso backed.
- Inventory result (2026-03-04):
  - `molecule_residual_fixed_point_data_source` currently routes through
    `molecule_h_fixed_data_direct`, which depends on
    `renormalizable_fixed_exists_of_global_norm molecule_h_norm` and
    `fixed_point_local_normalization_transfer_of_global_norm molecule_h_norm`.
  - `molecule_residual_fixed_point_uniqueness_source` currently routes through
    `molecule_h_unique`, which is `False.elim molecule_h_norm_inconsistent`.
- New checkpoint (2026-03-04):
  - `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources` is
    axiom-clean modulo ground axioms.
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
    is axiom-clean modulo ground axioms.
  - `molecule_residual_fixed_point_assembly_sources_of_sources` is axiom-clean
    modulo ground axioms.
  - `molecule_residual_fixed_point_assembly_sources` is now reconstructible
    from non-ground ingredients and remains a ground-axiom-only seam theorem.
  - fixed-point blocker has been concentrated to
    `molecule_residual_fixed_point_normalization_ingredients`.
  - `molecule_residual_non_ground_sources_of_ingredients_and_orbit` is
    axiom-clean modulo ground axioms; the current
    `molecule_residual_non_ground_sources` now depends directly on:
    - `molecule_residual_fixed_point_normalization_ingredients`
    - `molecule_residual_orbit_clause_for_fixed_data_source`.
- This plan runs in parallel with PLAN_51 (orbit fixed-data source route).
- Sub-plan linkage:
  - witness extraction bottleneck is tracked explicitly in
    `PLAN_52_fixed_point_renorm_witness_extraction.md`.
