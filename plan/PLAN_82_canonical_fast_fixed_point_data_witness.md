# PLAN 82 - Canonical Fast Fixed-Point Data Witness

Status: ACTIVE
Progress: [######----] 60%
Scope: Replace the current `Molecule.molecule_h_norm`-backed canonical
fixed-point source with a non-`molecule_h_norm` theorem producing
`MoleculeResidualCanonicalFastFixedPointDataSource`.
Acceptance:
1. `#print axioms Molecule.molecule_residual_canonical_fast_fixed_point_data_source`
   does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_existence_source`
   does not include `Molecule.molecule_h_norm`.
3. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_76_non_h_norm_anchor_witness_bottleneck_break.md`
Stuck Rule: STUCK if every canonical fixed-point witness candidate still
factors through the current existence source or another equivalent
`molecule_h_norm` carrier.
Last Updated: 2026-03-07

## Work Plan

- [x] Verify that canonical fast fixed-point data is equivalent to the
  existence-side split target.
- [x] Identify the smallest live source package that could imply canonical fast
  fixed-point data directly.
- [ ] Attempt a non-`molecule_h_norm` canonical witness theorem.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Target exposure | The existence half is now formally reduced to `MoleculeResidualCanonicalFastFixedPointDataSource`, and the current canonical theorem is rerouted through fixed-point ingredients plus the fixed-data canonical orbit debt source. | [##########] 100% |
| Downstream leverage | The active canonical route now consumes the transfer-routed orbit-debt alias, so canonical work shares the transfer branch explicitly. | [#######---] 70% |
| Witness search | The live upstream package is now split as `MoleculeResidualFixedPointIngredientsSource` together with the transfer-routed orbit-debt alias; no non-`molecule_h_norm` witness for that combination is known yet. | [#####-----] 50% |

## Notes

- This plan is the existence-side subtarget of PLAN_81.
- Ground-axiom-only equivalence is already available:
  `molecule_residual_fixed_point_existence_source_iff_canonical_fast_fixed_point_data_source`.
- The current canonical source theorem is still `Molecule.molecule_h_norm`-
  backed.
- Step-2 bounds-package checkpoint (2026-03-07):
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_bounds`,
    `molecule_residual_canonical_fast_fixed_point_data_source_of_bounds_assembly_sources`,
    and
    `molecule_residual_canonical_fast_fixed_point_data_source_of_non_ground_sources`;
  - rerouted current
    `molecule_residual_canonical_fast_fixed_point_data_source`
    through `molecule_residual_bounds_assembly_sources`;
  - this identifies the current smallest live upstream package for PLAN_82 as
    `MoleculeResidualBoundsAssemblySources`;
  - the remaining gap is no longer generic canonical existence, but a
    non-`molecule_h_norm` producer for that bounds-assembly package.
- Step-3 frontier split checkpoint (2026-03-07):
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_orbit_clause_source`
    and
    `molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_orbit_clause_source`;
  - rerouted current
    `molecule_residual_canonical_fast_fixed_point_data_source`
    through
    `molecule_residual_fixed_point_ingredients_source`
    and
    `molecule_residual_orbit_clause_source`;
  - targeted probes should now show the existence-side canonical blocker as the
    pair of current ingredient and orbit-clause carriers, rather than the
    coarser bounds-assembly package.
- Step-4 local-orbit frontier checkpoint (2026-03-07):
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_orbit_clause_at_source`
    and
    `molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_orbit_clause_at_source`;
  - rerouted current
    `molecule_residual_canonical_fast_fixed_point_data_source`
    through
    `molecule_residual_fixed_point_ingredients_source`
    and
    `molecule_residual_orbit_clause_at_source`;
  - this shows the broad orbit-clause wrapper is no longer part of the active
    canonical frontier; the live blocker is now the smaller pair of ingredient
    and local orbit-at carriers.
- Step-5 canonical-orbit frontier checkpoint (2026-03-07):
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_canonical_orbit_at_debt_source`
    and
    `molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_canonical_orbit_at_debt_source`;
  - rerouted current
    `molecule_residual_canonical_fast_fixed_point_data_source`
    through
    `molecule_residual_fixed_point_ingredients_source`
    and
    `molecule_residual_canonical_orbit_at_debt_source`;
  - this removes the stronger local orbit-at wrapper from the active canonical
    frontier; the remaining existence-side blockers are now the current
    ingredient carrier and the current fixed-data canonical orbit debt source.
- Step-6 transfer-shared orbit checkpoint (2026-03-07):
  - rerouted
    `molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_canonical_orbit_at_debt_source`
    through
    `molecule_residual_canonical_orbit_at_debt_source_via_fixed_point_transfer_source`;
  - this means the active canonical route now shares the transfer branch
    explicitly on the orbit side, without needing to move the earlier current
    debt declarations.
