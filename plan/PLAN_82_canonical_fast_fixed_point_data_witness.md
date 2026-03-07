# PLAN 82 - Canonical Fast Fixed-Point Data Witness

Status: ACTIVE
Progress: [#---------] 10%
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
- [ ] Identify the smallest live source package that could imply canonical fast
  fixed-point data directly.
- [ ] Attempt a non-`molecule_h_norm` canonical witness theorem.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Target exposure | The existence half is now formally reduced to `MoleculeResidualCanonicalFastFixedPointDataSource`. | [#####-----] 50% |
| Downstream leverage | A canonical witness would also feed downstream uniqueness/anchor routes already consuming canonical data. | [######----] 60% |
| Witness search | No non-`molecule_h_norm` canonical witness source is known yet. | [#---------] 10% |

## Notes

- This plan is the existence-side subtarget of PLAN_81.
- Ground-axiom-only equivalence is already available:
  `molecule_residual_fixed_point_existence_source_iff_canonical_fast_fixed_point_data_source`.
- The current canonical source theorem is still `Molecule.molecule_h_norm`-
  backed.
