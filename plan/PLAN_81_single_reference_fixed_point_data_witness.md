# PLAN 81 - Single-Reference Fixed-Point Data Witness

Status: ACTIVE
Progress: [#---------] 10%
Scope: Prove one concrete non-`molecule_h_norm` witness of
`FixedPointNormalizationData`, then use it to replace
`molecule_residual_fixed_point_data_source_via_fixed_data_direct`.
Acceptance:
1. There is a theorem-level source producing `FixedPointNormalizationData`
   without `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_data_source` does not
   include `Molecule.molecule_h_norm` after cutover.
3. `#print axioms Molecule.molecule_residual_fixed_point_local_witness_on_sources`
   does not include `Molecule.molecule_h_norm` after cutover.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`,
`plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate witness theorem is equivalent to the dead
legacy normalized seam, to global normalization, or simply repackages
`molecule_h_fixed_data_direct`.
Last Updated: 2026-03-07

## Work Plan

- [x] State the missing theorem precisely:
  prove one witness of
  `∃ f : BMol, Rfast f = f ∧ IsFastRenormalizable f ∧ criticalValue f = 0 ∧ f.V ⊆ Metric.ball 0 0.1`
  without `Molecule.molecule_h_norm`.
- [x] Reuse PLAN_80 inventory of clean target constructors.
- [ ] Identify the smallest live source package that could imply that witness.
- [ ] Attempt a direct single-reference theorem from refined/local data.
- [ ] If that fails, split the target into:
  - renormalizable fixed-point existence
  - local normalization transfer at fixed renormalizable maps
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Target exposure | The exact live blocker is explicit: `molecule_residual_fixed_point_data_source` currently routes through `molecule_residual_fixed_point_data_source_via_fixed_data_direct`. | [###-------] 30% |
| Constructor readiness | Clean constructors already exist from `fixed_exists + transfer`, `ingredients`, and invariant-slice-data. | [#####-----] 50% |
| Upstream witness search | No non-`molecule_h_norm` producer is known yet for the required single-reference witness. | [#---------] 10% |

## Notes

- This plan is the concrete proof-target handoff from PLAN_80.
- What is missing is not another wrapper theorem. The missing theorem is an
  upstream witness of `FixedPointNormalizationData`.
- The two plausible live routes are:
  - direct single-reference proof of `FixedPointNormalizationData`;
  - split proof through `fixed_point_normalization_data_of_fixed_exists_and_transfer`.
- The dead route is the legacy `InvariantSliceDataWithNormalization` seam,
  already certified closed by PLAN_79.
