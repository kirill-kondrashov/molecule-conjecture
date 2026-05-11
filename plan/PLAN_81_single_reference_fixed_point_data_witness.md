# PLAN 81 - Single-Reference Fixed-Point Data Witness

Status: ACTIVE
Progress: [######----] 60%
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
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
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
- [x] Identify the smallest live source package that could imply that witness.
- [ ] Attempt a direct single-reference theorem from refined/local data.
- [ ] If that fails, split the target into:
  - renormalizable fixed-point existence
  - local normalization transfer at fixed renormalizable maps
- [x] Cut over the active current existence/transfer theorems to the split
  carriers so the fallback route matches the actual frontier.
- [x] Cut over the active current data/ingredient theorems to the split
  existence+transfer route.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Target exposure | The exact live blocker is explicit: the active current data, ingredient, existence, and transfer theorems now all route through the split existence+transfer frontier. | [#######---] 70% |
| Constructor readiness | Clean constructors already exist from `fixed_exists + transfer`, `ingredients`, and invariant-slice-data. | [######----] 60% |
| Upstream witness search | No non-`molecule_h_norm` producer is known yet for the required single-reference witness; the next rational target is the existence half, now reduced to canonical fast fixed-point data. | [#####-----] 50% |

## Notes

- This plan is the concrete proof-target handoff from PLAN_80.
- What is missing is not another wrapper theorem. The missing theorem is an
  upstream witness of `FixedPointNormalizationData`.
- The two plausible live routes are:
  - direct single-reference proof of `FixedPointNormalizationData`;
  - split proof through `fixed_point_normalization_data_of_fixed_exists_and_transfer`.
- Step-2 checkpoint (2026-03-07):
  - identified the smallest live fallback source package as
    `MoleculeResidualFixedPointNormalizationIngredients`, equivalently the pair
    `(MoleculeResidualFixedPointExistenceSource, MoleculeResidualFixedPointTransferSource)`;
  - added explicit fallback route theorems:
    `molecule_residual_fixed_point_normalization_ingredients_via_existence_and_transfer`,
    `molecule_residual_fixed_point_data_source_via_existence_and_transfer`,
    `molecule_residual_fixed_point_local_witness_on_sources_via_existence_and_transfer`;
  - this does not remove `Molecule.molecule_h_norm`, but it provides a live
    non-stuck split target if the direct single-reference witness route stalls.
- Step-3 checkpoint (2026-03-07):
  - added named current split carriers:
    `molecule_residual_fixed_point_existence_source_via_fixed_data_direct`,
    `molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct`;
  - this makes the split witness target concrete on both halves, instead of
    leaving PLAN_81 to target only an unnamed pair.
- Step-4 cutover checkpoint (2026-03-07):
  - rerouted current
    `molecule_residual_fixed_point_existence_source`
    to `molecule_residual_fixed_point_existence_source_via_fixed_data_direct`;
  - rerouted current
    `molecule_residual_fixed_point_transfer_source`
    to `molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct`;
  - targeted probes show both active current carriers remain
    `Molecule.molecule_h_norm`-backed;
  - next preferred attack is the existence half first, because it has the
    smaller dependency set.
- Step-5 frontier checkpoint (2026-03-07):
  - rerouted current
    `molecule_residual_fixed_point_data_source`
    and
    `molecule_residual_fixed_point_normalization_ingredients`
    through the active split existence+transfer route;
  - targeted probes show the active current data, ingredient, existence, and
    transfer theorems all remain `Molecule.molecule_h_norm`-backed;
  - the routing work is now saturated enough that the next step should be an
    actual existence-side witness attempt, not further split refactors.
- Step-6 existence reduction checkpoint (2026-03-07):
  - added
    `molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source`
    and
    `molecule_residual_fixed_point_existence_source_iff_canonical_fast_fixed_point_data_source`;
  - targeted probes show this reduction is ground-axiom-only;
  - the existence half is now reduced to a canonical fast fixed-point data
    witness, and active continuation moves to `PLAN_82`.
- The dead route is the legacy `InvariantSliceDataWithNormalization` seam,
  already certified closed by PLAN_79.
