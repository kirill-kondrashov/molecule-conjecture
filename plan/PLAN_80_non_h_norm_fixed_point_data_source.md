# PLAN 80 - Non-h_norm Fixed-Point Data Source

Status: ACTIVE
Progress: [#######---] 70%
Scope: Replace the current `molecule_h_fixed_data_direct` carrier with one
concrete non-`molecule_h_norm` theorem-level source for
`MoleculeResidualFixedPointDataSource`, then feed
`molecule_residual_fixed_point_local_witness_on_sources` through that direct
route.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_data_source` does not
   include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_local_witness_on_sources`
   does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_transfer_source_via_on_sources`
   does not include `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`,
`plan/PLAN_79_invariant_domain_fixed_point_source.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate fixed-point-normalization-data proof still
factors through global normalization, the dead legacy
`InvariantSliceDataWithNormalization` seam, or an equivalent
`molecule_h_fixed_data_direct` wrapper.
Last Updated: 2026-03-07

## Work Plan

- [x] Expose the current local-witness route directly through
  `MoleculeResidualFixedPointDataSource`.
- [x] Record that the legacy
  `MoleculeResidualInvariantSliceDataWithNormalizationSource` seam is dead in
  the current model.
- [x] Inventory all existing non-`molecule_h_norm` inputs strong enough to
  imply one `FixedPointNormalizationData` witness.
- [ ] Attempt a direct single-reference proof of `FixedPointNormalizationData`
  from a live refined/local source.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Minimal blocker exposure | The current `molecule_residual_fixed_point_data_source`, existence, transfer, and downstream local-witness theorems now route through the exact direct frontier: ground `fixed_point_exists` plus exact renormalizability/critical-value/`V`-bound blockers. | [##########] 100% |
| Legacy branch closure | `no_molecule_residual_invariant_slice_data_with_normalization_source` proves the old normalized invariant-slice-data seam is inconsistent in the current model. | [##########] 100% |
| Live source search | Ground-axiom-only constructors exist from ingredients, fixed-exists+transfer, and invariant-slice-data; the missing piece is now a live producer for one of those inputs that does not pass through the dead legacy normalized seam. | [##--------] 20% |

## Notes

- This plan is the live continuation after PLAN_79 certified the legacy
  normalized invariant-slice-data branch as a dead end.
- The concrete proof-target handoff for the missing witness theorem is now
  `PLAN_81_single_reference_fixed_point_data_witness.md`.
- The exact current fixed-data blocker set is now:
  `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`,
  `molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct`,
  and
  `molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct`.
- Step-1 checkpoint (2026-03-07):
  - added direct current-route alias
    `molecule_residual_fixed_point_local_witness_on_sources_via_fixed_data_source`;
  - added minimal theorem-level data-source alias
    `molecule_residual_fixed_point_data_source_via_fixed_data_direct`;
  - rerouted current
    `molecule_residual_fixed_point_data_source`
    through that direct fixed-data carrier;
  - rerouted current
    `molecule_residual_fixed_point_local_witness_on_sources`
    through that direct fixed-data source;
  - added seam-level dead-end theorem
    `no_molecule_residual_invariant_slice_data_with_normalization_source`;
  - `make build` passed;
  - `make check` passed;
  - targeted probes show the dead-end theorem is ground-axiom-only, while the
    current local-witness theorem still carries `Molecule.molecule_h_norm`
    through `molecule_h_fixed_data_direct`.
- Step-2 inventory checkpoint (2026-03-07):
  - verified ground-axiom-only constructors:
    `fixed_point_normalization_data_of_fixed_exists_and_transfer`,
    `fixed_point_normalization_data_of_ingredients`,
    `fixed_point_normalization_data_of_invariant_slice_data`,
    `molecule_residual_fixed_point_data_source_of_invariant_slice_data_with_normalization_source`;
  - result: the live route is not dead, but it is narrower than before;
  - the remaining task is to produce one of the constructor inputs without
    passing through `molecule_h_fixed_data_direct` or the dead legacy
    `InvariantSliceDataWithNormalization` seam.
- Step-3 fallback checkpoint (2026-03-07):
  - added explicit split fallback route through current existence + transfer:
    `molecule_residual_fixed_point_normalization_ingredients_via_existence_and_transfer`,
    `molecule_residual_fixed_point_data_source_via_existence_and_transfer`;
  - this identifies the smallest live fallback package for PLAN_81 without
    changing the current direct fixed-data carrier theorem.
- Step-4 split-carrier checkpoint (2026-03-07):
  - added named current split carriers:
    `molecule_residual_fixed_point_existence_source_via_fixed_data_direct`,
    `molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct`;
  - this isolates the current existence-side and transfer-side theorem carriers
    for the PLAN_81 fallback route.
- Step-5 active-cutover checkpoint (2026-03-07):
  - rerouted current `molecule_residual_fixed_point_existence_source` and
    `molecule_residual_fixed_point_transfer_source` through the direct split
    carriers;
  - this makes the PLAN_81 split fallback the active frontier, not just a
    candidate side route.
- Step-6 data-frontier checkpoint (2026-03-07):
  - rerouted current `molecule_residual_fixed_point_data_source` and
    `molecule_residual_fixed_point_normalization_ingredients` through the split
    existence+transfer frontier;
  - this completes the active cutover from bundled fixed-data current routes to
    the split frontier.
- Step-7 existence reduction checkpoint (2026-03-07):
  - reduced the existence half to canonical fast fixed-point data via
    `molecule_residual_fixed_point_existence_source_iff_canonical_fast_fixed_point_data_source`;
  - active existence-side continuation now moves to `PLAN_82`.
- Step-8 fixed-data split checkpoint (2026-03-07):
  - added
    `molecule_residual_fixed_exists_via_global_norm_direct`,
    `molecule_residual_fixed_point_local_normalization_transfer_via_global_norm_direct`,
    and
    `molecule_residual_fixed_point_data_source_via_fixed_exists_and_transfer_direct`;
  - rerouted
    `molecule_residual_fixed_point_data_source_via_fixed_data_direct`
    through those two direct theorem carriers;
  - targeted probes show the fixed-data branch is still
    `Molecule.molecule_h_norm`-backed, but its exact blocker pair is now
    explicit.
- Step-9 fixed-data primitive checkpoint (2026-03-07):
  - added
    `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`,
    `molecule_residual_fixed_exists_via_fixed_point_exists_and_renorm_direct`,
    `molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct`,
    and
    `molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct`;
  - rerouted
    `molecule_residual_fixed_exists_via_global_norm_direct`
    through ground `fixed_point_exists` plus the direct renormalizability
    carrier;
  - rerouted
    `molecule_residual_fixed_point_local_normalization_transfer_via_global_norm_direct`
    through direct critical-value and `V`-bound carriers;
  - targeted probes show `fixed_point_exists` is ground-axiom-only, so the
    remaining fixed-data debt is now concentrated in:
    `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`,
    `molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct`,
    and
    `molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct`.
- Step-10 primitive-ingredient checkpoint (2026-03-07):
  - added
    `residual_fixed_point_normalization_ingredients_of_fixed_point_exists_and_component_transfers`
    and current-route alias
    `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`;
  - rerouted
    `molecule_residual_fixed_point_data_source_via_fixed_exists_and_transfer_direct`
    through that explicit primitive-ingredient theorem;
  - this makes the fixed-data branch mathematically exact: ground
    `fixed_point_exists` plus the three remaining non-ground carriers
    (`renormalizable`, critical-value transfer, `V`-bound transfer).
- Step-11 transfer primitive checkpoint (2026-03-08):
  - added
    `fixed_point_local_normalization_transfer_of_ingredients_and_unique`;
  - rerouted
    `molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct`
    through
    `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`
    and
    `molecule_residual_fixed_point_uniqueness_direct_source`;
  - this removes the extra `FixedPointNormalizationData` wrapper from the
    active transfer branch and aligns the transfer frontier with the primitive
    fixed-data blocker set;
  - targeted probes show the new constructor is ground-axiom-only, while the
    current transfer theorem is now blocked exactly by
    `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`
    and
    `molecule_residual_fixed_point_uniqueness_direct_source`.
- Step-12 direct-projection checkpoint (2026-03-08):
  - added
    `fixed_point_local_normalization_transfer_of_ingredients`;
  - rerouted
    `molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct`
    directly through
    `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`;
  - this removes the remaining uniqueness wrapper from the active transfer
    frontier; the transfer theorem is now a direct projection from the
    primitive fixed-point ingredient carrier.
- Step-13 exact-carrier checkpoint (2026-03-08):
  - added
    `fixed_point_normalization_data_of_fixed_point_exists_and_component_transfers`;
  - rerouted current
    `molecule_residual_fixed_point_data_source_via_fixed_exists_and_transfer_direct`
    directly through the exact non-ground carrier triple:
    `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`,
    `molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct`,
    and
    `molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct`;
  - rerouted current
    `molecule_residual_fixed_point_existence_source` through the ground
    fixed-point theorem plus the direct renormalizability carrier;
  - rerouted current transfer and local-witness theorems to consume those
    exact direct component carriers.
