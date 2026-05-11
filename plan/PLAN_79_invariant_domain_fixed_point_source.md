# PLAN 79 - Invariant-Domain Fixed-Point Source

Status: STUCK
Progress: [#######---] 70%
Scope: Turn the invariant-domain route into an explicit upstream source for
`molecule_residual_fixed_point_local_witness_on_sources`, using
`InvariantSliceDataWithNormalization` rather than the current
`molecule_h_fixed_data_direct` value.
Acceptance:
1. `Molecule/Conjecture.lean` exposes an explicit source seam for
   `InvariantSliceDataWithNormalization`.
2. There is a theorem from that source seam to
   `MoleculeResidualFixedPointDataSource`.
3. There is a direct constructor from that source seam to
   `MoleculeResidualFixedPointLocalWitnessOnSources`.
4. `#print axioms` for the new source-to-data theorem and source-to-local-
   witness constructor excludes `Molecule.molecule_h_norm`.
5. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`
Stuck Rule: STUCK if the invariant-domain source seam can only be fed by
legacy `slice_chart` witnesses equivalent to global normalization, with no
constructive source candidate left to test.
Last Updated: 2026-03-07

## Work Plan

- [x] Expose the invariant-domain route as an explicit source seam.
- [x] Add direct invariant-domain -> fixed-point-data theorem.
- [x] Add direct invariant-domain -> local-witness theorem.
- [x] Add refined invariant fixed-point source pack and route the current
  local-witness theorem through it.
- [x] Add invariant-slice-data -> fixed-point-in-domain and normalized-package
  -> bridge-on/existence theorems.
- [x] Determine whether the legacy normalized invariant-domain seam is
  constructively live or dead in the current model.
- [ ] Identify a non-`molecule_h_norm` producer for the invariant-domain source
  seam.
- [ ] Attempt transfer-branch cutover through the new invariant-domain source
  once a producer exists.
- [x] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Source seam exposure | The invariant-domain package now has dedicated residual source targets for invariant slice-data, fixed-point-in-domain, bridge-on, refined fixed-point packs, and direct local-witness ingredients. | [########--] 80% |
| Local-witness derivation | The source-to-data theorem, the refined fixed-point pack, and the direct local-witness ingredient theorem are implemented and probe ground-axiom-only. | [#######---] 70% |
| Source producer search | The only legacy seam producer collapses to global normalization, and `no_molecule_residual_invariant_slice_data_with_normalization_source` now certifies that this branch is dead in the current model. | [##########] 100% dead |

## Notes

- This is a focused subplan under `PLAN_78`.
- The immediate value is not cutover by itself; it isolates the next proof
  target to the existence of an invariant-domain source, instead of the larger
  transfer branch.
- Checkpoint (2026-03-07, step-1):
  - added source seam:
    `MoleculeResidualInvariantSliceDataWithNormalizationSource`;
  - added direct projections:
    `molecule_residual_fixed_point_data_source_of_invariant_slice_data_with_normalization_source`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_invariant_slice_data_with_normalization_source`;
  - `make build` passed;
  - `make check` passed;
  - targeted probes show both new projections are ground-axiom-only, while the
    active current-route theorems
    `molecule_residual_fixed_point_local_witness_on_sources` and
    `molecule_residual_fixed_point_transfer_source_via_on_sources`
    still carry `Molecule.molecule_h_norm`.
- Inventory checkpoint (2026-03-07, step-2):
  - current search shows the only producer of
    `InvariantSliceDataWithNormalization` is still
    `invariant_slice_data_with_normalization_of_global`;
  - there is no existing non-`molecule_h_norm` producer yet for
    `MoleculeResidualInvariantSliceDataWithNormalizationSource`;
  - this confirms the next proof target is the source producer itself, not the
    downstream transfer routing.
- Refined-route checkpoint (2026-03-07, step-3):
  - added refined fixed-point pack:
    `MoleculeResidualRefinedInvariantFixedPointSources`;
  - added clean constructor:
    `molecule_residual_refined_invariant_fixed_point_sources_of_fixed_data`;
  - added projection:
    `molecule_residual_fixed_point_local_witness_on_sources_of_refined_invariant_fixed_point_sources`;
  - rerouted current
    `molecule_residual_fixed_point_local_witness_on_sources`
    through the refined fixed-point pack;
  - `make build` passed;
  - `make check` passed;
  - targeted probes show the new refined-pack constructor and projection are
    ground-axiom-only, while the current routed theorem still carries
    `Molecule.molecule_h_norm` because its current producer remains
    `molecule_h_fixed_data_direct`.
- Invariant-fixed-point checkpoint (2026-03-07, step-4):
  - added source seams:
    `MoleculeResidualInvariantSliceDataSource`,
    `MoleculeResidualInvariantSliceFixedPointSource`;
  - added ground-axiom-only theorems:
    `molecule_residual_invariant_slice_fixed_point_source_of_invariant_slice_data_source`,
    `molecule_residual_fixed_point_bridge_on_source_of_invariant_slice_data_with_normalization_source`,
    `molecule_residual_fixed_point_existence_source_of_invariant_slice_data_with_normalization_source`;
  - `make build` passed;
  - `make check` passed;
  - targeted probes show the fixed-point-in-domain and bridge/existence route
    from invariant slice-data-with-normalization is ground-axiom-only.
  - The remaining blocker is narrower: producing normalized invariant
    slice-data without `Molecule.molecule_h_norm`.
- Normalization-split checkpoint (2026-03-07, step-5):
  - factored the reusable theorem
    `invariant_slice_fixed_point_in_of_sources`;
  - added proposition-level local-witness ingredients theorem
    `invariant_slice_local_witness_ingredients_of_with_normalization`;
  - rerouted the normalized-package local-witness constructor through that
    fixed-point-plus-normalization split;
  - `make build` passed;
  - `make check` passed;
  - targeted probes show the new helper, ingredient theorem, and direct
    local-witness route from normalized invariant slice-data are
    ground-axiom-only.
- Dead-end checkpoint (2026-03-07, step-6):
  - added
    `invariant_slice_data_with_normalization_implies_global_normalization_contract`;
  - added
    `no_invariant_slice_data_with_normalization`;
  - added seam-level alias
    `no_molecule_residual_invariant_slice_data_with_normalization_source`;
  - `make build` passed;
  - `make check` passed;
  - targeted probes show the new dead-end theorems are ground-axiom-only;
  - result: the legacy `InvariantSliceDataWithNormalization` route is closed in
    the current model, so active continuation moves to `PLAN_80`.
- Expected next candidates:
  - no further candidates remain for the legacy
    `InvariantSliceDataWithNormalization` seam in the current scaffold;
  - live continuation is `PLAN_80`, which targets a direct non-
    `molecule_h_norm` `FixedPointNormalizationData` producer instead.
