# PLAN 78 - Non-h_norm Local Witness-On-Sources Theorem

Status: ACTIVE
Progress: [########--] 80%
Scope: Replace the current transfer-branch local witness root with one
concrete non-`molecule_h_norm` theorem:
`molecule_residual_fixed_point_local_witness_on_sources`.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_local_witness_on_sources`
   does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_local_witness_sources`
   does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_transfer_source_via_on_sources`
   does not include `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`,
`Molecule/BanachSlice.lean`,
`plan/PLAN_79_invariant_domain_fixed_point_source.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`,
`plan/PLAN_77_upstream_model_change_for_non_h_norm_fixed_point_sources.md`
Stuck Rule: STUCK if every candidate proof of
`molecule_residual_fixed_point_local_witness_on_sources` still factors through
`molecule_h_fixed_data_direct` or an equivalent `molecule_h_norm`-backed local
witness.
Last Updated: 2026-03-07

## Work Plan

- [x] Make the concrete target explicit in code:
  - `MoleculeResidualFixedPointLocalWitnessOnSources`
  - `molecule_residual_fixed_point_local_witness_sources_of_on_sources`
  - current target theorem
    `molecule_residual_fixed_point_local_witness_on_sources`
- [x] Rebase current local-witness theorem through the concrete target.
- [ ] Identify the strongest existing non-`molecule_h_norm` data that could
  imply:
  - existence of a fixed point in some `K`
  - `NormalizationOn K`
- [x] Expose the invariant-domain route as a dedicated subplan:
  `PLAN_79_invariant_domain_fixed_point_source.md`.
- [x] Certify whether the legacy
  `InvariantSliceDataWithNormalization` branch is live or dead under the
  current scaffold.
- [x] Reduce the current local-witness route to its minimal live blocker:
  `molecule_h_fixed_data_direct`.
- [ ] Attempt a direct replacement of `MoleculeResidualFixedPointDataSource`
  through `PLAN_80`.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Concrete target exposure | The concrete local-domain witness target is explicit in `Molecule/Conjecture.lean` and current local-witness routing now goes directly through the exact three non-ground fixed-point component carriers instead of the fixed-data wrapper. | [#########-] 90% |
| Transfer-branch cutover readiness | `molecule_residual_fixed_point_local_witness_sources` and `molecule_residual_fixed_point_transfer_source_via_on_sources` now consume the direct component-transfer local-witness route, so a replacement there will propagate immediately. | [########--] 80% |
| Proof-source search | `PLAN_79` closed the legacy normalized invariant-slice-data branch as a dead end; the live search is now `PLAN_80`, targeting a non-`molecule_h_norm` `FixedPointNormalizationData` source. | [######----] 60% |

## Notes

- This plan is the active handoff from `PLAN_77`, whose seam-only decomposition
  is now considered saturated.
- Current concrete root theorem:
  `molecule_residual_fixed_point_local_witness_on_sources`.
- Current current-route construction still comes from
  `molecule_h_fixed_data_direct`, so the concrete target remains
  `Molecule.molecule_h_norm`-backed.
- New checkpoint (2026-03-07, step-1 attempt):
  - Added explicit concrete target:
    `MoleculeResidualFixedPointLocalWitnessOnSources`.
  - Added source-level constructors:
    `molecule_residual_fixed_point_local_witness_sources_of_on_sources`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data`.
  - Rebased current
    `molecule_residual_fixed_point_local_witness_sources`
    onto `molecule_residual_fixed_point_local_witness_on_sources`.
  - Targeted probes:
    constructor theorems are ground-axiom-only; current target theorem
    `molecule_residual_fixed_point_local_witness_on_sources` and the derived
    theorem `molecule_residual_fixed_point_transfer_source_via_on_sources`
    remain `Molecule.molecule_h_norm`-backed until a new witness proof is
    found.
- New checkpoint (2026-03-07, step-2 invariant-domain split):
  - Opened `PLAN_79_invariant_domain_fixed_point_source.md`.
  - PLAN_79 isolates the invariant-domain route behind an explicit source seam
    for `InvariantSliceDataWithNormalization`.
  - The next immediate proof target is no longer the whole transfer branch; it
    is a producer for that invariant-domain source seam.
  - First PLAN_79 implementation added:
    `MoleculeResidualInvariantSliceDataWithNormalizationSource`,
    `molecule_residual_fixed_point_data_source_of_invariant_slice_data_with_normalization_source`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_invariant_slice_data_with_normalization_source`.
  - Targeted probes show the new invariant-domain projections are
    ground-axiom-only; the current concrete target theorem remains
    `Molecule.molecule_h_norm`-backed because no active source producer exists
    yet for the invariant-domain seam.
  - Second PLAN_79 implementation added:
    `MoleculeResidualRefinedInvariantFixedPointSources`,
    `molecule_residual_refined_invariant_fixed_point_sources_of_fixed_data`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_refined_invariant_fixed_point_sources`.
  - Current
    `molecule_residual_fixed_point_local_witness_on_sources`
    is now routed through that refined fixed-point pack.
  - Targeted probes show the new refined-pack route is ground-axiom-only
    upstream, while the current theorem remains `Molecule.molecule_h_norm`-
    backed through `molecule_h_fixed_data_direct`.
  - Added invariant-slice-data fixed-point route:
    `molecule_residual_invariant_slice_fixed_point_source_of_invariant_slice_data_source`.
  - Added normalized-package bridge/existence route:
    `molecule_residual_fixed_point_bridge_on_source_of_invariant_slice_data_with_normalization_source`,
    `molecule_residual_fixed_point_existence_source_of_invariant_slice_data_with_normalization_source`.
  - Targeted probes show these new theorems are ground-axiom-only. This
    settles the fixed-point-in-`K` part; the remaining unsolved ingredient is a
    non-`molecule_h_norm` producer of normalized invariant slice-data.
  - Added direct local-witness ingredient split:
    `invariant_slice_fixed_point_in_of_sources`,
    `invariant_slice_local_witness_ingredients_of_with_normalization`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_invariant_slice_data_with_normalization_source_via_invariant_slice_fixed_point`.
  - Targeted probes show the new helper and direct local-witness route are
    ground-axiom-only. The remaining unsolved ingredient is unchanged:
    a non-`molecule_h_norm` producer of normalized invariant slice-data.
  - Added dead-end certificate for the legacy normalized seam:
    `no_molecule_residual_invariant_slice_data_with_normalization_source`.
  - Rerouted current
    `molecule_residual_fixed_point_local_witness_on_sources`
    directly through
    `molecule_residual_fixed_point_local_witness_on_sources_via_fixed_data_source`.
  - Active continuation therefore moves to `PLAN_80`: replace
    `molecule_h_fixed_data_direct` itself rather than continue on the dead
    legacy invariant-domain branch.
- New checkpoint (2026-03-08, primitive-ingredient cutover):
  - added
    `molecule_residual_fixed_point_local_witness_sources_of_ingredients`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_ingredients`,
    and
    `molecule_residual_fixed_point_local_witness_on_sources_via_ingredients_source`;
  - rerouted current
    `molecule_residual_fixed_point_local_witness_on_sources`
    and
    `molecule_residual_fixed_point_local_witness_sources`
    through
    `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`;
  - this removes the remaining `FixedPointNormalizationData` wrapper from the
    active local-witness branch, aligning it with the PLAN_80 primitive
    ingredient frontier.
- New checkpoint (2026-03-08, direct-component cutover):
  - added
    `molecule_residual_fixed_point_local_witness_sources_of_fixed_point_exists_and_component_transfers`
    and
    `molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_component_transfers`;
  - rerouted current
    `molecule_residual_fixed_point_local_witness_on_sources`
    and
    `molecule_residual_fixed_point_local_witness_sources`
    through the exact three current non-ground component carriers:
    `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`,
    `molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct`,
    and
    `molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct`;
  - targeted probes show the downstream local-witness theorems are now aligned
    with the exact fixed-point frontier.
