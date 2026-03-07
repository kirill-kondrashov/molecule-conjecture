# PLAN 78 - Non-h_norm Local Witness-On-Sources Theorem

Status: ACTIVE
Progress: [######----] 60%
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
- [ ] Attempt a theorem from localized normalization data plus a fixed-point-in-
  `K` witness.
- [ ] Attempt a theorem from refined-chart invariant slice-data with
  normalization, if that package can be shown to contain an `Rfast` fixed point.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Concrete target exposure | The concrete local-domain witness target is explicit in `Molecule/Conjecture.lean` and current local-witness routing now goes through it. | [####------] 40% |
| Transfer-branch cutover readiness | `molecule_residual_fixed_point_local_witness_sources` and `molecule_residual_fixed_point_transfer_source_via_on_sources` already consume the concrete target theorem, so a replacement there will propagate immediately. | [#####-----] 50% |
| Proof-source search | `PLAN_79` now isolates invariant slice-data, fixed-point-in-domain, bridge-on, refined fixed-point, and direct local-witness ingredient seams; current local-witness routing uses the refined pack, but no non-`molecule_h_norm` normalized-source producer exists yet. | [#####-----] 50% |

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
