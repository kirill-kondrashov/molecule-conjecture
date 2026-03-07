# PLAN 78 - Non-h_norm Local Witness-On-Sources Theorem

Status: ACTIVE
Progress: [##--------] 20%
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
| Proof-source search | No non-`molecule_h_norm` theorem has been found yet for the concrete target. | [#---------] 10% |

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
