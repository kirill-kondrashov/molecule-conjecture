# PLAN 86 - Localized Or Reseeded Replacement For R

Status: DONE
Progress: [##########] 100%
Scope: Structural handoff plan for replacing the formally blocked global witness-side carrier
`R := ∀ f : BMol, Rfast f = f -> IsFastRenormalizable f`
by a viable theorem shape on the active downstream routes.

The direct global `R` route is false in the current scaffold, so this plan does
not try to prove `R`. It targets one of two viable replacements:
- a localized bridge `R_K` on a concrete live domain `K`, or
- a reseeded existence theorem that avoids the global `fixed_point_exists`
  witness route entirely.

Acceptance:
1. No step in this plan attempts to prove literal global `R`.
2. The structural frontier is reduced to exact theorem targets rather than
   wrapper prose.
3. The localized and reseeded singleton routes are compared honestly against
   each other and against canonical data.
4. The downstream handoff into existence / canonical / fixed-data /
   local-witness is explicit.
5. Remaining live theorem search is handed off to a more focused plan.

Dependencies: `Molecule/Conjecture.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_83_localized_fixed_point_renormalizability_bridge.md`,
`plan/PLAN_84_canonical_seed_replacement_for_existence_route.md`,
`plan/PLAN_85_upstream_four_carrier_burndown.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`

Completion Rule: DONE once the plan has isolated the real remaining theorem
targets and no further progress can come from route reshaping alone.

Last Updated: 2026-03-09

## Research Program

- [x] Record the blocking fact from PLAN_85:
  global `R` is false in the current scaffold.
- [x] Localized singleton branch made concrete and compared against the seed
  route.
- [x] Reseeded singleton branch made concrete and compared against canonical
  fast fixed-point data.
- [x] Exact larger-domain localized target exposed.
- [x] Exact downstream rebase interface exposed.
- [x] Structural work saturated; theorem search handed off.

## Priority Order

1. Finish structural reductions
2. Expose exact remaining theorem targets
3. Hand off active theorem search

## Carrier Dictionary

```text
R  := ∀ f : BMol, Rfast f = f -> IsFastRenormalizable f

R_K := ∀ f : BMol, f ∈ K -> Rfast f = f -> IsFastRenormalizable f

RV := ∀ f : BMol, IsFastRenormalizable f -> criticalValue f = 0 ->
        f.V ⊆ Metric.ball 0 0.1
```

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Blocked global route inventory | `R` is formally blocked by `no_molecule_residual_fixed_point_renormalizable_source`. | [##########] 100% |
| Localized singleton analysis | Concrete, but equivalent to the reseeded/canonical singleton route and incapable of witnessing the required larger-domain target. | [##########] 100% |
| Reseeded singleton analysis | Concrete and compared against canonical data; remaining debt is upstream seed production. | [##########] 100% |
| Downstream rebase interface | Exact interface exposed: existence + critical-value transfer + `RV`, with full structural cutovers in place. | [##########] 100% |
| Handoff readiness | Remaining live theorem search isolated and ready for focused follow-on plan. | [##########] 100% |

## Notes

- PLAN_85 is complete as a burndown/handoff plan.
- The direct current existence route is now exactly:
  ground `fixed_point_exists` + global `R`.
- The direct current canonical route is now exactly:
  current existence route.
- New checkpoint:
  - added
    `molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source`
  - added
    `molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source_via_bridge_on`
  - targeted probes show both new theorems are ground-axiom-only
  - this means the localized and reseeded branches now share one clean
    singleton-bridge seam that avoids both `fixed_point_exists` and
    `selected_fixed_point`
- New checkpoint:
  - added
    `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_of_renormalizable_fixed_seed_source`
  - added
    `molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain`
  - added
    `molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain`
  - targeted probes show the localized seed-domain bridge and existence route
    are ground-axiom-only
  - this makes the localized branch concrete, but only on a singleton domain
    under the current refined witness
- New checkpoint:
  - added
    `molecule_residual_renormalizable_fixed_seed_source_of_refined_invariant_fixed_seed_singleton_domain_sources`
  - added
    `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_renormalizable_fixed_seed_source`
  - targeted probes show both new reduction theorems are ground-axiom-only
  - this means the current localized refined-singleton branch is not stronger
    than the reseeded branch: it is equivalent to the same seed source
- New checkpoint:
  - added
    `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_canonical_fast_fixed_point_data_source`
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_refined_invariant_fixed_seed_singleton_domain_sources`
  - added
    `molecule_residual_fixed_point_existence_source_of_refined_invariant_fixed_seed_singleton_domain_sources`
  - targeted probes show all three new comparison/cutover theorems are
    ground-axiom-only
  - this means the current localized refined-singleton branch is also exactly
    as strong as canonical fast fixed-point data
- New checkpoint:
  - added the exact larger-domain target
    `MoleculeResidualNonSingletonLocalizedBridgeSources`
  - added
    `molecule_residual_fixed_point_bridge_on_source_of_non_singleton_localized_bridge_sources`
    and
    `molecule_residual_fixed_point_existence_source_of_non_singleton_localized_bridge_sources`
  - added
    `no_nontrivial_member_of_refined_invariant_fixed_seed_singleton_domain_sources`
  - targeted probes show all three theorems are ground-axiom-only
  - this means the current refined singleton route cannot be the sought larger
    localized replacement
- New checkpoint:
  - added the stronger downstream seed contract
    `MoleculeResidualCriticalRenormalizableFixedSeedSource`
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_fixed_point_existence_source_and_critical_value_transfer`
  - added
    `molecule_residual_fixed_point_data_source_of_existence_and_critical_value_transfer_and_renorm_vbound`
    and
    `molecule_residual_fixed_point_local_witness_on_sources_of_existence_and_critical_value_transfer_and_renorm_vbound`
  - targeted probes show those three new theorems are ground-axiom-only
  - this means the downstream rebase requirement is now exact:
    replacement existence alone is too weak; the `PLAN_80` / `PLAN_78`
    branches need existence + critical-value transfer + `RV`
- New checkpoint:
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_non_singleton_localized_bridge_sources`
  - added
    `molecule_residual_fixed_point_data_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound`
  - added
    `molecule_residual_fixed_point_local_witness_on_sources_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound`
    and
    `molecule_residual_fixed_point_local_witness_sources_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound`
  - targeted probes show all four downstream cutovers are ground-axiom-only
  - this completes the structural handoff: a non-singleton localized bridge
    source would now propagate through existence, canonical, fixed-data, and
    local-witness
- Critical revision:
  - This plan became too broad once the singleton localized route, singleton
    reseeded route, and canonical seed route were shown equivalent.
  - It also mixed two different tasks:
    1. theorem search for an upstream seed/bridge source
    2. structural downstream handoff
  - The structural task is complete; the theorem search should now live in a
    narrower plan.
- Handoff:
  - Active focused follow-on is now
    `PLAN_88_dual_track_seed_or_non_singleton_localized_bridge.md`.
  - `PLAN_87_non_circular_critical_seed_source.md` remains useful, but only as
    the seed-side subtrack inside that broader program.
  - Larger-domain localized redesign is no longer treated as a mere fallback;
    it is a co-equal live branch under PLAN_88.
