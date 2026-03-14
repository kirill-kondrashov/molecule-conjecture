# PLAN 88 - Dual-Track Seed Or Non-Singleton Localized Bridge

Status: ACTIVE
Progress: [########--] 80%
Scope: Coordination and gating plan for replacing the formally blocked global
witness-side route while distinguishing theorem-shape viability from current
operational plausibility:

1. a non-circular critical seed source
2. a genuinely non-singleton localized bridge source

This plan is the critical revision of the current research program. It exists
because PLAN_87 was too narrow as a master program: seed search is only one
subtrack, not the whole live search space. But the newest obstruction results
also show that the two theorem shapes should not be treated as equally active
day-to-day searches. It is not itself the owner of every remaining theorem on
the downstream branches.

Acceptance:
1. Treat either of the following only as a real upstream breakthrough:
   - `MoleculeResidualCriticalRenormalizableFixedSeedSource`
   - `MoleculeResidualNonSingletonLocalizedBridgeSources`
   both without `Molecule.molecule_h_norm`.
2. Do not count as progress any producer that is definitionally equivalent to:
   - the current canonical singleton route
   - the refined singleton-domain route
   - the current existence route
   - the formally blocked global `R` route
3. On the localized-side track, do not count as progress any `K` or bridge
   package that is defined from, or whose proof factors through:
   - `MoleculeResidualRenormalizableFixedSeedSource`
   - `MoleculeResidualCriticalRenormalizableFixedSeedSource`
   - any definition explicitly mentioning `IsFastRenormalizable`
   - the current singleton/canonical equivalence class
4. Treat localized-side work as active only after naming a concrete producer
   class outside the now-closed refined-chart / `slice_chart_refined`
   scaffold, together with an explicit plausibility case that it can avoid the
   singleton/global-`R` collapse.
5. Keep the two tracks separate, but not equally prioritized:
   - seed-side producer inventory is owned operationally by `PLAN_89`
   - seed-side theorem search is owned by `PLAN_87`
   - larger-domain localized search remains owned here, but only after (4)
6. Treat fixed-point critical-value transfer and renormalizable-point `V`-bound
   control (`RV`) as external dependencies owned by existing plans:
   - `PLAN_80`
   - `PLAN_78`
   - `PLAN_53`
   This plan may coordinate with those carriers, but does not itself own their
   proof search.
7. Do not count an upstream breakthrough as downstream completion unless it is
   paired with:
   - fixed-point critical-value transfer, and
   - renormalizable-point `V`-bound control (`RV`)
   through the already exposed cutovers.
8. While the seed-side inventory remains open, do not treat abstract
   localized-side wrapper search as co-equal progress.
9. If the seed-side inventory closes and no concrete localized producer class
   survives the plausibility screen, record the exact obstruction and hand off
   to model redesign.
10. If one track collapses to an already-known equivalence class, keep the
   other eligible track active rather than declaring the overall program
   stalled.
11. If both tracks collapse, record the exact obstruction and hand off to model
   redesign.

Dependencies: `Molecule/Conjecture.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_86_localized_or_reseeded_R_replacement.md`,
`plan/PLAN_87_non_circular_critical_seed_source.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`

Stuck Rule: STUCK only if both of the following are established:
- every seed-side candidate collapses to the singleton/canonical equivalence
  class, and
- no concrete larger-domain producer class outside the closed refined-chart
  scaffold survives the initial plausibility screen.

Last Updated: 2026-03-11

## Critical Revision

- PLAN_87 isolated the exact seed target correctly.
- But as a full research program it was too narrow, because a second theorem
  shape remains structurally available:
  `MoleculeResidualNonSingletonLocalizedBridgeSources`.
- The newer obstruction results change the operational picture:
  the only larger-domain producer class currently encoded in the repository is
  the refined-chart family, and it is now closed.
- By contrast, the seed side now has a concrete producer-family inventory,
  even though the first explicit family is `h_norm`-backed.
- So the master program must distinguish logical possibility from current
  plausibility:
  seed inventory is the active route; localized-side work becomes active only
  when attached to a named producer class with a reason it might avoid the
  refined-chart/global-`R` collapse.
- This plan also needed another correction:
  an upstream breakthrough is not the same as a full route replacement.
  The downstream interface still requires critical-value transfer and `RV`.
- And another correction:
  a “larger-domain” package is not meaningful if it secretly bakes in
  renormalizability or is recovered from the seed/singleton equivalence class.
- And another correction:
  this plan should not pretend to own the sidecar carrier proofs already owned
  by `PLAN_80`, `PLAN_78`, and `PLAN_53`.

## Research Program

- [ ] Keep both exact theorem targets explicit:
  - seed-side: `MoleculeResidualCriticalRenormalizableFixedSeedSource`
  - localized-side: `MoleculeResidualNonSingletonLocalizedBridgeSources`
- [x] Treat `PLAN_89` as the primary operational route:
  close the repository's explicit seed-side producer inventory before spending
  equal effort on more speculative branches.
- [ ] Treat `PLAN_90` as the active redesign follow-on now that the explicit
  seed-side inventory is closed and the current chart/operator scaffold is the
  next exact bottleneck.
- [ ] For every candidate, first prove it escapes the current singleton /
  canonical equivalence class.
- [ ] For every localized-side candidate, first name the concrete producer
  class, then prove it is non-circular in the stronger sense:
  the domain/bridge package is not defined from a seed route, does not smuggle
  in renormalizability, and has a plausible escape from the refined-chart /
  global-`R` collapse.
- [ ] Do not count abstract localized wrapper search with no new producer class
  as progress.
- [ ] Treat critical-value transfer + `RV` as external readiness gates from
  `PLAN_80` / `PLAN_78` / `PLAN_53`, not as local proof obligations of this
  plan.
- [ ] If a seed-side candidate lands, record the exact downstream gate:
  re-enter fixed-data/local-witness through the existing cutovers once the
  sidecar carriers are available.
- [ ] If a localized-side candidate lands, record the exact downstream gate:
  re-enter existence/canonical/fixed-data/local-witness through the existing
  cutovers once the sidecar carriers are available.
- [ ] If the seed inventory closes and no concrete localized producer class
  survives the plausibility screen, write the exact obstruction and escalate
  to a model-redesign plan rather than continuing wrapper search.

## Priority Order

1. Close `PLAN_89` inventory and carry the obstruction into `PLAN_90`
2. Clean theorem route for any surviving seed-side family
3. Localized-side activation only after naming a new producer class outside the
   closed refined-chart scaffold
4. Non-equivalence and strong non-circularity screening for any such
   localized-side candidate
5. Coordinate exact downstream gate with `PLAN_80` / `PLAN_78` / `PLAN_53`
6. Obstruction certificate if seed inventory closes and no plausible localized
   producer class remains

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Seed-side operational track | `PLAN_89` has now closed the explicit in-repo inventory: no surviving non-`h_norm` producer class remains under the current scaffold. | [######----] 60% |
| Localized-side reserve track | The only encoded larger-domain producer class is the refined-chart family, and it is now closed; no alternative producer class is currently named in the repository. | [##--------] 20% |
| Plausibility screening | Current evidence now separates theorem-shape viability from operational priority: current theorem search is exhausted, and further progress needs model redesign rather than more wrapper search. | [########--] 80% |
| Non-equivalence screening | Singleton localized / singleton seed / canonical seed collapse already recorded, and the current refined-chart localized producer class is now shown to collapse to singleton or blocked global `R`. | [########--] 80% |
| Strong non-circularity screening | The current refined-chart localized producer class is now ruled out as a genuine larger-domain route, and the current `slice_operator` is too trivial to realize genuine operator-side dynamics even after chart refinement. | [#######---] 70% |
| Downstream cutover readiness | Already complete structurally via PLAN_86. | [##########] 100% |
| External sidecar dependency gate | Exact downstream interface is known and now partially realized by common-midend cutovers from both upstream tracks into the stronger critical-seed contract and the canonical fixed-data/local-witness gate. | [########--] 80% |
| Redesign handoff | Exact redesign seam is now sharper: the legacy `slice_chart` blocks separated chart directions, and the current `slice_operator` blocks separated operator action even if the chart changes. Active follow-on is now `PLAN_90`. | [#######---] 70% |

## Notes

- Exact seed-side target:
  `MoleculeResidualCriticalRenormalizableFixedSeedSource`
- Exact localized-side target:
  `MoleculeResidualNonSingletonLocalizedBridgeSources`
- Operational priority revision:
  `PLAN_89` is now DONE as the inventory/handoff plan.
  The active concrete follow-on is
  `PLAN_90_separated_operator_action_redesign.md`;
  localized-side work remains reserve-only until a new producer class is named
  outside the closed refined-chart family.
- Exact downstream interface after either upstream breakthrough:
  - replacement existence,
  - fixed-point critical-value transfer,
  - renormalizable-point `V`-bound control (`RV`)
- Ownership correction:
  this plan owns the upstream replacement search only.
  The sidecar carriers remain owned by `PLAN_80`, `PLAN_78`, and `PLAN_53`.
- New checkpoint:
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer`
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer`
  - added
    `molecule_residual_fixed_point_data_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound`
    and
    `molecule_residual_fixed_point_local_witness_on_sources_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound`
  - targeted probes show all four new theorems are ground-axiom-only
  - this means the two PLAN_88 upstream tracks now share one exact common
    midpoint once critical-value transfer is available, and the seed-side
    canonical gate into fixed-data/local-witness is fully explicit
- New checkpoint:
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_standard_siegel_fixed_point`
  - targeted probe shows it is ground-axiom-only
  - this exposes a concrete seed-side producer family already present in the
    repository, but it does not count as a live upstream hit for PLAN_88
    because it explicitly factors through `h_norm`
- New checkpoint:
  - added
    `molecule_residual_non_singleton_localized_bridge_sources_of_refined_invariant_fixed_point_domain_sources_and_bridge_on_and_nontrivial`
  - targeted probe shows it is ground-axiom-only
  - this makes the refined-side localized search exact:
    the remaining larger-domain producer must supply
    refined invariant domain data +
    localized bridge-on on that domain +
    a genuine nontrivial second point
- New checkpoint:
  - added
    `molecule_residual_non_singleton_localized_bridge_sources_of_fixed_point_exists_refined_domain_and_bridge_on_and_nontrivial`
    and
    `molecule_residual_fixed_point_existence_source_of_fixed_point_exists_refined_domain_and_bridge_on_and_nontrivial`
  - targeted probes show both are ground-axiom-only
  - this makes the current localized-side candidate exact:
    the present `fixed_point_exists`-based refined-domain route needs
    only two additional hypotheses to become a genuine larger-domain
    breakthrough:
    localized bridge-on on its chosen domain, and nontriviality of that domain
- New checkpoint:
  - added
    `molecule_residual_refined_invariant_fixed_point_domain_sources_shape`
    and
    `no_fixed_point_exists_refined_domain_bridge_on_and_nontrivial`
  - targeted probes show both are ground-axiom-only
  - this closes the current `fixed_point_exists`-based refined-domain
    candidate: its chosen domain is always either the singleton `{f_ref}` or
    `univ`; nontriviality rules out the singleton branch, and the `univ`
    branch collapses localized bridge-on to the already-false global `R`
- New checkpoint:
  - added
    `no_refined_invariant_fixed_point_domain_sources_bridge_on_and_nontrivial`
  - targeted probe shows it is ground-axiom-only
  - this closes the whole current refined-chart localized producer class:
    any refined invariant fixed-point domain source built with
    `slice_chart_refined`, together with bridge-on and nontriviality, would
    still collapse to the already-false global `R`
- The current refined singleton localized route cannot supply the larger-domain
  target:
  `no_nontrivial_member_of_refined_invariant_fixed_seed_singleton_domain_sources`
- Redesign checkpoint:
  - added
    `MoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith`,
    `MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith`,
    and
    `MoleculeResidualSeparatedSliceChartSourceWith`
  - added
    `molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_of_renormalizable_fixed_seed_source`
    and
    `molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_iff_renormalizable_fixed_seed_source`
  - result:
    the paper-guided operator-route shape is not itself the problem; the
    legacy `slice_chart` is. But merely swapping in a nonconstant refined
    chart still does not produce a new upstream class, because the refined
    separated operator package is available exactly when a seed already exists.
- Redesign checkpoint:
  - added
    `MoleculeResidualSeparatedOperatorActionSourceWith`
    and
    `MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith`
  - added
    `no_molecule_residual_separated_operator_action_source_with_current_operator`
    and
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_current_operator`
  - result:
    chart separation alone is now certified insufficient.
    Even with an arbitrary chart choice, the current `slice_operator` cannot
    realize genuine operator-side dynamics, so the active redesign frontier
    now includes the operator scaffold itself.
- Critical revision:
  a candidate larger-domain package is still invalid if it only repackages a
  seed theorem or encodes renormalizability directly in the domain.
- Therefore the next honest progress now runs through:
  - `PLAN_90_separated_operator_action_redesign.md`
    for a genuinely nontrivial chart/operator scaffold
- And only after that, or alongside naming a specific new producer class,
  localized-side work can count by:
  - producing a genuinely non-singleton live localized domain coming from a
    different producer class than the now-closed refined-chart route.
