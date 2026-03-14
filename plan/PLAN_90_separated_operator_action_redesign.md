# PLAN 90 - Separated Operator Action Redesign

Status: ACTIVE
Progress: [#########-] 90%
Scope: Redesign follow-on after the `PLAN_89` inventory closure. The current
repository has now isolated two exact scaffold defects in the paper-guided
Banach-neighborhood operator route:

1. the legacy `slice_chart` is constant, so separated chart directions are
   impossible;
2. even after replacing it by `slice_chart_refined`, the current
   `slice_operator` is still constant, so no genuine operator-side dynamics can
   be realized on a separated chart direction.

This plan owns the next model-side source search: find or encode a concrete
chart/operator scaffold that can support a genuinely new Banach-neighborhood
producer class rather than repackaging an existing PLAN_84 seed.
Feasibility revision:
domain-only variants of the current literal `z^2` model are now closed, but
the earlier “base-map first” ordering is now too optimistic.
The current refined scaffold is still toy-level:
`slice_domain = univ`, `slice_chart_refined` is only a two-valued equality
code, `slice_operator_refined` is the identity, and `BMol` still carries the
current discrete placeholder topology.
So the next feasible search must first strengthen the scaffold/model enough to
make local Banach-neighborhood claims non-vacuous, or isolate that model debt
exactly. Searching for new base maps only counts once paired with that stronger
scaffold story.

Acceptance:
1. Name a concrete chart/operator source class yielding
   `MoleculeResidualSeparatedOperatorActionSourceWith chart op` without using:
   - `MoleculeResidualRenormalizableFixedSeedSource`
   - `fixed_point_exists`
   - the current canonical/singleton equivalence class
   - `Molecule.molecule_h_norm`
2. Show that the candidate source is stronger than bare chart separation:
   it must realize genuinely different operator values on a separated chart
   direction.
3. Do not count as progress any scaffold change that still collapses
   definitionally to the PLAN_84 seed interface.
4. Require nontrivial dependence on `f_star`; an equality-coded two-point chart
   by itself no longer counts as a meaningful operator-side redesign.
5. Require a nontrivial chart domain or neighborhood notion; `slice_domain = univ`
   under the current discrete placeholder topology does not count by itself.
6. Require at least one non-vacuous local or analytic property that is not made
   trivial by constant maps, the identity map, or the current discrete
   topology.
7. Do not count further exclusion theorems unless they either directly unblock
   such a positive constructor or isolate the exact model/scaffold weakness
   forcing a redesign.
8. Either lift a surviving source into a concrete Banach-neighborhood operator
   package candidate, or record a smaller exact model obstruction theorem.
9. If a genuine operator package survives, record the downstream gate back into
   `MoleculeResidualCriticalRenormalizableFixedSeedSource`.

Dependencies: `Molecule/BanachSlice.lean`,
`Molecule/Conjecture.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_88_dual_track_seed_or_non_singleton_localized_bridge.md`,
`plan/PLAN_89_non_h_norm_seed_producer_inventory.md`,
`refs/1703.01206v3.pdf`

Stuck Rule: STUCK if every candidate chart/operator scaffold either:
- still makes separated operator action impossible, or
- still collapses to the existing PLAN_84 seed interface, or
- only works through toy/vacuous features of the current model
  (`slice_domain = univ`, equality-coded chart values, identity operator,
  discrete placeholder topology on `BMol`).

Last Updated: 2026-03-13

Execution split:
the remaining theorem backlog after the current obstruction inventory is now
tracked in `plan/PLAN_91_nonvacuous_scaffold_remaining_theorems.md`. `PLAN_90`
remains the governing route plan; `PLAN_91` owns the concrete theorem queue
for the next scaffold-or-model decision.

## Research Program

- [x] Make the next operator-side minimal source interface explicit:
  `MoleculeResidualSeparatedOperatorActionSourceWith`.
- [x] Record that current `slice_operator` blocks that interface for every
  chart choice.
- [x] Search for one concrete chart/operator scaffold in `Molecule/BanachSlice.lean`
  that can realize separated operator action without presupposing an existing
  seed.
- [x] Prove that the current scaffold candidate is not merely a renamed PLAN_84
  seed package.
- [x] Lift any surviving scaffold into a genuine Banach-neighborhood operator
  package candidate.
- [x] Close the current literal `z^2` family as live search space for
  non-`defaultBMol` fixed-base candidates.
- [x] Encode one explicit non-`z^2` `BMol` base in `Molecule/BMol.lean`.
- [x] Re-test the existing refined chart/operator package on that new base
  before changing `Molecule/BanachSlice.lean` again.
- [x] Screen the explicit shifted-base package against the next
  fixedness/renormalizability gate.
- [ ] Replace the current toy refined scaffold by one with nontrivial
  `f_star`-dependence, a nontrivial chart domain, and at least one non-vacuous
  local/analytic obligation.
- [ ] Decide whether that strengthening can be done inside the current
  placeholder `BMol` topology, or whether the next exact debt is a
  model/topology redesign in `Molecule/BMol.lean`.
- [ ] Only after that, search beyond the current explicit polynomial family in
  `Molecule/BMol.lean`.
- [ ] Reuse the stronger scaffold on the first non-explicit-polynomial base
  rather than screening more bases against the current toy operator.
- [ ] Thread any surviving non-explicit-polynomial package to the existing
  critical-seed cutover.
- [ ] If all such packages still collapse, record the exact model-redesign
  obstruction and hand off again.

## Priority Order

1. Non-vacuous `Molecule/BanachSlice.lean` scaffold redesign
2. Decide whether `BMol` model/topology strengthening is required
3. Non-explicit-polynomial `BMol` constructor search under the stronger scaffold
4. Critical-seed cutover readiness for any surviving package
5. Exact model-redesign handoff if still blocked

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Obstruction inventory | The toy-scaffold failures are explicit, and the program now also records that the live search boundary is beyond the explicit-polynomial family. The chart-side toy weakness is now formalized exactly, the current `slice_domain = univ` placeholder is now formally disqualified as a proper localized chart domain, and the current model/topology debt now has four exact theorem-level consequences: local chart injectivity, chart continuity, and local chart constancy are automatic for every chart under the current discrete `BMol` topology, while genuine local variation on every neighborhood is impossible. | [##########] 100% |
| Minimal source interface | `MoleculeResidualSeparatedOperatorActionSourceWith` and the scaffold/seed interfaces are explicit, and the repo now has a replacement chart/operator pair that realizes distinct nonbase chart and operator directions together with a nontrivial operator linearization theorem. The remaining gap is no longer interface or local-analytic existence, but reuse of that stronger scaffold on the next base search. | [#########-] 90% |
| Toy-family screening | The literal `z^2` family, the shifted `z^2 + c` family, and in fact every explicit polynomial `BMol` base map are screened under the current scaffold. | [##########] 100% |
| Non-vacuous scaffold redesign | The repo now has a theorem-backed replacement domain, a multivalued chart with two distinct nonbase directions, a nonidentity reference-dependent operator, a compact scaffold package built from that pair, and a nontrivial operator-linearization theorem that excludes the constant and identity placeholders. The next live step is no longer redesign inside `BanachSlice.lean`, but reuse of this stronger scaffold on the first non-explicit-polynomial base. | [#########-] 90% |
| Model/topology adequacy | `BMol` still uses the current discrete placeholder topology as its default instance, and four exact consequences of that choice are formalized. But `BMol` now carries two named non-discrete topology candidates: `bmol_zero_topology`, induced by `f ↦ f 0`, and the stronger `bmol_finite_topology`, induced by `(f 0, 1_{(5 / 2) ∈ U})`. The boundary is now sharper than “continuity is no longer automatic”: `slice_chart_multivalued` still fails continuity under the weaker named topology, but the new observation-based `slice_chart_finite_observation` is continuous under `bmol_finite_topology` and still realizes the same nontrivial `{0, 1, 2}` shifted scaffold package. So the broader migration story is no longer blocked at the first chart step; the remaining gap is to move the later local/analytic and base-search obligations onto a topology-compatible scaffold. | [##########] 100% |
| Non-equivalence screening | The original default-based package is screened by the `defaultBMol` renormalizability obstruction, and the explicit `largeBMol`-based package is now screened all the way down to a false fixedness claim via impossible self-renormalization. | [##########] 100% |
| Downstream gate readiness | The generic fixed-to-seed upgrade machinery is in place, but it is only useful once a non-vacuous surviving package exists. | [########--] 80% |

## Notes

- `PLAN_89` is complete as an inventory/handoff plan:
  no surviving non-`h_norm` seed producer class was found in the current repo.
- New code checkpoint:
  - added
    `MoleculeResidualSeparatedOperatorActionSourceWith`
  - added
    `MoleculeResidualDistinctNonbaseChartDirectionsSourceWith`
  - added
    `MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith`
  - added
    `molecule_residual_separated_operator_action_source_with_of_dynamical_banach_neighborhood_operator_seed_sources_with`
  - added
    `no_molecule_residual_separated_operator_action_source_with_current_operator`
  - added
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_current_operator`
- New concrete-scaffold checkpoint:
  - added
    `largeBMol`
    and
    `largeBMol_ne_defaultBMol`
  - added
    `slice_operator_refined`
    and
    `slice_operator_refined_separates_zero_one`
  - added
    `molecule_residual_separated_operator_action_source_with_refined_chart_and_operator`
  - result:
    the repo now has a zero-argument separated-operator-action witness that
    does not pass through any seed source
- New non-vacuous chart obstruction checkpoint:
  - added
    `slice_chart_refined_self`,
    `slice_chart_refined_eq_one_of_ne`,
    and
    `slice_chart_refined_nonbase_eq_of_ne`
  - added
    `no_molecule_residual_distinct_nonbase_chart_directions_source_with_refined_chart`
    and
    `no_molecule_residual_distinct_nonbase_operator_directions_source_with_refined_chart`
  - result:
    the revised acceptance rule against equality-coded two-point charts is now
    backed by exact theorems.
    The current refined chart separates the base point from nonbase points, but
    all nonbase points still collapse to the same chart value, so the scaffold
    cannot realize two distinct nonbase directions.
    Consequently, no operator layered on top of `slice_chart_refined` can turn
    it into a richer operator-side source requiring two distinct nonbase
    directions either.
- New topology-side obstruction checkpoint:
  - added
    `MoleculeResidualLocallyInjectiveChartSourceWith`
    and
    `molecule_residual_locally_injective_chart_source_with_of_current_BMol_topology`
    and
    `MoleculeResidualContinuousChartSourceWith`
    and
    `molecule_residual_continuous_chart_source_with_of_current_BMol_topology`
    and
    `MoleculeResidualLocallyConstantChartSourceWith`
    and
    `molecule_residual_locally_constant_chart_source_with_of_current_BMol_topology`
    and
    `MoleculeResidualLocallyNonconstantChartSourceWith`
    and
    `no_molecule_residual_locally_nonconstant_chart_source_with_of_current_BMol_topology`
  - result:
    the current discrete placeholder topology on `BMol` now has four exact
    theorem-level weaknesses.
    Under the current discrete placeholder topology on `BMol`, every chart is
    automatically injective on the singleton open neighborhood of each point.
    Also, every chart is automatically continuous and locally constant. So
    none of local chart injectivity, continuity, or local constancy can count
    as meaningful progress in the current model.
    More sharply, any source target that demands a distinct nearby chart
    direction in every open neighborhood is outright impossible in the current
    model, because singleton neighborhoods leave no room for such variation.
- New named-topology checkpoint:
  - added in `Molecule/BMol.lean`
    `bmol_zero_observation`,
    `bmol_zero_topology`,
    `continuous_bmol_zero_observation`,
    `exists_open_separating_default_and_shifted_of_bmol_zero_topology`,
    `not_isOpen_singleton_default_of_bmol_zero_topology`,
    and
    `not_discrete_bmol_zero_topology`
  - result:
    `BMol` no longer only has the discrete placeholder topology in the
    repository. There is now a concrete non-discrete topology candidate on the
    same carrier, induced by the observable `f ↦ f 0`.
    This does not yet replace the default instance or repair the current local
    scaffold theorems, but it turns the topology redesign problem into a
    migration/usefulness question rather than a “no candidate exists” gap.
- First migrated-family checkpoint:
  - added in `Molecule/Conjecture.lean`
    `MoleculeResidualContinuousChartSourceWithOn`,
    `molecule_residual_continuous_chart_source_with_on_of_current_BMol_topology`,
    `molecule_residual_continuous_chart_source_with_on_zero_observation_chart_of_bmol_zero_topology`,
    and
    `not_molecule_residual_continuous_chart_source_with_on_slice_chart_multivalued_of_bmol_zero_topology`
  - result:
    the first topology family has now been ported off the default discrete
    instance.
    Under `bmol_zero_topology`, continuity is no longer automatic for every
    chart: it survives for the observation chart by construction, but it fails
    for `slice_chart_multivalued` because that chart separates `defaultBMol`
    from `largeBMol` even though the named topology does not.
- Topology-compatible replacement-chart checkpoint:
  - added in `Molecule/BMol.lean`
    `bmol_large_source_tag_observation`,
    `bmol_finite_observation`,
    `bmol_finite_topology`,
    `continuous_bmol_finite_observation`,
    `continuous_bmol_zero_observation_of_bmol_finite_topology`,
    and
    `continuous_bmol_large_source_tag_observation_of_bmol_finite_topology`
  - added in `Molecule/BanachSlice.lean`
    `slice_chart_finite_observation`,
    `continuous_slice_chart_finite_observation_of_bmol_finite_topology`,
    `slice_chart_finite_observation_self`,
    `slice_chart_finite_observation_default_shifted`,
    and
    `slice_chart_finite_observation_large_shifted`
  - added in `Molecule/Conjecture.lean`
    `molecule_residual_continuous_chart_source_with_on_slice_chart_finite_observation_of_bmol_finite_topology`,
    `molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_finite_observation`,
    `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_finite_observation_and_slice_operator_multivalued`,
    and
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_multivalued`
  - result:
    the repo now has a first replacement chart that is both topology-compatible
    and nonvacuous.
    It no longer depends on literal `BMol` equality tests for the chart, it is
    continuous under a named non-discrete topology, and it still supports the
    existing compact shifted `{0, 1, 2}` operator scaffold.
    So the active model-side frontier has moved past “can any nontrivial chart
    survive off the discrete instance?” to “can the remaining local/analytic
    and base-search obligations be rebuilt on top of such a chart?”
- Topology-compatible local/analytic checkpoint:
  - added in `Molecule/BanachSlice.lean`
    `slice_operator_multivalued_eq_id_of_ne_shifted`,
    `slice_operator_multivalued_differentiableAt_of_ne_shifted`,
    and
    `deriv_slice_operator_multivalued_of_ne_shifted`
  - added in `Molecule/Conjecture.lean`
    `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_multivalued`,
    `eq_shifted_of_deriv_ne_one_slice_operator_multivalued`,
    and
    `eq_shifted_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_multivalued`
  - result:
    the topology-compatible chart now carries the same nontrivial derivative
    checkpoint too, so the local/analytic migration is not blocked at the
    chart level.
    But the next exact redesign target is now sharper:
    for the current `slice_operator_multivalued`, every witness of derivative
    different from `1` is forced onto the hard-coded `shiftedBMol` branch.
    So the route is still feasible, but the remaining operator-side debt is no
    longer vague: to leave the explicit-polynomial dead zone, the next
    operator scaffold must realize nontrivial local dynamics away from that
    one named base.
- Observation-class operator checkpoint:
  - added in `Molecule/BanachSlice.lean`
    `slice_operator_finite_observation`
    and its shifted-observation-class action, invariance, and derivative
    lemmas
  - added in `Molecule/Conjecture.lean`
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation`,
    `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation`,
    `eq_shifted_observation_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_finite_observation`,
    `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed`,
    and
    `not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed`
  - result:
    the active scaffold is no longer tied to literal equality with the named
    base `shiftedBMol`.
    It now applies to every base in the shifted finite-observation class and
    already threads into the fixed-to-seed upgrade seam.
    So the next live search is sharper and still feasible:
    find a non-explicit-polynomial base in that observation class, or broaden
    the observation-class operator further so its nontrivial branch reaches a
    larger non-explicit family.
- Broader zero-observation operator checkpoint:
  - added in `Molecule/BanachSlice.lean`
    `slice_operator_zero_observation`
    and its zero-observation-class action, invariance, and derivative lemmas
  - added in `Molecule/Conjecture.lean`
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one`,
    `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one`,
    `eq_one_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_zero_observation`,
    `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed`,
    and
    `not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed`
  - result:
    the active route is now broader again:
    the nontrivial operator branch no longer needs the full shifted
    finite-observation class, only the scalar condition `f_ref.f 0 = 1`.
    The finite-observation chart still supports a compact scaffold package on
    that larger class, with the invariant set chosen by the source-domain tag.
    So the next live search is now: find a non-explicit-polynomial base with
    `f(0)=1`, or broaden the operator further if even that scalar class is too
    narrow.
- New chart-domain obstruction checkpoint:
  - added
    `MoleculeResidualProperLocalizedChartDomainSource`
    and
    `no_molecule_residual_proper_localized_chart_domain_source_of_eq_univ`
    and
    `no_molecule_residual_proper_localized_chart_domain_source_current_slice_domain`
  - result:
    the revised acceptance rule against counting `slice_domain = univ` as a
    meaningful localized domain is now backed by an exact theorem.
    Any chart-domain scaffold that is definitionally `univ` at every reference
    point is disqualified from the proper localized-domain target, and the
    current `slice_domain` fails for exactly that reason.
- New replacement-domain checkpoint:
  - added in `Molecule/BanachSlice.lean`
    `slice_domain_localized`,
    `slice_domain_localized_open`,
    `mem_slice_domain_localized_self`,
    `exists_not_mem_slice_domain_localized`,
    `slice_chart_refined_open_localized`
  - added in `Molecule/Conjecture.lean`
    `molecule_residual_proper_localized_chart_domain_source_with_slice_domain_localized`
  - result:
    the first theorem family in `PLAN_91` is now complete.
    The repo has a reference-dependent proper localized chart domain witness,
    so the remaining scaffold debt is no longer “find any proper domain at
    all”; it is specifically to replace the equality-coded chart and identity
    operator on top of that stronger domain.
- Homology-side note:
  - any homology extracted from the current slice scaffold is still only
    discrete `H_0` bookkeeping, because the active chart/operator images are
    finite or discrete in the current model
  - if a homology seam becomes useful, the first honest target is not the
    current Banach-slice toy scaffold but the global main-cardioid geometry in
    `Molecule/Mol.lean`
  - that reserve sidecar is now tracked separately in
    `plan/PLAN_92_main_cardioid_boundary_first_homology_seam.md`
- New multivalued scaffold checkpoint:
  - added in `Molecule/BanachSlice.lean`
    `slice_chart_multivalued`,
    `slice_chart_multivalued_open`,
    `slice_chart_multivalued_self`,
    `slice_chart_multivalued_default_eq_one_of_ne`,
    `slice_chart_multivalued_large_eq_two_of_ne`,
    `slice_operator_multivalued`,
    `slice_operator_multivalued_zero_shifted`,
    `slice_operator_multivalued_one_shifted`,
    `slice_operator_multivalued_two_shifted`,
    `slice_operator_multivalued_separates_one_two_shifted`,
    `slice_operator_multivalued_maps_three_point_shifted`
  - added in `Molecule/Conjecture.lean`
    `molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_multivalued`,
    `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_multivalued_and_slice_operator_multivalued`,
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued`
  - result:
    the next three `PLAN_91` theorem families are now complete.
    The replacement search is no longer stuck at the level of a proper domain:
    the repo now has a concrete multivalued chart/operator scaffold with two
    distinct nonbase directions and a compact invariant slice package. The
    next live question is whether this stronger scaffold can satisfy at least
    one nonvacuous local or analytic obligation in the current `BMol` model.
- New operator-linearization checkpoint:
  - added in `Molecule/BanachSlice.lean`
    `slice_operator_multivalued_differentiableAt_shifted`
    and
    `deriv_slice_operator_multivalued_shifted`
  - added in `Molecule/Conjecture.lean`
    `MoleculeResidualNontrivialOperatorLinearizationSourceWith`,
    `no_molecule_residual_nontrivial_operator_linearization_source_with_refined_operator`,
    `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_multivalued_and_slice_operator_multivalued`
  - result:
    the nonvacuous local/analytic obligation item in `PLAN_91` is now closed.
    The stronger multivalued scaffold has operator derivative `-1` at its
    reference chart value, so it satisfies an analytic target that the old
    constant and identity operators fail exactly.
    The next live step is now the first non-explicit-polynomial base reuse
    under this stronger scaffold.
- New package-lift checkpoint:
  - added
    `MoleculeResidualBanachNeighborhoodOperatorScaffoldSourcesWith`
    and
    `MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm`
  - result:
    the current refined chart/operator candidate is no longer only a bare
    separated-action witness; it is now lifted to a compact Banach-neighborhood
    scaffold package candidate, and the remaining gate back to the existing
    seed package is exactly fixedness plus renormalizability of the base map
- New non-equivalence checkpoint:
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_base_fixed`
  - added
    `no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_base_renorm`
    and
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_scaffold_and_fixed_renorm`
  - result:
    the current scaffold candidate is not merely a disguised PLAN_84 seed
    package. Its exact remaining upgrade debt collapses to renormalizability of
    `defaultBMol`, and that upgrade is false in the current model, now also
    explicitly at the fixed-and-renormalizable seed-upgrade interface.
- New distinct-base scaffold checkpoint:
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_ne_default`
  - result:
    the refined chart/operator search no longer has only the
    `defaultBMol`-anchored package candidate.
    There is now a second concrete scaffold package based at `largeBMol`, so
    future screening cannot just replay the old `defaultBMol`
    non-renormalizability contradiction.
- New large-base gate checkpoint:
  - added
    `isFastRenormalizable_of_fixed_of_ne_defaultBMol`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_renorm_of_fixed`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_large_base_refined_chart_and_operator_of_fixed`
  - result:
    the second scaffold candidate now has an exact upgrade gate.
    Because `Rfast` returns `defaultBMol` on non-renormalizable inputs, any
    non-`defaultBMol` fixed base is already fast-renormalizable.
    So the `largeBMol`-based package no longer carries an independent
    renormalizability debt: its remaining live upgrade question is fixedness.
- New self-renormalization reduction checkpoint:
  - added
    `self_renormalization_relation_of_fixed_of_ne_defaultBMol`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_self_renorm_of_fixed`
  - added
    `no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_fixed_of_no_self_renorm`
  - result:
    the fixedness question for the `largeBMol`-based package is now reduced to
    a smaller exact obligation.
    Any proof of fixedness would force a self-renormalization relation on
    `largeBMol`, and any future proof ruling out that self-renormalization
    relation will automatically rule out fixedness.
- New generic refined-scaffold reduction checkpoint:
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_renorm_of_fixed`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_self_renorm_of_fixed`
  - added
    `no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_no_self_renorm`
    and
    `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed`
  - added
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed_of_no_self_renorm`
  - result:
    the old large-base-only reduction is now generic.
    Any future non-`defaultBMol` refined-scaffold candidate built via `of_ne`
    now inherits the same exact route:
    fixedness forces renormalizability and self-renormalization, any
    no-self-renormalization proof kills fixedness, and any surviving fixed base
    upgrades directly to the seed package.
- New large-base obstruction checkpoint:
  - added
    `no_self_renormalization_relation_largeBMol`
  - added
    `no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_fixed`
  - result:
    the explicit `largeBMol`-based refined scaffold candidate is now screened.
    Its remaining fixedness gate is false, because fixedness would force an
    affine self-renormalization relation on `largeBMol`, and that relation is
    impossible by polynomial degree.
- New literal-`z^2` obstruction checkpoint:
  - added
    `no_self_renormalization_relation_of_eq_sq`
  - added
    `no_fixed_of_eq_sq_of_ne_defaultBMol`
  - result:
    the previous `largeBMol` obstruction is now generalized.
    Any non-`defaultBMol` `BMol` whose underlying map is literally `z ↦ z^2`
    is ruled out as a fixed base for the current totalized `Rfast` model.
    So merely changing the source/target disks around the same quadratic
    polynomial can no longer count as live `PLAN_90` search.
- Feasibility-guided revision:
  the highest-value next step is now explicit:
  first search in `Molecule/BMol.lean` for one concrete non-`z^2` base map,
  then test the current refined chart/operator package on it.
  Another `Molecule/BanachSlice.lean` redesign should only happen if that
  base-map search stalls.
- New shifted-base checkpoint:
  - added
    `isProperMap_quad`
    and
    `isProperMap_quad_add_const`
  - added
    `shiftedBMol`,
    `shiftedBMol_ne_defaultBMol`,
    and
    `shiftedBMol_f_ne_sq`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator`
  - added
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator_base_ne_default`
    and
    `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator_base_f_ne_sq`
  - result:
    the feasibility-prioritized next move is no longer just a plan item.
    The repo now has a first explicit refined-scaffold candidate whose base is
    neither `defaultBMol` nor literally `z ↦ z^2`.
    That candidate has now been screened too, so the next live `PLAN_90`
    question is beyond the current explicit quadratic-polynomial family.
- New explicit-polynomial obstruction checkpoint:
  - added
    `eval_quad_add_const_iterate`
    and
    `natDegree_quad_add_const_iterate`
  - added
    `no_self_renormalization_relation_of_eq_sq_add_const`
    and
    `no_fixed_of_eq_sq_add_const_of_ne_defaultBMol`
  - added
    `no_self_renormalization_relation_shiftedBMol`
    and
    `no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator_base_fixed`
  - added
    `eval_polynomial_iterate`,
    `natDegree_polynomial_iterate`,
    `no_self_renormalization_relation_of_eq_eval_polynomial_natDegree_gt_one`,
    `one_lt_natDegree_of_eq_eval_polynomial`,
    `no_self_renormalization_relation_of_eq_eval_polynomial`,
    `no_fixed_and_renorm_of_eq_eval_polynomial`,
    `not_exists_eq_eval_polynomial_of_fixed_and_renorm`,
    `no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_eq_eval_polynomial`,
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed_of_eq_eval_polynomial`,
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_eq_eval_polynomial`,
    `not_exists_eq_eval_polynomial_of_refined_chart_and_operator_of_ne_fixed_and_renorm`,
    `not_exists_eq_eval_polynomial_of_refined_chart_and_operator_seed_sources_with_of_ne_of_fixed`,
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_large_base_refined_chart_and_operator_of_fixed`,
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_shifted_base_refined_chart_and_operator_of_fixed`,
    and
    `no_fixed_of_eq_eval_polynomial_of_ne_defaultBMol`
  - result:
    the degree obstruction is no longer limited to the literal `z^2` branch.
    It first extended to the explicit family `z ↦ z^2 + c`, then to explicit
    polynomial maps of degree `> 1`, and now to every explicit polynomial
    `BMol` point:
    low-degree polynomial models are impossible by the `BMol` critical-point
    axioms, while higher-degree models fail by iterate degree growth.
    The full fixed-and-renormalizable gate is now closed already at the bare
    `BMol` level by `no_fixed_and_renorm_of_eq_eval_polynomial`.
    Equivalently, `not_exists_eq_eval_polynomial_of_fixed_and_renorm` says any
    surviving fixed-and-renormalizable point must already lie outside the
    explicit-polynomial family, and
    `not_exists_eq_eval_polynomial_of_refined_chart_and_operator_of_ne_fixed_and_renorm`
    lifts that frontier statement to the generic refined-scaffold constructor.
    `not_exists_eq_eval_polynomial_of_refined_chart_and_operator_seed_sources_with_of_ne_of_fixed`
    then records the same frontier directly on the actual seed package produced
    by the generic `of_ne` fixed-upgrade constructor.
    That screen is then lifted to the generic refined-scaffold constructor too,
    so the current shifted-base scaffold is not fixed by `Rfast`, and any
    future explicit polynomial refined-scaffold candidate will fail for the
    same reason.
    The fixedness-based seed-upgrade interface is now closed for every
    non-`defaultBMol` explicit-polynomial branch, and the full
    fixed-and-renormalizable upgrade interface is now closed for the whole
    explicit-polynomial `of_ne` family, including the named default/large/
    shifted refined-scaffold candidates.
- Exact current obstruction:
  changing only the chart is not enough.
  The current `slice_operator` is constant, so even a separated chart cannot
  support genuine operator-side dynamics.
- Remaining debt:
  the broader literal-`z^2` model family is now screened,
  and the first explicit non-`z^2` candidate is screened too:
  the default-based candidate fails on renormalizability of `defaultBMol`,
  and every non-`defaultBMol` literal-`z^2` candidate fails on fixedness via
  the impossible self-renormalization relation.
  The shifted-base scaffold also fails on fixedness, and the same degree
  obstruction now covers every explicit polynomial `BMol` point.
  Any future fixed-and-renormalizable `of_ne` refined-scaffold candidate must
  therefore come from a base with no explicit polynomial representation.
  So the remaining live search is now narrower:
  either widen the non-`z^2` base-map search beyond the current explicit
  polynomial family, or redesign the chart/operator scaffold again
  around a genuinely different base.
  If a surviving package appears, the critical-seed cutover is already
  explicit.
- Operational consequence:
  the next honest work should still avoid new domain variants of the same
  `z^2` model.
  And it should no longer start by screening `shiftedBMol`: that step is
  complete too.
  It should either widen `Molecule/BMol.lean` beyond the current explicit
  polynomial family, or redesign `Molecule/BanachSlice.lean`.
