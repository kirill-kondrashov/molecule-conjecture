# PLAN 91 - Nonvacuous Scaffold Remaining Theorems

Status: ACTIVE
Progress: [#########-] 93%
Scope: theorem backlog after the `PLAN_90` obstruction inventory. The current
repo has already proved that the existing refined scaffold is too weak:
`slice_chart_refined` has only one nonbase direction, `slice_domain = univ`
does not count as a proper localized domain, and the current discrete `BMol`
topology makes several local regularity targets vacuous while blocking genuine
local variation. This plan isolates the remaining theorem families needed to
either produce a nonvacuous replacement scaffold or prove the exact next
model-redesign obstruction.

Parent plan: `plan/PLAN_90_separated_operator_action_redesign.md`

Last Updated: 2026-03-14

## Current Boundary

Already proved in `Molecule/Conjecture.lean`:

- `no_molecule_residual_distinct_nonbase_chart_directions_source_with_refined_chart`
- `no_molecule_residual_distinct_nonbase_operator_directions_source_with_refined_chart`
- `no_molecule_residual_proper_localized_chart_domain_source_current_slice_domain`
- `molecule_residual_locally_injective_chart_source_with_of_current_BMol_topology`
- `molecule_residual_continuous_chart_source_with_of_current_BMol_topology`
- `MoleculeResidualContinuousChartSourceWithOn`
- `molecule_residual_continuous_chart_source_with_on_of_current_BMol_topology`
- `molecule_residual_continuous_chart_source_with_on_zero_observation_chart_of_bmol_zero_topology`
- `not_molecule_residual_continuous_chart_source_with_on_slice_chart_multivalued_of_bmol_zero_topology`
- `molecule_residual_continuous_chart_source_with_on_slice_chart_finite_observation_of_bmol_finite_topology`
- `molecule_residual_locally_constant_chart_source_with_of_current_BMol_topology`
- `no_molecule_residual_locally_nonconstant_chart_source_with_of_current_BMol_topology`
- `molecule_residual_proper_localized_chart_domain_source_with_slice_domain_localized`
- `molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_multivalued`
- `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_multivalued_and_slice_operator_multivalued`
- `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued`
- `molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_finite_observation`
- `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_finite_observation_and_slice_operator_multivalued`
- `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation`
- `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_multivalued`
- `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation`
- `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation`
- `MoleculeResidualNontrivialOperatorLinearizationSourceWith`
- `no_molecule_residual_nontrivial_operator_linearization_source_with_refined_operator`
- `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_multivalued_and_slice_operator_multivalued`
- `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_multivalued`
- `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation`
- `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation`
- `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one`
- `eq_shifted_of_deriv_ne_one_slice_operator_multivalued`
- `eq_shifted_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_multivalued`
- `eq_shifted_observation_of_deriv_ne_one_slice_operator_finite_observation`
- `eq_shifted_observation_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_finite_observation`
- `eq_one_of_deriv_ne_one_slice_operator_zero_observation`
- `eq_one_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_zero_observation`
- `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed`
- `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one`
- `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed`
- `not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed`
- `not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed`

Already proved in `Molecule/BanachSlice.lean`:

- `slice_domain_localized`
- `slice_domain_localized_open`
- `mem_slice_domain_localized_self`
- `exists_not_mem_slice_domain_localized`
- `slice_chart_refined_open_localized`
- `slice_chart_multivalued`
- `slice_chart_multivalued_open`
- `slice_chart_multivalued_self`
- `slice_chart_multivalued_default_eq_one_of_ne`
- `slice_chart_multivalued_large_eq_two_of_ne`
- `slice_chart_finite_observation`
- `continuous_slice_chart_finite_observation_of_bmol_finite_topology`
- `slice_chart_finite_observation_self`
- `slice_chart_finite_observation_default_shifted`
- `slice_chart_finite_observation_large_shifted`
- `slice_chart_finite_observation_default_eq_one_of_zero_eq_one_and_tag_zero`
- `slice_chart_finite_observation_large_eq_two_of_zero_eq_one_and_tag_zero`
- `slice_chart_finite_observation_shifted_eq_neg_one_of_zero_eq_one_and_tag_one`
- `slice_chart_finite_observation_large_eq_one_of_zero_eq_one_and_tag_one`
- `slice_chart_finite_observation_default_eq_one_of_eq_shifted_observation`
- `slice_chart_finite_observation_large_eq_two_of_eq_shifted_observation`
- `slice_operator_multivalued`
- `slice_operator_finite_observation`
- `slice_operator_zero_observation`
- `slice_operator_multivalued_zero_shifted`
- `slice_operator_multivalued_one_shifted`
- `slice_operator_multivalued_two_shifted`
- `slice_operator_multivalued_separates_one_two_shifted`
- `slice_operator_multivalued_maps_three_point_shifted`
- `slice_operator_multivalued_differentiableAt_shifted`
- `deriv_slice_operator_multivalued_shifted`
- `slice_operator_multivalued_eq_id_of_ne_shifted`
- `slice_operator_multivalued_differentiableAt_of_ne_shifted`
- `deriv_slice_operator_multivalued_of_ne_shifted`
- `slice_operator_finite_observation_eq_shifted_of_eq_shifted_observation`
- `slice_operator_finite_observation_eq_id_of_ne_shifted_observation`
- `slice_operator_finite_observation_zero_of_eq_shifted_observation`
- `slice_operator_finite_observation_one_of_eq_shifted_observation`
- `slice_operator_finite_observation_two_of_eq_shifted_observation`
- `slice_operator_finite_observation_separates_one_two_of_eq_shifted_observation`
- `slice_operator_finite_observation_maps_three_point_of_eq_shifted_observation`
- `slice_operator_finite_observation_differentiableAt_of_eq_shifted_observation`
- `deriv_slice_operator_finite_observation_of_eq_shifted_observation`
- `slice_operator_finite_observation_differentiableAt_of_ne_shifted_observation`
- `deriv_slice_operator_finite_observation_of_ne_shifted_observation`
- `slice_operator_zero_observation_eq_active_of_zero_eq_one`
- `slice_operator_zero_observation_eq_id_of_zero_ne_one`
- `slice_operator_zero_observation_maps_three_point_of_zero_eq_one`
- `slice_operator_zero_observation_maps_five_point_of_zero_eq_one`
- `deriv_slice_operator_zero_observation_of_zero_eq_one`
- `deriv_slice_operator_zero_observation_of_zero_ne_one`

Already proved in `Molecule/BMol.lean`:

- `bmol_zero_observation`
- `bmol_large_source_tag_observation`
- `bmol_finite_observation`
- `bmol_zero_topology`
- `bmol_finite_topology`
- `continuous_bmol_zero_observation`
- `continuous_bmol_finite_observation`
- `continuous_bmol_zero_observation_of_bmol_finite_topology`
- `continuous_bmol_large_source_tag_observation_of_bmol_finite_topology`
- `exists_open_separating_default_and_shifted_of_bmol_zero_topology`
- `not_isOpen_singleton_default_of_bmol_zero_topology`
- `not_discrete_bmol_zero_topology`

Therefore the remaining theorems cannot be more theorems about the current
toy scaffold unless they isolate a strictly smaller exact model obstruction.
The next productive theorem must either:

1. witness a genuinely stronger scaffold in `Molecule/BanachSlice.lean`, or
2. prove that the current default `BMol` topology blocks exactly the next stronger
   scaffold target too.

The new `bmol_zero_topology` candidate changes the interpretation of (2):
the repo now has a first theorem-backed non-discrete `BMol` topology candidate,
so the next model-side result should decide whether the active scaffold can be
ported to a named non-discrete topology, not just restate failures of the
default discrete instance.

First migrated-family result:
the continuity family has now been ported to an explicit `BMol` topology.
This shows a real boundary rather than another vacuous obstruction:
continuity survives for the zero-observation chart under `bmol_zero_topology`,
but it fails for the current multivalued chart. So the next migration work
should focus on chart/topology compatibility, not just existence of a
non-discrete topology candidate.

Second migrated-family result:
the repo now has a topology-compatible replacement chart, not just a topology
obstruction. `bmol_finite_topology` strengthens the observable data to
`(f 0, 1_{(5 / 2) ∈ U})`, and `slice_chart_finite_observation` factors through
that finite observation rather than through literal `BMol` equality tests.
This chart is continuous under the named non-discrete topology, still realizes
two distinct nonbase directions at `shiftedBMol`, and already reuses the
existing compact `{0, 1, 2}` scaffold package with `slice_operator_multivalued`.
So the next model-side question is no longer whether a nontrivial chart can be
made topology-compatible at all; it is whether the remaining local/analytic
and base-search steps can be migrated onto such a chart.

Third migrated-family result:
the local/analytic obligation now migrates too. The finite-observation chart
supports the same nontrivial operator-linearization theorem with
`slice_operator_multivalued`, so the stronger scaffold is not just continuous
under a named non-discrete topology; it also carries the current derivative
`-1` checkpoint. But the new exact obstruction is now visible as well:
every nontrivial-derivative witness for `slice_operator_multivalued` is forced
to the hard-coded `shiftedBMol` branch, because away from that reference point
the operator is just the identity with derivative `1`. So the next live
redesign target is no longer the chart. It is an operator whose nontrivial
local dynamics are not pinned to the explicit shifted base.

Fourth migrated-family result:
the operator-side dependence is now weakened from literal base equality to an
observation class. `slice_operator_finite_observation` uses the same
`2 - z` branch on every reference map with the shifted finite observation, and
the finite-observation scaffold plus fixed-to-seed upgrade are now already
packaged for that whole class. The route is therefore no longer pinned to the
named point `shiftedBMol` itself. The remaining gap is sharper: produce a
non-explicit-polynomial base in that shifted observation class, or enlarge the
observation-class operator so its nontrivial branch reaches a broader
non-explicit family.

Fifth migrated-family result:
that operator broadening is now implemented. The nontrivial branch no longer
needs the full shifted finite observation `(1, 0)`; it now applies to the
larger zero-observation class `f_ref.f 0 = 1`. The finite-observation chart
still supplies a compact scaffold package on that whole class, with the
invariant set chosen by the source-domain tag (`{0,1,2}` in the tag-`0`
branch, `{-1,0,1,2,3}` in the tag-`1` branch). The fixed-to-seed seam is
already wired for that broader class too, and any fixed base there is again
forced outside the explicit-polynomial family. So the next live search is now
strictly broader: find a non-explicit-polynomial base with `f(0)=1`, or
broaden the operator further if even that class proves too narrow.

## Acceptance

1. Produce a theorem-backed replacement scaffold with:
   - nontrivial `f_star` dependence,
   - a proper localized chart domain,
   - at least two nonbase chart directions or a clearly stated weaker target,
   - genuinely different operator action on realized chart directions.
2. If the current `BMol` model blocks that, prove the exact blocking theorem
   instead of adding more descriptive notes.
3. Keep theorem names aligned with the existing `PLAN_90` naming style so they
   can be promoted into the route plan without renaming churn.
4. A surviving scaffold must feed into the existing fixed/renorm upgrade path,
   not just exist as a disconnected witness.

## Theorem Queue

- [x] Domain witness family in `Molecule/BanachSlice.lean` and
      `Molecule/Conjecture.lean`.
  Target shape:
  `molecule_residual_proper_localized_chart_domain_source_with_<new_domain>`
  Goal:
  prove the replacement domain satisfies
  `MoleculeResidualProperLocalizedChartDomainSource`.
  Completed with:
  `slice_domain_localized` and
  `molecule_residual_proper_localized_chart_domain_source_with_slice_domain_localized`.

- [x] Chart-separation witness family for a replacement chart.
  Target shape:
  `molecule_residual_distinct_nonbase_chart_directions_source_with_<new_chart>`
  Goal:
  prove the replacement chart satisfies
  `MoleculeResidualDistinctNonbaseChartDirectionsSourceWith`.
  Completed with:
  `slice_chart_multivalued` and
  `molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_multivalued`.

- [x] Operator-action witness family for a replacement chart/operator pair.
  Preferred target shape:
  `molecule_residual_distinct_nonbase_operator_directions_source_with_<new_chart>_<new_op>`
  Fallback target shape:
  `molecule_residual_separated_operator_action_source_with_<new_chart>_<new_op>`
  Goal:
  prove the operator does more than separate one hard-coded nonbase value.
  Completed with:
  `slice_operator_multivalued` and
  `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_multivalued_and_slice_operator_multivalued`.

- [x] Scaffold-package lift for the replacement pair.
  Target shape:
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_<new_chart>_<new_op>`
  Goal:
  produce
  `MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith`
  without using a seed source.
  Completed with:
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued`.

- [x] Nonvacuous local or analytic obligation theorem for the replacement
      scaffold.
  Positive target shape:
  `molecule_residual_<local_or_analytic_property>_with_<new_chart>_<new_op>`
  Obstruction fallback:
  `no_molecule_residual_<local_or_analytic_property>_with_<new_chart>_<new_op>_of_current_BMol_topology`
  Goal:
  decide whether the replacement scaffold can satisfy at least one local or
  analytic target that is not made trivial by the current model.
  Completed with:
  `MoleculeResidualNontrivialOperatorLinearizationSourceWith`,
  `no_molecule_residual_nontrivial_operator_linearization_source_with_refined_operator`,
  and
  `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_multivalued_and_slice_operator_multivalued`.

- [x] Topology-compatible replacement-chart family under a named non-discrete
      `BMol` topology.
  Target shape:
  `molecule_residual_continuous_chart_source_with_on_<new_chart>_of_<new_topology>`
  Goal:
  show the stronger replacement chart survives continuity after leaving the
  default discrete `BMol` instance.
  Completed with:
  `bmol_finite_topology`,
  `slice_chart_finite_observation`,
  `molecule_residual_continuous_chart_source_with_on_slice_chart_finite_observation_of_bmol_finite_topology`,
  `molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_finite_observation`,
  `molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_finite_observation_and_slice_operator_multivalued`,
  and
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_multivalued`.

- [x] Topology-compatible local/analytic obligation family for the replacement
      chart, together with the exact current operator anchor obstruction.
  Target shape:
  `molecule_residual_<local_or_analytic_property>_with_<new_chart>_<new_op>`
  Obstruction companion:
  `eq_<hard_coded_base>_of_<property>_with_<current_op>`
  Goal:
  port the nontrivial derivative checkpoint onto the topology-compatible chart
  and identify whether the current operator still hard-codes the only viable
  base.
  Completed with:
  `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_multivalued`,
  `eq_shifted_of_deriv_ne_one_slice_operator_multivalued`,
  and
  `eq_shifted_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_multivalued`.

- [x] Observation-class operator/scaffold family with fixed-to-seed upgrade
      seam.
  Target shape:
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_<new_chart>_<new_op>_of_<observation_class>`
  and
  `..._seed_sources_with_..._of_<observation_class>_of_fixed`
  Goal:
  weaken the operator dependence from a single named base to an observation
  class and thread that scaffold into the existing fixed/seed machinery.
  Completed with:
  `slice_operator_finite_observation`,
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation`,
  `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed`,
  and
  `not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed`.

- [x] Broader zero-observation operator/scaffold family with fixed-to-seed
      upgrade seam.
  Target shape:
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_<new_chart>_<broader_op>_of_<scalar_observation>`
  and
  `..._seed_sources_with_..._of_<scalar_observation>_of_fixed`
  Goal:
  widen the nontrivial branch from the shifted finite-observation class to a
  strictly larger scalar observation class while preserving the existing
  no-explicit-polynomial frontier.
  Completed with:
  `slice_operator_zero_observation`,
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one`,
  `molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one`,
  `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed`,
  and
  `not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed`.

- [ ] First non-explicit-polynomial base theorem family under the stronger
      scaffold.
  Target shape:
  `molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_<base>_<new_chart>_<new_op>`
  Goal:
  reuse the stronger scaffold on the first base outside the already-closed
  explicit-polynomial family.

- [ ] Fixedness/renormalizability gate theorem family for that first surviving
      base.
  Positive targets:
  `..._base_fixed`
  `..._seed_sources_with_of_fixed`
  Obstruction fallback:
  `no_..._base_fixed`
  or
  `no_..._seed_sources_with_of_fixed`
  Goal:
  thread the surviving scaffold into the existing
  `molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm`
  route, or prove the exact next failure point.

- [ ] Critical-seed cutover theorem or exact handoff obstruction.
  Positive target shape:
  `molecule_residual_critical_renormalizable_fixed_seed_source_of_<surviving_package>`
  Obstruction fallback:
  `no_molecule_residual_critical_renormalizable_fixed_seed_source_of_<surviving_package>_of_current_model`
  Goal:
  either connect the new scaffold route back to the main seed target or record
  the exact theorem that forces a broader model redesign.

## Execution Order

1. Replace `slice_domain`.
2. Replace `slice_chart_refined`.
3. Replace `slice_operator_refined`.
4. Lift the triple to a scaffold package.
5. Test one nonvacuous local/analytic obligation.
6. Only then return to `BMol` base search.
7. Try the fixed/renorm upgrade.
8. Try the critical-seed cutover.

## Stuck Rule

STUCK if every candidate replacement in `Molecule/BanachSlice.lean` still:

- has a domain that is definitionally `univ`, or
- reduces all nonbase points to one chart value, or
- has operator action equivalent to the identity or a constant map, or
- only satisfies local/analytic obligations because of the discrete
  placeholder topology on `BMol`.

If STUCK, stop broadening the theorem inventory and switch to a dedicated
`BMol` model/topology redesign plan.
