# PLAN 85 - Upstream Four-Carrier Burndown

Status: DONE
Progress: [##########] 100%
Scope: Attack the exact upstream frontier isolated by PLAN_84:
- fixed-point renormalizability,
- renormalizable-point `V`-bound control on the witness-side branch,
- local orbit-at,
- hybrid-class collapse.

The goal was not more route reshaping. The goal was to replace one or more of
these theorem carriers non-circularly, or prove that a branch is blocked and
needs model redesign.

Outcome:
- The direct global `R` route is formally blocked in the current scaffold.
- The active current downstream frontier has been reduced to:
  - existence/canonical: `R`
  - fixed-data/local-witness: `R + RV`
- The next active work is no longer this burndown. It is the redesign handoff
  in `PLAN_86`.

Acceptance:
1. The residual frontier is tracked explicitly as the four-carrier tuple:
   `R`, `RV`, `O`, `H`.
2. At least one carrier is either:
   - replaced by a non-`molecule_h_norm` theorem, or
   - bypassed on the active downstream route by a strictly smaller frontier, or
   - certified blocked with a precise obstruction theorem.
3. Any successful replacement is threaded into the active downstream routes:
   PLAN_80 fixed-data, PLAN_78 local witness, and PLAN_82 canonical witness.
4. If all four carriers remain blocked by the same model-level trap, the plan
   produces a precise redesign handoff rather than more wrapper reductions.

Dependencies: `Molecule/Conjecture.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_84_canonical_seed_replacement_for_existence_route.md`

Stuck Rule: STUCK if every candidate replacement for the four-carrier tuple
still factors through the same current global-normalization debt without
shrinking the frontier or yielding a new obstruction theorem.

Last Updated: 2026-03-09

## Research Program

- [x] Introduce one explicit theorem-level package for the residual tuple
  `(R, RV, O, H)` so downstream cutovers stop moving between equivalent
  wrappers.
- [x] Stabilize the shared witness-side pair `R + RV` as its own package and
  route fixed-data / local-witness through it.
- [ ] Attack the shared witness-side pair first:
  - `R`: renormalizability of fixed points
  - `RV`: renormalizable-point `V`-bound control
- [ ] Test whether `O` can be derived from a weaker local package once `R` and
  `RV` are available, instead of treating orbit-at as fully independent.
- [ ] Test whether `H` can be weakened from full direct uniqueness to the exact
  hybrid-class-collapse theorem already sufficient on the PLAN_84 branch.
- [ ] Thread any successful carrier replacement through:
  - PLAN_80 fixed-data route
  - PLAN_78 local-witness route
  - PLAN_82 canonical route
- [ ] If a carrier remains blocked, add an obstruction theorem instead of
  another decomposition layer.

## Priority Order

1. Shared witness-side pair:
   `R` and `RV`
2. Canonical-specific orbit side:
   `O`
3. Uniqueness/collapse side:
   `H`
4. Model redesign handoff if the same obstruction persists across 1-3

## Carrier Dictionary

```text
R := ∀ f : BMol, Rfast f = f -> IsFastRenormalizable f

RV := ∀ f : BMol, IsFastRenormalizable f -> criticalValue f = 0 ->
        f.V ⊆ Metric.ball 0 0.1

O := local orbit-at source
     MoleculeResidualOrbitClauseAtSource

H := hybrid-class-collapse source
     MoleculeResidualFixedPointHybridClassCollapseSource
```

## Ownership / Handoff

- `R`, `RV`:
  primary owners are PLAN_80 / PLAN_81 / PLAN_53
- `O`:
  primary owner is PLAN_82, with orbit-side support from PLAN_54 / PLAN_57
- `H`:
  primary owner is PLAN_53, with archived uniqueness/collapse plans as history

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Frontier stabilization | `MoleculeResidualUpstreamFourCarrierSources` now packages the exact frontier, and existence is routed through that package. | [##########] 100% |
| Shared witness-side attack | The current fixed-data and local-witness theorems are now routed through the smaller witness-side pair `R + RV`; the current canonical theorem has been cut one step further to `R` alone through current existence. A new obstruction theorem shows that literal global `R` is false in the current scaffold, so the direct current existence/canonical route is now formally blocked on `R`. | [##########] 100% |
| Orbit-side attack | `O` is no longer on the active current canonical route; it survives only on alternate seeded/package routes. | [##########] 100% |
| Collapse-side attack | `H` is no longer on the active current canonical route; it survives only on alternate seeded/package routes. | [##########] 100% |
| Redesign fallback | The redesign trigger is now forced on the current existence/canonical route: global `R` is formally false, so further progress must come from a localized/reseeded replacement of `R`, not from proving the direct global carrier. | [#####-----] 50% |

## Notes

- PLAN_84 is now DONE. It removed seed-specific debt and handed off the exact
  remaining upstream carriers.
- New checkpoint:
  - added `MoleculeResidualUpstreamFourCarrierSources`
  - added `molecule_residual_fixed_point_existence_source_of_upstream_four_carrier_sources`
  - added `molecule_residual_upstream_four_carrier_sources`
  - added `molecule_residual_fixed_point_existence_source_via_upstream_four_carrier_sources`
  - targeted probes show:
    `molecule_residual_fixed_point_existence_source_of_upstream_four_carrier_sources`
    is ground-axiom-only, while
    `molecule_residual_upstream_four_carrier_sources`
    and
    `molecule_residual_fixed_point_existence_source_via_upstream_four_carrier_sources`
    carry exactly the shared `Molecule.molecule_h_norm` debt of the four
    packaged carriers.
- Shared-pair checkpoint:
  - added `MoleculeResidualWitnessPairSources`
  - added `molecule_residual_fixed_point_data_source_of_witness_pair_sources`
  - added `molecule_residual_fixed_point_local_witness_on_sources_of_witness_pair_sources`
  - rerouted the current four-carrier package through the witness-pair package
  - this shows the active upstream frontier now splits cleanly as:
    `(R, RV)` shared witness-side pair + `O` orbit-side + `H` collapse-side
  - targeted probes show:
    `molecule_residual_fixed_point_data_source_of_witness_pair_sources`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_witness_pair_sources`,
    and
    `molecule_residual_upstream_four_carrier_sources_of_witness_pair_orbit_at_and_hybrid_class_collapse`
    are ground-axiom-only;
    `molecule_residual_witness_pair_sources` and
    `molecule_residual_fixed_point_data_source_via_witness_pair_sources`
    carry exactly the current witness-side `Molecule.molecule_h_norm` debt.
  - existence checkpoint:
    `molecule_residual_fixed_point_existence_source_of_witness_pair_orbit_at_and_hybrid_class_collapse_via_seed`
    reduces the seeded existence branch to:
    shared witness-side pair + orbit-at + collapse.
- Witness-pair shrink checkpoint:
  - added
    `fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound`
  - the PLAN_85 witness-side pair now uses
    `MoleculeResidualRenormVBoundSource`
    instead of fixed-point `V`-bound transfer
  - current pair package is now:
    `molecule_residual_fixed_point_renormalizable_via_global_norm_direct` +
    `molecule_residual_renorm_vbound_source`
  - targeted probes show:
    `molecule_residual_fixed_point_data_source_of_witness_pair_sources`,
    `molecule_residual_fixed_point_local_witness_on_sources_of_witness_pair_sources`,
    and
    `molecule_residual_fixed_point_existence_source_of_witness_pair_orbit_at_and_hybrid_class_collapse_via_seed`
    are ground-axiom-only, while
    `molecule_residual_witness_pair_sources`,
    `molecule_residual_upstream_four_carrier_sources`,
    and
    `molecule_residual_fixed_point_existence_source_via_upstream_four_carrier_sources`
    still carry `Molecule.molecule_h_norm` exactly through the smaller
    witness-side pair + `O` + `H` frontier.
- Canonical-threading checkpoint:
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_upstream_four_carrier_sources`
  - added
    `molecule_residual_canonical_fast_fixed_point_data_source_of_witness_pair_orbit_at_and_hybrid_class_collapse`
  - added current canonical alias
    `molecule_residual_canonical_fast_fixed_point_data_source_via_upstream_four_carrier_sources`
  - targeted probes show the two parameterized canonical theorems are
    ground-axiom-only, while the current canonical alias carries exactly the
    reduced `(R, RV, O, H)` frontier and no extra canonical wrapper debt.
- Active-current-route shrink checkpoint:
  - rerouted current
    `molecule_residual_fixed_point_data_source`
    through
    `fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound`
  - rerouted current
    `molecule_residual_fixed_point_local_witness_on_sources`
    and
    `molecule_residual_fixed_point_local_witness_sources`
    through the same `R + RV` witness-side pair
  - rerouted current
    `molecule_residual_canonical_fast_fixed_point_data_source`
    through current fixed-data, so the active canonical branch no longer uses
    `O` or `H`
  - targeted probes show the current
    fixed-data, local-witness, and canonical theorems still carry
    `Molecule.molecule_h_norm`, but the exact remaining current carriers are
    now just:
    `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`
    and
    `molecule_residual_renorm_vbound_source`
- Canonical-direct-existence checkpoint:
  - rerouted current
    `molecule_residual_canonical_fast_fixed_point_data_source`
    through
    `molecule_residual_fixed_point_existence_source`
  - targeted probes show the current canonical theorem now has the same axiom
    footprint as the current existence theorem
  - this removes `RV`, `O`, and `H` from the active current canonical route;
    only `R` remains there
- `R` obstruction checkpoint:
  - added
    `no_molecule_residual_fixed_point_renormalizable_source`
  - added
    `molecule_residual_fixed_point_existence_source_of_fixed_point_renormalizable`
    to expose the current existence route exactly as:
    ground `fixed_point_exists` + `R`
  - targeted probes show both new theorems are ground-axiom-only
  - targeted probes also show the current
    `molecule_residual_fixed_point_existence_source`
    and
    `molecule_residual_canonical_fast_fixed_point_data_source`
    still carry `Molecule.molecule_h_norm`
  - conclusion:
    the direct global `R` route is formally blocked in the current scaffold,
    so any further elimination must replace global `R` by a localized/reseeded
    theorem, not prove `R` itself
- The key discipline for this plan is to avoid further equivalent route
  decompositions unless they strictly shrink the carrier tuple or add a new
  obstruction theorem.
- The most promising next move is now to redesign `R`, not to attack it
  directly:
  the direct global `R` theorem is false in the current scaffold.
  The live technical debt on the active current routes is:
  - existence/canonical: replace `R` by a localized or reseeded theorem
  - fixed-data/local-witness: replace `RV`, and then rebase them on the new
    existence route
- The least promising move is more seed-route or canonical-route reshaping;
  those branches are already saturated.
