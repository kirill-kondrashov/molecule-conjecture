# PLAN 84 - Canonical Seed Replacement for Existence Route

Status: DONE
Progress: [##########] 100%
Scope: Replace the existence-side dependence on
`selected_fixed_point := Classical.choose fixed_point_exists` with a seed
obtained from canonical or renormalizable fixed-point data, and isolate the
exact remaining upstream frontier on that seeded branch. This plan does not own
proofs of the remaining upstream carriers.
Acceptance:
1. A theorem-level source yields a seed `f_seed : BMol` with
   `IsFastRenormalizable f_seed ∧ Rfast f_seed = f_seed` without mentioning
   `fixed_point_exists`, `selected_fixed_point`, or
   `MoleculeResidualFixedPointExistenceSource`.
2. The singleton-bridge / identification machinery currently used by PLAN_83 is
   rebuilt against `f_seed` rather than `selected_fixed_point`.
3. The old PLAN_83 obstruction
   `no_molecule_residual_fixed_point_existence_source_of_hybrid_class_fixed_point_exact_uniqueness`
   does not reappear by construction on the new seeded route.
4. The seeded route is expanded until the remaining non-ground debt is stated
   entirely in terms of upstream carriers that are not specific to seed
   replacement.
5. Further wrapper reductions on the seeded branch are shown not to shrink the
   axiom frontier, so the plan can be handed off as complete.
Dependencies: `Molecule/Conjecture.lean`,
`Molecule/FixedPointExistence.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_83_localized_fixed_point_renormalizability_bridge.md`
Completion Rule: DONE once the seeded branch no longer carries any residual
debt specific to `selected_fixed_point` or seed selection, and the remaining
frontier is expressed purely in upstream carriers.
Last Updated: 2026-03-09

## Work Plan

- [x] Inventory all current uses of `selected_fixed_point` and
  `Classical.choose fixed_point_exists` in the existence-side route.
- [x] Introduce a seed interface whose data is exactly
  `∃ f_seed, IsFastRenormalizable f_seed ∧ Rfast f_seed = f_seed`.
- [x] Identify one non-circular live source for that seed, with
  `CanonicalFastFixedPointData` the primary candidate.
- [x] Rebuild the minimal existence-side singleton bridge against the new seed.
- [x] Compare the new seed route against the PLAN_83 obstruction and certify
  that the `defaultBMol` contradiction is gone.
- [x] Thread the seeded route into the active existence theorem or state the
  exact remaining upstream dependency.
- [x] Prove that further wrapper lowering on this branch does not shrink the
  live non-ground frontier.
- [x] Hand off the residual carrier tuple to the upstream plans that own it.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Seed abstraction | `MoleculeResidualRenormalizableFixedSeedSource`, `renormalizable_fixed_seed_point`, and the seed singleton bridge are now in place. | [##########] 100% |
| Obstruction escape | `renormalizable_fixed_seed_point_ne_defaultBMol` shows the new seed route avoids the old `defaultBMol` witness by construction. | [##########] 100% |
| Upstream witness source | Canonical fast fixed-point data is wired into the seed interface, and the two source contracts are definitionally equivalent. | [##########] 100% |
| Downstream cutover readiness | The later aliases expose the seeded route all the way down to the residual upstream carrier tuple. | [##########] 100% |

## Notes

- PLAN_83 is now STUCK because its current target,
  `MoleculeResidualHybridClassFixedPointExactUniquenessSource`, implies
  `¬ MoleculeResidualFixedPointExistenceSource` in the current scaffold.
- The core reason is upstream: `fixed_point_exists` is currently proved by
  taking `defaultBMol`, a fixed but non-renormalizable map.
- So the next viable direction is not another uniqueness wrapper. It is to
  replace the seed of the existence-side route.
- `CanonicalFastFixedPointData` is the cleanest live candidate seed source:
  it already provides `∃ f, IsFastRenormalizable f ∧ Rfast f = f`.
- This plan is compatible with PLAN_82: if PLAN_82 can provide canonical fixed
  data without `Molecule.molecule_h_norm`, PLAN_84 should be able to reuse that
  witness directly instead of routing through `fixed_point_exists`.
- Critical revision:
  - The earlier `ACTIVE [#########-] 99%` framing was misleading.
  - `PLAN_84` no longer owns any live theorem debt. It has completed its
    seed-replacement job and is now a handoff plan.
  - The remaining non-ground frontier is upstream and non-seed-specific.
- New checkpoint:
  - `MoleculeResidualRenormalizableFixedSeedSource` is now an explicit
    interface, disjoint from `defaultBMol` by construction.
  - `molecule_residual_renormalizable_fixed_seed_source_iff_canonical_fast_fixed_point_data_source`
    shows the PLAN_84 seed route has no extra structural debt beyond the
    current canonical data source.
  - The remaining PLAN_84 question is purely upstream: can
    `MoleculeResidualCanonicalFastFixedPointDataSource` be produced without
    `Molecule.molecule_h_norm`?
  - Verified by targeted probes:
    `molecule_residual_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source`,
    `molecule_residual_renormalizable_fixed_seed_source_iff_canonical_fast_fixed_point_data_source`,
    and
    `molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source_via_seed`
    are ground-axiom-only, while the current
    `molecule_residual_fixed_point_existence_source` still carries
    `Molecule.molecule_h_norm`.
  - Declaration-order note:
    `molecule_residual_fixed_point_existence_source` is still defined earlier in
    the file via the legacy route, but
    `molecule_residual_fixed_point_existence_source_via_canonical_fast_fixed_point_data_source`
    now exposes the seeded canonical route as a concrete theorem.
  - Final structural checkpoint:
    `molecule_residual_fixed_point_existence_source_via_canonical_fast_fixed_point_data_source`,
    `molecule_residual_canonical_fast_fixed_point_data_source`, and the current
    `molecule_residual_fixed_point_existence_source` all have the same axiom
    frontier (`Molecule.molecule_h_norm` plus ground axioms). So PLAN_84 has no
    additional structural debt left to remove.
  - Final dependency checkpoint:
    `molecule_residual_fixed_point_existence_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed`
    is ground-axiom-only, and
    `molecule_residual_fixed_point_existence_source_via_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed`
    shows the seeded branch now depends exactly on the current fixed-data,
    local orbit-at, and direct uniqueness carriers.
  - Final frontier checkpoint:
    `molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed`
    is ground-axiom-only, and the fully expanded current alias now names the
    exact four residual inputs on this branch:
    renormalizability, `V`-bound transfer, local orbit-at, and direct
    uniqueness.
  - One wrapper less:
    `molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed`
    is also ground-axiom-only, so the seeded branch can be expressed with
    hybrid-class collapse instead of direct uniqueness.
  - Saturation note:
    the collapse-based current alias has the same axiom frontier as the
    uniqueness-based current alias, so this reduction improves naming but does
    not further shrink the live non-ground debt.
  - Probe confirmation:
    `molecule_residual_fixed_point_existence_source_via_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed`
    has exactly the same non-ground axiom frontier as those four current
    carriers, and nothing else.
  - Residual handoff frontier:
    - renormalizability of fixed points
    - `V`-bound transfer on fixed renormalizable maps
    - local orbit-at
    - hybrid-class collapse
  - Those debts are not specific to seed replacement and should now be attacked
    in the upstream plans that natively own them.
