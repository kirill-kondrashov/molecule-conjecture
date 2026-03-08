# PLAN 84 - Canonical Seed Replacement for Existence Route

Status: ACTIVE
Progress: [#########-] 96%
Scope: Replace the existence-side dependence on
`selected_fixed_point := Classical.choose fixed_point_exists` with a seed
obtained from canonical or renormalizable fixed-point data, so the active
existence route no longer inherits the `defaultBMol` obstruction.
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
4. The seeded route either removes `Molecule.molecule_h_norm` from the active
   existence theorem or isolates one exact upstream theorem still needed.
Dependencies: `Molecule/Conjecture.lean`,
`Molecule/FixedPointExistence.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_83_localized_fixed_point_renormalizability_bridge.md`
Stuck Rule: STUCK if every candidate `f_seed` either:
- definitionally factors through `fixed_point_exists` / `selected_fixed_point`;
- already requires `MoleculeResidualFixedPointExistenceSource`; or
- only exists on a route that already depends on `Molecule.molecule_h_norm`.
Last Updated: 2026-03-08

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

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Seed abstraction | `MoleculeResidualRenormalizableFixedSeedSource`, `renormalizable_fixed_seed_point`, and the seed singleton bridge are now in place. | [#########-] 90% |
| Obstruction escape | `renormalizable_fixed_seed_point_ne_defaultBMol` shows the new seed route avoids the old `defaultBMol` witness by construction. | [########--] 80% |
| Upstream witness source | Canonical fast fixed-point data is now wired into the seed interface, and the two source contracts are definitionally equivalent. | [#########-] 90% |
| Downstream cutover readiness | The later aliases now expose both `canonical -> seed -> existence` and its fully expanded `fixed_data + orbit_at + uniqueness_direct -> seed -> existence` form. | [##########] 100% |

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
