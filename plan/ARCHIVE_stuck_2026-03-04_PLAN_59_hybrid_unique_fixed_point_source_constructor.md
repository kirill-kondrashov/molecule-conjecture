# PLAN 59 - Hybrid Unique Fixed-Point Source Constructor

Status: STUCK (ARCHIVED)
Progress: [##########] 100%
Scope: Replace the remaining uniqueness bottleneck by constructing a non-`molecule_h_norm` source for hybrid-level uniqueness, then derive map-level fixed-point uniqueness and route downstream orbit-debt composition through that source.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source` does not include `Molecule.molecule_h_norm` through uniqueness.
3. The uniqueness source route is non-circular with respect to `molecule_residual_non_ground_sources`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/HyperbolicityTheorems.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_58_fixed_point_uniqueness_source_constructive_route.md`
Stuck Rule: STUCK if every constructor candidate for `MoleculeResidualHybridUniqueFixedPointSource` still requires either `molecule_h_norm`/`False.elim` or an equivalent uniqueness assumption.
Last Updated: 2026-03-04

## Work Plan

- [x] Open successor track from PLAN_58 with an explicit hybrid-level target seam.
- [x] Add source seam and projection theorems:
  - `MoleculeResidualHybridUniqueFixedPointSource`
  - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_unique_fixed_point_source`
  - `molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source`.
- [x] Add downstream transport + fixed-data integration seam:
  - `molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_hybrid_unique_fixed_point_source`.
- [x] Run `make build`, `make check`, and targeted `#print axioms` probes for the new seams.
- [x] Add canonical/refined bridge constructors into the hybrid-unique source:
  - `molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_uniqueness_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_of_refined_and_uniqueness_source`
  - current theorem:
    `molecule_residual_hybrid_unique_fixed_point_source`.
- [x] Add explicit current-route wrappers through the hybrid-unique source seam:
  - `molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_uniqueness_source`
  - `molecule_residual_fixed_point_uniqueness_source_via_hybrid_unique_fixed_point_source`
  - `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_hybrid_unique_fixed_point_source`
  - `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source_via_hybrid_unique_fixed_point_source`.
- [x] Add hybrid-class-collapse bridge constructors into the hybrid-unique source:
  - `molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_of_refined_and_hybrid_class_collapse_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_hybrid_class_collapse_source`.
- [ ] Construct a non-`molecule_h_norm` theorem for `MoleculeResidualHybridUniqueFixedPointSource`.
- [x] Rewire current uniqueness source (`molecule_residual_fixed_point_uniqueness_source`) to the hybrid-unique source route, preserving a direct legacy theorem as `molecule_residual_fixed_point_uniqueness_source_direct`.
- [x] Rewire the public orbit-debt wrapper theorem name
  (`molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source`)
  through the hybrid-routed public uniqueness theorem, preserving a direct
  legacy theorem as
  `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source_direct`.
- [x] Re-run fixed-point/orbit/top-level axiom probes and update tracker.

## Notes

- PLAN_58 is archived as stuck; it isolated and rewired the route but could not
  produce a constructive source theorem.
- Current new seams are axiom-clean modulo ground axioms.
- Canonical/refined bridge constructors into the hybrid-unique source are
  axiom-clean modulo ground axioms; current theorem
  `molecule_residual_hybrid_unique_fixed_point_source` still carries
  `Molecule.molecule_h_norm`.
- Current public uniqueness theorem
  `molecule_residual_fixed_point_uniqueness_source` now routes through
  `molecule_residual_hybrid_unique_fixed_point_source`; the former direct route
  is retained as `molecule_residual_fixed_point_uniqueness_source_direct`.
- Current public orbit-debt wrapper theorem name
  `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source`
  now routes through the public hybrid-unique uniqueness theorem; the former
  direct route is retained as
  `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source_direct`.
- The current-route wrappers above compile and probe as expected; they still
  carry `Molecule.molecule_h_norm` through the current hybrid-unique source
  theorem.
- The remaining blocker is now concentrated at construction of:
  `MoleculeResidualHybridUniqueFixedPointSource` (currently inherited via
  `molecule_residual_fixed_point_hybrid_class_collapse_source_direct`).
- Final stuck check added on 2026-03-04:
  - `molecule_residual_fixed_point_hybrid_class_collapse_source_iff_uniqueness_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_canonical`
  - `molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_bounds`
  These certify the current route is equivalence-bound, satisfying the plan's
  stuck rule.
