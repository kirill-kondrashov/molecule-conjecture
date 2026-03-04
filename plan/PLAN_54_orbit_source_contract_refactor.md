# PLAN 54 - Orbit Source Contract Refactor

Status: ACTIVE
Progress: [#########-] 95%
Scope: Replace the stuck direct constructive search (PLAN_51) with a refactor-first route that minimizes active dependence on legacy orbit transport wrappers and concentrates the orbit-side frontier at a single local source theorem.
Acceptance:
1. Legacy bounds/helper routes no longer depend on `MoleculeResidualOrbitTransportSource` when a local fixed-data orbit source is sufficient.
2. `molecule_residual_orbit_clause_for_fixed_data_source` remains the single orbit-side frontier theorem on the active top path.
3. `#print axioms` probes for the new orbit-source composition seam theorems are ground-axiom-only modulo source inputs.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/RenormalizationOrbit.lean`, `Molecule/RenormalizationPullback.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_51_orbit_fixed_data_source_replacement.md`
Stuck Rule: STUCK if the refactor still leaves more than one independent orbit-side non-ground source in the active top path, or if no further theorem-level narrowing can be achieved without introducing new axioms.
Last Updated: 2026-03-04

## Work Plan

- [x] Archive PLAN_51 as stuck after confirming no non-circular constructor is exported by current orbit modules.
- [x] Rewire legacy fixed-data residual-bounds theorem to use local fixed-data orbit source directly:
  - `molecule_residual_bounds_from_fixed_data` now uses
    `molecule_residual_bounds_from_fixed_data_and_local_orbit_source`.
- [x] Add explicit orbit-source composition seam theorem(s) for current route to improve probe granularity:
  - `molecule_residual_orbit_clause_for_fixed_data_source_of_orbit_clause_source`
  - `molecule_residual_orbit_clause_for_fixed_data_source_of_transport_source`
- [x] Run targeted `#print axioms` probes for the new orbit-source seam theorem(s).
- [x] Sync PLAN_47/tracker dependencies and progress after orbit refactor checkpoint.
- [x] Route additional legacy wrappers through the new orbit-source composition seams where ordering permits:
  - `molecule_residual_orbit_clause_for_fixed_data_source_via_transport`.
- [x] Decide and implement top-path cutover to the transport-routed wrapper:
  - `molecule_residual_non_ground_sources` now uses
    `molecule_residual_orbit_clause_for_fixed_data_source_via_transport`.
- [x] Reorder declarations so
  `molecule_residual_orbit_clause_for_fixed_data_source` itself now routes via
  the transport wrapper without forward-reference issues.
- [ ] Decide whether to keep both
  `molecule_residual_orbit_clause_for_fixed_data_source` and
  `molecule_residual_orbit_clause_for_fixed_data_source_via_transport`, or
  collapse to one canonical exported theorem name.

## Notes

- This plan supersedes PLAN_51.
- This is a narrowing/refactor track, not a full constructive proof of the orbit clause itself.
- Probe checkpoint:
  - `molecule_residual_bounds_from_fixed_data_localized` is ground-axiom-only.
  - `molecule_residual_bounds_from_fixed_data` now depends on
    `molecule_residual_orbit_clause_for_fixed_data_source` (no direct transport
    dependency), and therefore still carries `Molecule.molecule_h_norm`.
