# PLAN 56 - Orbit Clause Constructor Decomposition

Status: ACTIVE
Progress: [#######---] 70%
Scope: Replace the stuck PLAN_55 search with a decomposition-first route that
isolates the minimal missing theorem needed to construct
`MoleculeResidualOrbitClauseForFixedDataSource` without `molecule_h_norm`.
Acceptance:
1. The target is decomposed into explicit constructor seam theorem(s) with clear
   input contracts and no circular dependence on the target theorem itself.
2. At least one candidate constructor seam theorem is implemented and probed.
3. If still blocked, the blocker is narrowed to one minimal missing theorem
   statement (not a broad route failure).
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationOrbit.lean`, `Molecule/RenormalizationPullback.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/PLAN_54_orbit_source_contract_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_55_orbit_constructive_source_extraction_v2.md`
Stuck Rule: STUCK if every decomposition candidate still requires either the
full orbit-clause assumption as input or `False.elim`/global-normalization
assumptions.
Last Updated: 2026-03-04

## Work Plan

- [x] Start from PLAN_54 canonicalized topology:
  `molecule_residual_orbit_clause_for_fixed_data_source` is the single
  orbit-side frontier theorem on active path.
- [x] Record PLAN_55 blocker: post-PLAN_54 inventory found no exported
  non-circular constructor in current orbit modules.
- [x] Implement a first decomposition seam theorem that factors
  `MoleculeResidualOrbitClauseForFixedDataSource` through a strictly smaller
  contract than the current global orbit clause:
  - `MoleculeResidualOrbitClauseAtFixedDataSource`
  - `molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source`
  (drops the unused `h_domain` payload from the local constructor route).
- [x] Probe the new decomposition seam theorem(s) with `#print axioms`.
- [x] Add second decomposition layer from orbit-clause / transport sources into
  `MoleculeResidualOrbitClauseAtFixedDataSource`:
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_orbit_clause_source`
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_transport_source`
  - current theorem `molecule_residual_orbit_clause_at_fixed_data_source`.
- [ ] Decide go/no-go: continue constructive proof on this seam or open a
  further minimal sub-plan.

## Notes

- This plan supersedes the active role of PLAN_55 (now archived as stuck).
- Goal is to isolate one minimal theorem debt item, not to solve the full orbit
  constructive route in one step.
- Probe checkpoint:
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_local` is
    axiom-clean modulo ground axioms.
  - `molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source`
    is axiom-clean modulo ground axioms.
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_orbit_clause_source`
    and `..._of_transport_source` are axiom-clean modulo ground axioms.
  - Current theorem `molecule_residual_orbit_clause_at_fixed_data_source` still
    carries `Molecule.molecule_h_norm` via current transport/orbit source.
