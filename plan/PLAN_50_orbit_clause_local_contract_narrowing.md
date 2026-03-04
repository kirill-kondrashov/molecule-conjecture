# PLAN 50 - Orbit-Clause Local Contract Narrowing

Status: ACTIVE
Progress: [######----] 65%
Scope: Replace the stalled global orbit-clause elimination route with a local-obligation route by narrowing orbit-clause interfaces around the exact obligations consumed in the residual bounds pipeline.
Acceptance:
1. Local orbit-clause seam theorem(s) compile and are wired into Conjecture/Problem4_3 interfaces without regressions.
2. `#print axioms` on local seam constructors remains ground-axiom only.
3. A replacement target is isolated so `molecule_residual_orbit_clause_source` can be rebuilt without circular dependence on bounds.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `Molecule/RenormalizationOrbit.lean`, `Molecule/RenormalizationPullback.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`
Stuck Rule: STUCK if narrowing to local obligations still requires proving the same global `MoleculeOrbitClause` theorem as a prerequisite.
Last Updated: 2026-03-04

## Work Plan

- [x] Introduce local orbit obligation seam:
  - `MoleculeOrbitClauseAt`
  - `molecule_orbit_clause_at_of_orbit_clause`
- [x] Verify local orbit seam theorems are axiom-clean modulo ground axioms.
- [x] Thread local seam through residual-bounds-facing constructors where possible.
  - `molecule_h_orbit_at`
  - `MoleculeResidualOrbitClauseAtSource`
  - `molecule_residual_orbit_clause_source_of_local`
  - `molecule_residual_orbit_clause_source := ..._of_local ...`
- [x] Isolate minimal local source contract that is non-circular with bounds construction.
  - `MoleculeResidualOrbitClauseForFixedDataSource`
  - `molecule_residual_orbit_clause_for_fixed_data_source_of_local`
- [x] Route residual bounds assembly through the fixed-data local orbit-source path:
  - `molecule_residual_bounds_from_fixed_data_and_local_orbit_source`
  - `molecule_residual_bounds_seed_free_of_bounds_assembly_sources` now uses
    local-orbit conversion (`..._at_source_of_orbit_clause`).
- [ ] Rebuild `molecule_residual_orbit_clause_source` from the narrowed local contract path.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- This plan supersedes archived PLAN_48, which stalled at the global-contract level.
- Current code status:
  - local seam added in `Molecule/Conjecture.lean`;
  - local seam axiom profile is ground-only (`propext`, `Classical.choice`, `Quot.sound`);
  - local source constructor theorem (`molecule_residual_orbit_clause_source_of_local`)
    is ground-only, while the current local source witness
    (`molecule_residual_orbit_clause_at_source`) remains `molecule_h_norm`-backed;
  - local fixed-data orbit-source constructor theorem and local-orbit residual
    bounds constructor are ground-only;
  - top-level axiom frontier still includes `Molecule.molecule_h_norm`.
