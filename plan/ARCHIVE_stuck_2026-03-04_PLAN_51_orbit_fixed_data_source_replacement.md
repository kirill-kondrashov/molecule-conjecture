# PLAN 51 - Orbit Fixed-Data Source Replacement

Status: ACTIVE
Progress: [###-------] 30%
Scope: Replace `molecule_residual_orbit_clause_for_fixed_data_source` with a constructive theorem-level source so the remaining orbit-side dependency on `molecule_h_norm` is removed from the top-path non-ground source assembly.
Acceptance:
1. `#print axioms Molecule.molecule_residual_orbit_clause_for_fixed_data_source` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_non_ground_sources` does not include `Molecule.molecule_h_norm` from the orbit-side source.
3. `#print axioms Molecule.molecule_residual_bounds_seed_free` does not include `Molecule.molecule_h_norm` from the orbit-side source.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `Molecule/RenormalizationOrbit.lean`, `Molecule/RenormalizationPullback.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/ARCHIVE_superseded_2026-03-04_PLAN_50_orbit_clause_local_contract_narrowing.md`
Stuck Rule: STUCK if all available local-contract routes still require `False.elim`/global-normalization assumptions and no non-circular replacement theorem can be extracted.
Last Updated: 2026-03-04

## Work Plan

- [x] Isolate local orbit seam and fixed-data local source contracts:
  - `MoleculeOrbitClauseAt`
  - `MoleculeResidualOrbitClauseAtSource`
  - `MoleculeResidualOrbitClauseForFixedDataSource`
- [x] Rewire top-path residual bounds assembly to consume fixed-data local orbit source directly.
- [x] Identify constructive/non-circular theorem candidates that can produce
  `MoleculeResidualOrbitClauseForFixedDataSource`.
- [ ] Replace body of `molecule_residual_orbit_clause_for_fixed_data_source`
  with constructive proof route.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- This plan supersedes PLAN_50 because the top path no longer depends on
  `MoleculeResidualOrbitClauseSource` (global clause type); the relevant seam is
  now `MoleculeResidualOrbitClauseForFixedDataSource`.
- Inventory result (2026-03-04):
  - `RenormalizationOrbit` / `RenormalizationPullback` and
    `Problem4_3*` theorems consume orbit-clause premises but do not currently
    export a non-circular constructor for
    `MoleculeResidualOrbitClauseForFixedDataSource`.
