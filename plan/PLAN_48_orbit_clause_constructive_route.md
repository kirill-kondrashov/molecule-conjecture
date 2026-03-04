# PLAN 48 - Constructive Orbit-Clause Route

Status: ACTIVE
Progress: [#---------] 10%
Scope: Eliminate the `molecule_h_norm` dependency in `molecule_residual_orbit_clause_source` by replacing the current ex-falso body with a theorem-level constructive route.
Acceptance:
1. `#print axioms Molecule.molecule_residual_orbit_clause_source` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_orbit_transport_source` does not include `Molecule.molecule_h_norm`.
3. The axiom removal propagates to `molecule_residual_non_ground_sources` once Track A is complete.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`
Stuck Rule: STUCK if no non-circular theorem path can produce `MoleculeOrbitClause` without using bounds that themselves consume orbit clause.
Last Updated: 2026-03-04

## Work Plan

- [x] Isolate orbit clause as explicit source seam (`MoleculeResidualOrbitClauseSource`).
- [ ] Inventory candidate upstream theorem routes for `MoleculeOrbitClause` that are not ex-falso.
- [ ] Add a non-circular constructor theorem for `MoleculeResidualOrbitClauseSource` (if needed, with minimal source assumptions).
- [ ] Route `molecule_residual_orbit_transport_source` through the new constructor.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- Current theorem body:
  - `molecule_h_orbit` is still `False.elim molecule_h_norm_inconsistent`.
- This sub-plan is intentionally split from PLAN_47 so Track B can progress independently.
