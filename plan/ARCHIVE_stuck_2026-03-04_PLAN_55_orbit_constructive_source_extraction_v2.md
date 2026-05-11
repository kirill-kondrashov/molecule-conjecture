# PLAN 55 - Orbit Constructive Source Extraction V2

Status: ACTIVE
Progress: [##--------] 20%
Scope: Build a constructive theorem-level route for
`molecule_residual_orbit_clause_for_fixed_data_source` after the PLAN_54
refactor consolidation, without introducing new project axioms.
Acceptance:
1. `#print axioms Molecule.molecule_residual_orbit_clause_for_fixed_data_source`
   does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_non_ground_sources`
   no longer includes `Molecule.molecule_h_norm` from the orbit side.
3. The replacement theorem is sourced from existing theorem infrastructure
   (no new axiom frontier).
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `Molecule/RenormalizationOrbit.lean`, `Molecule/RenormalizationPullback.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/PLAN_54_orbit_source_contract_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_51_orbit_fixed_data_source_replacement.md`
Stuck Rule: STUCK if all candidate routes still require either (a) assuming the target orbit clause itself, or (b) `False.elim`/global-normalization assumptions.
Last Updated: 2026-03-04

## Work Plan

- [x] Start from PLAN_54 canonicalized route where
  `molecule_residual_orbit_clause_for_fixed_data_source` is the single
  orbit-side frontier theorem on the active path.
- [ ] Inventory post-PLAN_54 candidate theorem routes that could yield
  `MoleculeResidualOrbitClauseForFixedDataSource` non-circularly.
- [ ] Add one explicit candidate constructor theorem (if extractable) and probe
  its axiom footprint.
- [ ] If no constructor is extractable, produce a formal blocker note in this
  plan and open the next minimal decomposition sub-plan.

## Notes

- This plan supersedes the *active* orbit effort after PLAN_54 reached DONE.
- It reopens the actual constructive objective (not only refactor/narrowing).
