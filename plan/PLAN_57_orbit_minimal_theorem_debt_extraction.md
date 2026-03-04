# PLAN 57 - Orbit Minimal Theorem Debt Extraction

Status: ACTIVE
Progress: [##--------] 20%
Scope: After PLAN_56 decomposition got stuck, isolate one minimal theorem debt
item whose proof would unlock a non-`molecule_h_norm` constructor for
`MoleculeResidualOrbitClauseForFixedDataSource`.
Acceptance:
1. The blocker is expressed as one explicit theorem statement (or equivalent
   tiny cluster) strictly below the current global orbit clause contract.
2. Existing seams route through that debt item with no circular dependency.
3. Axiom probes confirm all intermediate seam theorems remain ground-axiom-only
   modulo source inputs.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationOrbit.lean`, `Molecule/RenormalizationPullback.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/PLAN_54_orbit_source_contract_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_56_orbit_clause_constructor_decomposition.md`
Stuck Rule: STUCK if the candidate debt item is shown equivalent to the full
existing orbit-clause assumption in current infrastructure.
Last Updated: 2026-03-04

## Work Plan

- [x] Record PLAN_56 go/no-go result: decomposition seams exist but current
  constructors still require the residual orbit source carrying
  `Molecule.molecule_h_norm`.
- [ ] Define the minimal debt theorem statement (candidate: fixed-data canonical
  orbit-at constructor source that avoids global orbit-clause packaging).
- [ ] Add an explicit constructor theorem from the debt statement into
  `MoleculeResidualOrbitClauseAtFixedDataSource`.
- [ ] Probe axiom footprints for the debt-statement seam and constructor bridge.
- [ ] Decide next execution step: direct proof attempt vs another micro-split.

## Notes

- This plan supersedes the active role of PLAN_56 (now archived as stuck).
- Goal is to force the blocker down to one theorem-sized target.
