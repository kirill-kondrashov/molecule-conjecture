# PLAN 57 - Orbit Minimal Theorem Debt Extraction

Status: ACTIVE
Progress: [########--] 82%
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
- [x] Define the minimal debt theorem statement:
  - `MoleculeResidualCanonicalOrbitAtDebtSource`.
- [x] Add explicit constructor bridges between debt statement and
  `MoleculeResidualOrbitClauseAtFixedDataSource`:
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_canonical_debt_source`
  - `molecule_residual_canonical_orbit_at_debt_source_of_at_fixed_data_source`.
- [x] Probe axiom footprints for the debt-statement seam and constructor bridge.
- [x] Add explicit constructors from orbit-clause / transport sources into the
  debt statement:
  - `molecule_residual_canonical_orbit_at_debt_source_of_orbit_clause_source`
  - `molecule_residual_canonical_orbit_at_debt_source_of_transport_source`
  - current theorem `molecule_residual_canonical_orbit_at_debt_source`.
- [x] Decide next execution step: another micro-split, splitting canonical debt
  into landing + structure contracts and adding recomposition/projection seams.
- [x] Add structure-only projection and mixed constructors:
  - `molecule_residual_canonical_orbit_structure_source_of_at_fixed_data_source`
  - `molecule_residual_canonical_orbit_at_debt_source_of_landing_and_at_fixed_data_source`
  - `molecule_residual_canonical_orbit_structure_source_of_transport_source`
  - `molecule_residual_canonical_orbit_at_debt_source_of_landing_and_transport_source`.
- [ ] Attack the remaining landing-only debt target constructively:
  - prove `MoleculeResidualCanonicalOrbitLandingSource` from strictly weaker,
    non-`molecule_h_norm` ingredients (or replace the current source route).

## Notes

- This plan supersedes the active role of PLAN_56 (now archived as stuck).
- Goal is to force the blocker down to one theorem-sized target.
- Probe checkpoint:
  - debt bridge theorems above are axiom-clean modulo ground axioms.
  - constructors into the debt statement from orbit-clause/transport sources
    are axiom-clean modulo ground axioms.
  - landing/structure split and mixed constructor seams are axiom-clean modulo
    ground axioms.
  - current theorem `molecule_residual_canonical_orbit_at_debt_source` still
    carries `Molecule.molecule_h_norm`, and
    `molecule_residual_orbit_clause_at_fixed_data_source` inherits that.
  - current theorem `molecule_residual_canonical_orbit_landing_source` is now
    explicit and remains the residual `Molecule.molecule_h_norm` carrier.
