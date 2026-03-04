# PLAN 57 - Orbit Minimal Theorem Debt Extraction

Status: ACTIVE
Progress: [#########-] 91%
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
- [x] Add canonical `V`-bound seam and route landing/debt through
  `structure + V`-bound:
  - `MoleculeResidualCanonicalVBoundSource`
  - `molecule_residual_canonical_orbit_landing_source_of_structure_and_vbound_source`
  - `molecule_residual_canonical_orbit_at_debt_source_of_structure_and_vbound_source`
  - current theorem `molecule_residual_canonical_orbit_at_debt_source` now
    routes through this decomposition.
- [x] Split canonical `V`-bound debt into global and fixed-data projections:
  - `MoleculeResidualGlobalVBoundSource`
  - `molecule_residual_global_vbound_source_of_h_norm`
  - `molecule_residual_canonical_vbound_source_of_global_vbound_source`
  - current `molecule_residual_canonical_vbound_source` now routes through
    `molecule_residual_global_vbound_source`.
- [ ] Attack the remaining global `V`-bound source debt target constructively:
  - replace `molecule_residual_global_vbound_source` with a non-axiomatic
    source route.

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
  - landing and debt reconstruction seams from `structure + V`-bound are
    axiom-clean modulo ground axioms.
  - current theorems
    `molecule_residual_canonical_orbit_landing_source` and
    `molecule_residual_canonical_orbit_at_debt_source` now carry
    `Molecule.molecule_h_norm` only via
    `molecule_residual_canonical_vbound_source`.
  - `molecule_residual_canonical_vbound_source` now carries
    `Molecule.molecule_h_norm` only via
    `molecule_residual_global_vbound_source`.
