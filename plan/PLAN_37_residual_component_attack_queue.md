# PLAN 37 - Residual Component Attack Queue

Status: DONE
Progress: [##########] 100%
Scope: Convert the irreducibility certificate into executable, component-focused implementation tracks that can shrink `MoleculeResidualAssumptions`.
Acceptance: At least one residual component is discharged constructively, or a track is closed with a precise impossibility statement tied to concrete model definitions.
Dependencies: `plan/PLAN_35_final_axiom_component_source_search.md`, `plan/PLAN_36_final_axiom_irreducibility_certificate.md`, `Molecule/Conjecture.lean`, `Molecule/HMol.lean`, `Molecule/Construction.lean`, `Molecule/Problem4_3.lean`
Stuck Rule: STUCK if no track can produce either a constructive witness or a formal impossibility statement.
Last Updated: 2026-03-03

## Work Log

- [x] Track A (compactness): closed via contract realignment + constructive witness
  (`isCompactOperator_of_constant` / `molecule_h_compact`).
- [x] Track B (association): discharged constructively via
  `rfast_hmol_candidate_combinatorially_associated`.
- [x] Track C (shift): discharged constructively via
  `rprm_combinatorial_model_has_shift_factor`.
- [x] Track D1 (analytic interface): discharged `gap` and `piecewise` constructively via local witness realignment.
- [x] Track D2 (analytic bounds): resolve via contract realignment and discharge in PLAN_41.
- [x] Feed successful track output back into PLAN_34 and remove `MoleculeResidualAssumptions` axiom.

## Current Audit Snapshot

- Upstream target:
  - cleared
- Immediate objective:
  - completed
