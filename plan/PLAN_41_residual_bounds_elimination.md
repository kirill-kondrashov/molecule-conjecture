# PLAN 41 - Residual Bounds Elimination

Status: PROPOSED
Progress: [----------] 0%
Scope: Eliminate the final residual field (`bounds`) and remove `Molecule.molecule_residual_assumptions` entirely.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` lists no project-specific `Molecule.*` axiom symbol.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/Problem4_3_Lemmas.lean`, `Molecule/RenormalizationTheorem.lean`, `plan/PLAN_34_final_axiom_elimination.md`, `plan/PLAN_40_analytic_residual_triple_elimination.md`
Stuck Rule: STUCK if every route to produce `PseudoSiegelAPrioriBounds` requires introducing an equivalent new project axiom.
Last Updated: 2026-03-03

## Work Log

- [ ] Build a non-circular witness route for `PseudoSiegelAPrioriBounds` from existing theorem-level data.
- [ ] If that fails, formalize the obstruction as a precise impossibility statement tied to current model definitions.
- [ ] Decide and execute one route:
  - A) constructive witness from existing model objects and orbit-control lemmas, or
  - B) contract realignment of the bounds interface to the minimal theorem-consumed payload.
- [ ] Remove `molecule_residual_assumptions` axiom and replace with theorem-level `molecule_residual_bounds`.
- [ ] Re-run `lake build` and `check_axioms` to verify no project axiom remains.

## Current Audit Snapshot

- Remaining residual field:
  - `bounds`
- Remaining project axiom source:
  - `Molecule.molecule_residual_assumptions`
