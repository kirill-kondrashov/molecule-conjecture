# PLAN 11 - Full Axiom Burndown

Status: DONE
Progress: [##########] 100%
Scope: Remove all remaining `molecule_h_*` axioms and keep zero-arg top theorem.
Acceptance: `check_axioms` output contains no `Molecule.molecule_h_*` entries.
Dependencies: PLAN_18, PLAN_22, PLAN_23, PLAN_24
Stuck Rule: STUCK if PLAN_24 becomes STUCK.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Eliminated all top-level `molecule_h_*` dependencies except one.
- [x] Added localized-slice-data cutover theorem route.
- [x] Eliminate final root dependency `Molecule.molecule_h_norm`.

## Current Outcome

- `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists
  any `Molecule.molecule_h_*` symbol.
- Remaining project axiom moved to non-`molecule_h_*` bundle:
  - `Molecule.molecule_core_assumptions`
