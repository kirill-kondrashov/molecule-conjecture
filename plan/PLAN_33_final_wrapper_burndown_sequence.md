# PLAN 33 - Final Wrapper Burndown Sequence

Status: DONE
Progress: [##########] 100%
Scope: Sequence elimination of the last two wrapper assumptions (`molecule_core_analytic`, `molecule_core_combinatorial_topological`) without regressing the zero-argument export theorem.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists either wrapper assumption.
Dependencies: `Molecule/Conjecture.lean`, `plan/PLAN_30_analytic_core_wrapper_burndown.md`, `plan/PLAN_31_combinatorial_core_wrapper_burndown.md`
Stuck Rule: STUCK if eliminating one wrapper necessarily reintroduces an equivalent or stronger wrapper on the other side with no net reduction.
Last Updated: 2026-03-02

## Work Log

- [x] Execute PLAN_30 to completion (`molecule_core_analytic` removed).
- [x] Execute PLAN_31 to completion (`molecule_core_combinatorial_topological` removed).
- [x] Re-run `lake build` and `check_axioms`; confirm no project wrapper axioms remain in top theorem path.

## Current Audit Snapshot

- Removed from top theorem dependency path:
  - `Molecule.molecule_core_analytic`
  - `Molecule.molecule_core_combinatorial_topological`
