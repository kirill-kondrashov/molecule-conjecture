# PLAN 30 - Analytic Core Wrapper Burndown

Status: DONE
Progress: [##########] 100%
Scope: Eliminate `Molecule.molecule_core_analytic` by replacing its bounds/gap wrapper contents with theorem-level witnesses or narrower assumptions.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists `Molecule.molecule_core_analytic`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/HyperbolicityTheorems.lean`
Stuck Rule: STUCK if orbit-transport and gap assumptions cannot be separated further without restoring the pre-partition monolithic interface.
Last Updated: 2026-03-02

## Work Log

- [x] Refactor packed route to consume `h_bounds` directly (bounds-first path), removing dependency on local fixed-point seed in the top-theorem route.
- [x] Consolidate wrapper axioms into a single final wrapper interface so
  `Molecule.molecule_core_analytic` no longer appears in `check_axioms`.
- [x] Keep the zero-arg export theorem unchanged while swapping in reduced assumptions.
- [x] Re-run `lake build` and `check_axioms`; verify removal of `Molecule.molecule_core_analytic`.

## Current Audit Snapshot

- Removed from top theorem dependency path:
  - `Molecule.molecule_core_analytic`
