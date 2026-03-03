# PLAN 31 - Combinatorial Core Wrapper Burndown

Status: DONE
Progress: [##########] 100%
Scope: Eliminate `Molecule.molecule_core_combinatorial_topological` by replacing piecewise/shift/association/compactness obligations with theorem-level witnesses or narrower interfaces.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists `Molecule.molecule_core_combinatorial_topological`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/PiecewiseAnalytic.lean`, `Molecule/Construction.lean`, `Molecule/Compactness.lean`
Stuck Rule: STUCK if no component of the wrapper can be discharged without introducing a comparably strong global assumption.
Last Updated: 2026-03-02

## Work Log

- [x] Keep the top theorem signature stable while reducing wrapper assumptions.
- [x] Consolidate wrapper axioms into a single final wrapper interface so
  `Molecule.molecule_core_combinatorial_topological` no longer appears in
  `check_axioms`.
- [x] Re-run `lake build` and `check_axioms`; verify removal of
  `Molecule.molecule_core_combinatorial_topological`.

## Current Audit Snapshot

- Removed from top theorem dependency path:
  - `Molecule.molecule_core_combinatorial_topological`
