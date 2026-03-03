# PLAN 29 - Core Axiom Interface Partition

Status: DONE
Progress: [##########] 100%
Scope: Split remaining `molecule_core_*` assumptions into two independent burndown tracks (analytic and combinatorial/topological) to avoid blocked all-or-nothing rewrites.
Acceptance: Remaining `molecule_core_*` assumptions are partitioned into independent wrappers with separate theorem entry points and measurable `check_axioms` deltas.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/PiecewiseAnalytic.lean`, `Molecule/Compactness.lean`, `Molecule/Construction.lean`
Stuck Rule: STUCK if partitioning cannot be done without changing the exported theorem statement.
Last Updated: 2026-03-02

## Work Log

- [x] Introduce an analytic wrapper for `molecule_core_orbit` and `molecule_core_gap`:
  `MoleculeAnalyticCore`.
- [x] Introduce a combinatorial/topological wrapper for
  `molecule_core_piecewise`, `molecule_core_shift`, `molecule_core_assoc`,
  `molecule_core_compact`: `MoleculeCombinatorialTopologicalCore`.
- [x] Add theorem-level bridge so each wrapper can be replaced independently:
  `molecule_hypothesis_pack_of_partitioned_core`.
- [x] Re-run `check_axioms` and verify per-wrapper dependency isolation.

## Current Audit Snapshot

- Isolated wrapper assumptions now visible in `check_axioms`:
  - `Molecule.molecule_core_analytic`
  - `Molecule.molecule_core_combinatorial_topological`
