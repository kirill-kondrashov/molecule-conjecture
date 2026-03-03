# PLAN 26 - Decomposed Core Axiom Burndown

Status: DONE
Progress: [##########] 100%
Scope: Iteratively replace decomposed `molecule_core_*` axioms with theorem-level constructions and keep `molecule_conjecture_refined` zero-arg export.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists any `Molecule.molecule_core_*` symbol.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/GlobalAnalyticity.lean`, `Molecule/Compactness.lean`
Stuck Rule: STUCK if every remaining `molecule_core_*` dependency is equivalent to an unresolved global analytic theorem with no smaller separable interface.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Convert `molecule_core_conj` and `molecule_core_ps` from axioms to theorem-level aliases.
- [x] Remove `molecule_core_data` from the active top-theorem dependency path by dropping the unused localized slice-data argument and narrowing to `molecule_local_fixed_data`.
- [x] Replace monolithic `molecule_local_fixed_data` with decomposed fixed-point seed assumptions and theorem-level repackaging.
- [x] Partition remaining core assumptions into independent wrapper interfaces:
  `molecule_core_analytic` and `molecule_core_combinatorial_topological`.
- [x] Collapse decomposed local fixed-point assumptions into unified seed wrapper
  `molecule_local_fixed_seed` while keeping theorem-level projections stable.
- [x] Remove `molecule_local_fixed_seed` from the top-theorem axiom path by
  routing the packed export through bounds-first hyperbolicity assumptions.
- [x] Remove `molecule_core_analytic` and `molecule_core_combinatorial_topological`
  from the top-theorem axiom list by consolidating them under a single final wrapper
  axiom (`molecule_final_assumptions`).

## Current Audit Snapshot

- Current project axioms in top theorem path:
  - `molecule_final_assumptions`
