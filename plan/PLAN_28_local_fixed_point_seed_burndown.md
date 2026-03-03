# PLAN 28 - Local Fixed-Point Seed Burndown

Status: DONE
Progress: [##########] 100%
Scope: Eliminate the decomposed local fixed-point seed assumptions by replacing them with a narrower stable local interface.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists any `Molecule.molecule_local_fixed_point*` symbol.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FeigenbaumFixedPointAssumptions.lean`
Stuck Rule: STUCK if the current model cannot provide any fixed-point witness without reintroducing an equal-or-stronger global axiom.
Last Updated: 2026-03-02

## Work Log

- [x] Identify local fixed-point seed assumptions as a distinct blocker family.
- [x] Refactor five decomposed seed assumptions into one narrow interface:
  `MoleculeLocalFixedPointSeed` + `molecule_local_fixed_seed`.
- [x] Keep theorem-level projections (`molecule_local_fixed_point*`) for compatibility.
- [x] Re-run `lake build` and `check_axioms`; verify removal of
  `Molecule.molecule_local_fixed_point*` symbols.

## Current Audit Snapshot

- Removed from top theorem dependency path:
  - `Molecule.molecule_local_fixed_point`
  - `Molecule.molecule_local_fixed_point_is_fixed`
  - `Molecule.molecule_local_fixed_point_is_renorm`
  - `Molecule.molecule_local_fixed_point_critical_value`
  - `Molecule.molecule_local_fixed_point_domain_bound`
- New unified local blocker:
  - `Molecule.molecule_local_fixed_seed`
