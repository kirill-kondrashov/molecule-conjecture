# PLAN 27 - Local Fixed-Point Data Witness Construction

Status: DONE
Progress: [##########] 100%
Scope: Eliminate `Molecule.molecule_local_fixed_data` by constructing `FixedPointNormalizationData` from a smaller explicit local seed interface.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists `Molecule.molecule_local_fixed_data`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`
Stuck Rule: STUCK if no finite/nonempty invariant-slice witness can be built from current construction contracts without reintroducing a stronger global axiom.
Last Updated: 2026-03-02

## Work Log

- [x] Identify a minimal seed interface for fixed-point data requirements.
- [x] Replace the monolithic `molecule_local_fixed_data` axiom with decomposed local seed assumptions:
  `molecule_local_fixed_point`, `molecule_local_fixed_point_is_fixed`,
  `molecule_local_fixed_point_is_renorm`, `molecule_local_fixed_point_critical_value`,
  `molecule_local_fixed_point_domain_bound`.
- [x] Construct `molecule_local_fixed_data` theorem-level from the decomposed seeds.
- [x] Re-run `lake build` and `check_axioms`; confirm `Molecule.molecule_local_fixed_data` is removed.

## Current Audit Snapshot

- Removed from top theorem dependency path:
  - `Molecule.molecule_local_fixed_data`
- New residual seed assumptions in top theorem path:
  - `Molecule.molecule_local_fixed_point`
  - `Molecule.molecule_local_fixed_point_is_fixed`
  - `Molecule.molecule_local_fixed_point_is_renorm`
  - `Molecule.molecule_local_fixed_point_critical_value`
  - `Molecule.molecule_local_fixed_point_domain_bound`
