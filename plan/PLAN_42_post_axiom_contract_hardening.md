# PLAN 42 - Post-Axiom Contract Hardening

Status: ACTIVE
Progress: [#######---] 70%
Scope: Recover mathematical strength after the axiom-elimination cutover by replacing placeholder contracts with nontrivial theorem-consumed payloads.
Acceptance: `molecule_conjecture_refined` remains axiom-free while `PseudoSiegelAPrioriBounds` and hyperbolicity predicates are strengthened beyond trivial witnesses.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Hyperbolicity.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `plan/PLAN_41_residual_bounds_elimination.md`
Stuck Rule: STUCK if strengthening any contract necessarily reintroduces a project axiom in `check_axioms`.
Last Updated: 2026-03-03

## Work Log

- [x] Replace `PseudoSiegelAPrioriBounds` placeholder payload with a nontrivial contract that still admits theorem-level construction.
- [x] Rewire bounds theorems to use `Problem4_3` constructive statement route (`..._of_fixed_point_data`) instead of `trivial`.
- [x] Route canonical fixed-point extraction through bounds payload (`canonical_fast_fixed_point_data_of_bounds`).
- [x] Replace `molecule_residual_bounds` source with a seed-free route that avoids `molecule_h_data`
  (`molecule_residual_bounds_seed_free` via `problem_4_3_bounds_established_conjecture`).
- [x] Tighten `IsHyperbolic1DUnstable` incrementally (require nonzero unstable multiplier witness) while preserving compatibility.
- [x] Tighten `IsHyperbolic` interface incrementally (require chart target to contain basepoint `φ g`) and patch compatibility constructors.
- [ ] Re-prove `molecule_conjecture_refined` via the strengthened path and re-run `check_axioms`.

## Current Audit Snapshot

- Axiom status:
  - `check_axioms` for `Molecule.molecule_conjecture_refined` still reports:
    - `Molecule.molecule_h_norm`
  - `molecule_residual_bounds` no longer flows through
    `molecule_h_fixed_data -> molecule_h_data`; it now uses a seed-free bounds theorem path.
  - Remaining dependence is still through legacy global assumptions (`molecule_h_exists`,
    `molecule_h_norm`, `molecule_h_ps`, `molecule_h_orbit`, `molecule_h_unique`).
- Main risk:
  - semantic weakening introduced by the cutover contracts.
  - circularity risk if canonical/bounds witnesses are rebuilt from legacy global assumptions.
