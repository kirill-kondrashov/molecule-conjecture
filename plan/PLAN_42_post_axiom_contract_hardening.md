# PLAN 42 - Post-Axiom Contract Hardening

Status: ACTIVE
Progress: [#####-----] 50%
Scope: Recover mathematical strength after the axiom-elimination cutover by replacing placeholder contracts with nontrivial theorem-consumed payloads.
Acceptance: `molecule_conjecture_refined` remains axiom-free while `PseudoSiegelAPrioriBounds` and hyperbolicity predicates are strengthened beyond trivial witnesses.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Hyperbolicity.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `plan/PLAN_41_residual_bounds_elimination.md`
Stuck Rule: STUCK if strengthening any contract necessarily reintroduces a project axiom in `check_axioms`.
Last Updated: 2026-03-03

## Work Log

- [x] Replace `PseudoSiegelAPrioriBounds` placeholder payload with a nontrivial contract that still admits theorem-level construction.
- [x] Rewire bounds theorems to use `Problem4_3` constructive statement route (`..._of_fixed_point_data`) instead of `trivial`.
- [x] Route canonical fixed-point extraction through bounds payload (`canonical_fast_fixed_point_data_of_bounds`).
- [x] Tighten `IsHyperbolic1DUnstable` incrementally (require nonzero unstable multiplier witness) while preserving compatibility.
- [ ] Tighten `IsHyperbolic` interface incrementally and keep compatibility shims.
- [ ] Re-prove `molecule_conjecture_refined` via the strengthened path and re-run `check_axioms`.

## Current Audit Snapshot

- Axiom status:
  - `check_axioms` for `Molecule.molecule_conjecture_refined` still reports:
    - `Molecule.molecule_h_norm`
  - Current strengthened route is nontrivial at bounds-contract level, but the zero-arg
    bounds source still flows through `molecule_h_fixed_data -> molecule_h_data -> molecule_h_norm`.
- Main risk:
  - semantic weakening introduced by the cutover contracts.
  - circularity risk if canonical/bounds witnesses are rebuilt from legacy global assumptions.
