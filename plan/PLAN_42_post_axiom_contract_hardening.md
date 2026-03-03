# PLAN 42 - Post-Axiom Contract Hardening

Status: PROPOSED
Progress: [----------] 0%
Scope: Recover mathematical strength after the axiom-elimination cutover by replacing placeholder contracts with nontrivial theorem-consumed payloads.
Acceptance: `molecule_conjecture_refined` remains axiom-free while `PseudoSiegelAPrioriBounds` and hyperbolicity predicates are strengthened beyond trivial witnesses.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Hyperbolicity.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `plan/PLAN_41_residual_bounds_elimination.md`
Stuck Rule: STUCK if strengthening any contract necessarily reintroduces a project axiom in `check_axioms`.
Last Updated: 2026-03-03

## Work Log

- [ ] Replace `PseudoSiegelAPrioriBounds` placeholder payload with a nontrivial contract that still admits theorem-level construction.
- [ ] Tighten `IsHyperbolic1DUnstable`/`IsHyperbolic` interfaces incrementally and keep compatibility shims.
- [ ] Re-prove `molecule_conjecture_refined` via the strengthened path and re-run `check_axioms`.

## Current Audit Snapshot

- Axiom status:
  - clean (no project axiom symbols in final theorem).
- Main risk:
  - semantic weakening introduced by the cutover contracts.
