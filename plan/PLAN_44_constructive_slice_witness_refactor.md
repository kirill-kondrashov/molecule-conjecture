# PLAN 44 - Constructive Slice Witness Refactor

Status: ACTIVE
Progress: [#####-----] 50%
Scope: Remove the current constant-chart/finiteness bottleneck by refactoring slice witness infrastructure so `h_exists`-style data can be built constructively (without `molecule_h_norm`/ex-falso).
Acceptance: Introduce a constructive `HasInvariantSliceData` witness path that does not use `False.elim` and does not depend on `Molecule.molecule_h_norm`.
Dependencies: `Molecule/BanachSlice.lean`, `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `plan/PLAN_42_post_axiom_contract_hardening.md`
Stuck Rule: STUCK if every candidate chart/model redesign either reintroduces a project axiom or forces contract weakening in exported theorem signatures.
Last Updated: 2026-03-03

## Motivation

- Current obstruction theorem:
  - `Molecule.has_invariant_slice_data_forces_univ_finite`
- With current scaffold (`slice_chart` constant), `HasInvariantSliceData` implies
  `(Set.univ : Set BMol).Finite`, which blocks constructive upstream witness extraction
  in the intended model.

## Work Log

- [x] Add refined chart scaffolding in `Molecule/BanachSlice.lean`:
  - `slice_chart_refined`
  - `slice_chart_refined_open`
  - `refined_singleton_slice_witness`
- [x] Add chart-parameterized invariant-slice package in `Molecule/Conjecture.lean`:
  - `HasInvariantSliceDataWith`
  - `has_invariant_slice_data_with_refined`
- [x] Export zero-arg refined-chart witness:
  - `has_invariant_slice_data_with_refined_default`
- [ ] Redesign slice chart/model contract so chart preimage sets can be finite/nontrivial
  without collapsing to `univ`/`∅` on the main theorem path.
- [ ] Rebuild a constructive `h_exists` witness theorem in `Molecule/Conjecture.lean`.
- [ ] Rewire `molecule_residual_bounds_seed_free` inputs to use constructive upstream
  witness theorems (no `molecule_h_norm`-derived ex-falso).
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Candidate Implementation Notes

- Prefer adding a refined chart/witness interface rather than weakening
  `molecule_conjecture_refined` or core exported contracts.
- Keep backward-compatible wrappers while migrating call sites.
- Stage changes so each step remains buildable and auditable by `check_axioms`.
