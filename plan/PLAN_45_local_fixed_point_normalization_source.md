# PLAN 45 - Local Fixed-Point Normalization Source

Status: ACTIVE
Progress: [#---------] 10%
Scope: Replace the inconsistent global-normalization seam with a local fixed-point normalization source that can feed Problem 4.3 bounds without `molecule_h_norm`.
Acceptance: `molecule_residual_bounds_seed_free` no longer depends on `molecule_h_norm`; `check_axioms` for `Molecule.molecule_conjecture_refined` does not report `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/PLAN_44_constructive_slice_witness_refactor.md`
Stuck Rule: STUCK if no theorem-level route can produce `FixedPointNormalizationData` without reintroducing project axioms.
Last Updated: 2026-03-03

## Motivation

- `Molecule.global_normalization_contract_inconsistent` and
  `Molecule.no_global_normalization_contract` show the legacy global-normalization
  contract is inconsistent in the current model.
- Any remaining route that depends on this contract is mathematically blocked.

## Work Plan

- [x] Add an explicit dead-end certificate theorem in `Molecule/Conjecture.lean` for the global-normalization seam.
- [ ] Introduce a local theorem interface that supplies `FixedPointNormalizationData`
  directly (no `∀ K` global contract).
- [ ] Rewire `molecule_residual_bounds_seed_free` through the local fixed-point
  normalization interface.
- [ ] Remove `molecule_h_norm` from zero-arg residual exports and dependent wrappers.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes to confirm frontier movement.

## Candidate Next Proof Targets

- A seed-free theorem producing:
  - `∃ f_star, Rfast f_star = f_star ∧ IsFastRenormalizable f_star ∧
    criticalValue f_star = 0 ∧ f_star.V ⊆ Metric.ball 0 0.1`
- Or an equivalent theorem that directly builds `FixedPointNormalizationData`.

