# PLAN 40 - Analytic Residual Triple Elimination

Status: ACTIVE
Progress: [######----] 60%
Scope: Eliminate the remaining three residual fields (`bounds`, `gap`, `piecewise`) from `MoleculeResidualAssumptions`.
Acceptance: `MoleculeResidualAssumptions` is removed entirely or reduced to an empty theorem-level wrapper, and `check_axioms` for `Molecule.molecule_conjecture_refined` has no project-specific axiom symbols.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/HyperbolicityTheorems.lean`, `Molecule/PiecewiseAnalytic.lean`, `plan/PLAN_34_final_axiom_elimination.md`, `plan/PLAN_36_final_axiom_irreducibility_certificate.md`
Stuck Rule: STUCK if no non-circular route can produce either localized orbit-control witnesses or a theorem deriving `gap`/`piecewise` from already proved data.
Last Updated: 2026-03-03

## Work Log

- [x] Dead-end probe: old `Has1DUnstableDirection` universal-chart quantification forced non-constructive obligations in this model.
- [x] Interface realignment landed for analytic side:
  - `IsHyperbolic1DUnstable` reduced to unstable-multiplier witness.
  - `Has1DUnstableDirection` switched to local chart witness.
- [x] Derive `gap` and `piecewise` constructively from local witness path (no residual-field dependence).
- [ ] Build a localized orbit-control witness path that does not rely on `False.elim` routes.
- [ ] Derive `bounds` constructively from localized fixed-point + orbit-control data.
- [ ] Remove the residual axiom declaration and route the zero-arg theorem entirely through theorem-level data.
- [x] Re-run `lake build` and `check_axioms`; remaining project axiom is still `Molecule.molecule_residual_assumptions`.

## Current Audit Snapshot

- Remaining residual fields:
  - `bounds`
