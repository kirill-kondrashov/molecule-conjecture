# PLAN 34 - Final Axiom Elimination

Status: ACTIVE
Progress: [##########] 95%
Scope: Eliminate the last remaining project axiom `Molecule.molecule_residual_assumptions` while keeping `molecule_conjecture_refined` zero-arg and compiling.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` lists no project-specific axiom symbols from `Molecule.*`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/PiecewiseAnalytic.lean`, `Molecule/Construction.lean`, `Molecule/Compactness.lean`
Stuck Rule: STUCK if every route to remove `molecule_residual_assumptions` requires reintroducing an equivalent project axiom under a different name with no net reduction.
Last Updated: 2026-03-03

## Work Log

- [x] Add theorem-level projection layer from residual assumptions (`molecule_residual_bounds`, `molecule_residual_gap`, `molecule_residual_piecewise`, `molecule_residual_shift`, `molecule_residual_assoc`, `molecule_residual_compact`) and route packed assembly through a dedicated residual builder.
- [x] Split the former final wrapper into minimal theorem-level obligations and keep compatibility aliases (`molecule_final_*`).
- [x] Start component-source audit via PLAN_35 and connect projected fields to candidate theorems/transport lemmas.
- [x] Execute combinatorial interface realignment (PLAN_38 Option B) so shift/association are theorem-level witnesses instead of residual axiom fields.
- [x] Execute compactness interface realignment (PLAN_39 Option B) so compactness is theorem-level witness instead of residual axiom field.
- [x] Shrink `MoleculeResidualAssumptions` by removing `shift`, `assoc`, and `compact` fields.
- [x] Shrink `MoleculeResidualAssumptions` further by removing `gap` and `piecewise` fields after analytic interface realignment.
- [ ] Attempt constructive replacement for each obligation from existing local lemmas and model definitions.
- [ ] If full elimination is blocked, prove and record the minimal irreducible assumption set with explicit rationale.
- [x] Re-run `lake build` and `check_axioms`; verify current single project axiom is `Molecule.molecule_residual_assumptions`.

## Current Audit Snapshot

- Final remaining project axiom:
  - `Molecule.molecule_residual_assumptions`
- Remaining residual fields after current cutover:
  - `bounds`
