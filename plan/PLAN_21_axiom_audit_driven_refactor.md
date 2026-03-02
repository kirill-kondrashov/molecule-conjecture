# PLAN 21 - Axiom Audit Driven Refactor

Status: ACTIVE
Progress: [#######---] 70%
Scope: Use `#print axioms`/`check_axioms` output to iteratively remove residual root axiom paths from top theorem.
Acceptance: Top theorem axiom list excludes all `Molecule.molecule_h_*` symbols.
Dependencies: `Molecule/Conjecture.lean`, PLAN_20, PLAN_22, PLAN_23, PLAN_24
Stuck Rule: STUCK if only remaining path to proof is contradiction from an unresolved project axiom.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Add intermediate theorem checkpoints and audit after each.
- [ ] Remove final root axiom path.

## Current Outcome

- Added intermediate checkpoints:
  - `problem_4_3_fixed_point_data_of_global`
  - `problem_4_3_bounds_established_conjecture_localized`
  - `bounds_implies_hyperbolicity_of_spectral_data`
  - `Rfast_hyperbolicity_conjecture_localized`
  - `MoleculeHypothesisPack`
  - `molecule_conjecture_refined_of_pack`
- Cutover theorem path now consumes localized fixed-point/spectral contracts:
  - `molecule_conjecture_refined_with_localized_slice_data`
- Audit result still shows one project axiom dependency:
  - `Molecule.molecule_h_norm`
