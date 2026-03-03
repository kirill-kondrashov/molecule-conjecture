# PLAN 21 - Axiom Audit Driven Refactor

Status: DONE
Progress: [##########] 100%
Scope: Use `#print axioms`/`check_axioms` output to iteratively remove residual root axiom paths from top theorem.
Acceptance: Top theorem axiom list excludes all `Molecule.molecule_h_*` symbols.
Dependencies: `Molecule/Conjecture.lean`, PLAN_20, PLAN_22, PLAN_23, PLAN_24
Stuck Rule: STUCK if only remaining path to proof is contradiction from an unresolved project axiom.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Add intermediate theorem checkpoints and audit after each.
- [x] Remove `molecule_h_norm` dependency from `molecule_h_fixed_data`/`molecule_h_spectral_data` global bridges.
- [x] Remove final `molecule_h_*` root axiom path.

## Current Outcome

- Added intermediate checkpoints:
  - `problem_4_3_fixed_point_data_of_global`
  - `problem_4_3_bounds_established_conjecture_localized`
  - `bounds_implies_hyperbolicity_of_spectral_data`
  - `Rfast_hyperbolicity_conjecture_localized`
  - `MoleculeHypothesisPack`
  - `molecule_conjecture_refined_of_pack`
- Cutover theorem path now consumes localized fixed-point + gap/conjugacy contracts:
  - `molecule_conjecture_refined_with_localized_slice_data`
- Pack minimization step completed:
  - removed unused legacy fields from `MoleculeHypothesisPack`
- Replaced fixed-point data bridge with localized extraction from `h_data`.
- Removed packed spectral-data bridge and switched localized hyperbolicity route
  to `h_conj` + `h_gap` + localized bounds.
- Audit now shows no `Molecule.molecule_h_*` dependency.
- Remaining project axiom is:
  - `Molecule.molecule_core_assumptions`
