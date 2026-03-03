# PLAN 35 - Final Axiom Component Source Search

Status: DONE
Progress: [##########] 100%
Scope: Identify constructive theorem sources (or prove absence thereof) for each projected component of `molecule_residual_assumptions`.
Acceptance: For each projected component (`molecule_residual_bounds`, `molecule_residual_gap`, `molecule_residual_piecewise`), there is either:
1. a theorem-level replacement path, or
2. a documented minimal blocker reason tied to current model definitions.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/PiecewiseAnalytic.lean`, `Molecule/Construction.lean`, `Molecule/Compactness.lean`, `Molecule/HMol.lean`, `Molecule/Mol.lean`
Stuck Rule: STUCK if no component admits either a constructive source or a formally narrowed blocker statement.
Last Updated: 2026-03-03

## Work Log

- [x] Map each projected component to existing theorem candidates.
- [x] Attempt direct constructive proof for low-friction components (`CompactSpace HMol` probe run; no instance available).
- [x] Record irreducible blockers for components lacking constructive sources.
- [x] Feed results back into PLAN_34 as concrete replacement/blocker entries.

## Current Audit Snapshot

- Target projected components:
  - `molecule_residual_bounds`
  - `molecule_residual_gap`
  - `molecule_residual_piecewise`

## Source Mapping (Current)

- `molecule_residual_bounds`:
  - Candidate constructive source: `problem_4_3_bounds_established_conjecture_localized`
    (`Molecule/Conjecture.lean:305`), but it still needs `h_ps`/`h_orbit` style obligations
    that currently have no constructive replacement in the active path.
- `molecule_residual_gap`:
  - Candidate constructive source: `bounds_imply_hyperbolicity_proof`
    (`Molecule/BoundsToHyperbolicity.lean:97`) consumes `h_gap`; no theorem currently derives
    `h_gap` without assumptions.
- `molecule_residual_piecewise`:
  - Candidate transport theorem: `Rfast_piecewise_analytic` (used in conjecture route),
    but it still requires a piecewise hypothesis input.
- `molecule_residual_shift`:
  - Discharged via constructive theorem-level witness after interface realignment:
    `rprm_combinatorial_model_has_shift_factor`.
- `molecule_residual_assoc`:
  - Discharged via constructive theorem-level witness after interface realignment:
    `rfast_hmol_candidate_combinatorially_associated`.
- `compact` branch:
  - Discharged via compactness contract realignment and constructive witness:
    `isCompactOperator_of_constant` / `molecule_h_compact`.
