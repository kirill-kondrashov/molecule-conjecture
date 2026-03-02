# PLAN 22 - Hyperbolicity Local Fixed-Point Cutover

Status: DONE
Progress: [##########] 100%
Scope: Remove global `h_norm` from hyperbolicity-facing signatures by introducing localized intermediary contracts.
Acceptance: A hyperbolicity-entry theorem compiles with no global `h_norm` parameter in its public signature.
Dependencies: `Molecule/HyperbolicityTheorems.lean`, `Molecule/Problem4_3.lean`, `Molecule/Conjecture.lean`
Stuck Rule: STUCK if hyperbolicity chain cannot consume fixed-point data without simultaneous full-file signature rewrite.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Add localized hyperbolicity-entry theorem using spectral data contract.
- [x] Add compatibility bridge from legacy global-signature theorem to localized theorem.
- [x] Thread localized hyperbolicity-entry theorem into conjecture-level top chain.

## Current Outcome

- Added `bounds_implies_hyperbolicity_of_spectral_data` in
  `Molecule/HyperbolicityTheorems.lean` (no global `h_norm` in public signature).
- Refactored `bounds_implies_hyperbolicity` to bridge through the localized theorem.
- Refactored `Rfast_hyperbolicity_conjecture` in `Molecule/Conjecture.lean`
  to route hyperbolicity through localized spectral-data entry.
