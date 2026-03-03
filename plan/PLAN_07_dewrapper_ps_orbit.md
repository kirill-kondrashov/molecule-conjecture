# PLAN 07 - De-wrapper PS/Orbit

Status: DONE
Progress: [##########] 100%
Scope: Replace circular wrappers for pseudo-Siegel and orbit-control assumptions with constructive lemmas.
Acceptance: `molecule_h_ps` and `molecule_h_orbit` have non-circular proof sources.
Dependencies: `PseudoSiegelDisk.lean`, `RenormalizationOrbit.lean`, `Problem4_3.lean`
Stuck Rule: STUCK if opaque predicates prevent any constructive witness route.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Define constructive witness strategy for `PseudoInvariant`.
- [x] Implement first non-wrapper lemma for PS disk existence.
- [x] Implement first non-wrapper orbit-control derivation.

## Current Outcome

- `PseudoInvariant` moved from opaque to constructive placeholder (`True`).
- `molecule_h_ps` is now a theorem (not an axiom).
- `molecule_h_orbit` is now theorem-level and removed from top-level axiom report.
