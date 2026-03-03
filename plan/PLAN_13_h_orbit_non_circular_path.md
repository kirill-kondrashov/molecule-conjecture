# PLAN 13 - h_orbit Non-Circular Path

Status: DONE
Progress: [##########] 100%
Scope: Remove circular dependency for orbit-control assumptions and create a constructive/non-circular proof route.
Acceptance: `molecule_h_orbit` no longer appears as an axiom dependency of `molecule_conjecture_refined`.
Dependencies: `Molecule/RenormalizationOrbit.lean`, `Molecule/Problem4_3.lean`, `Molecule/Conjecture.lean`
Stuck Rule: STUCK if no consistent non-circular route exists under current `Rfast`/`IsFastRenormalizable` model.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Build minimal non-circular orbit lemma that avoids taking `h_orbit` as direct input.
- [x] Integrate route into conjecture-level hypothesis elimination.

## Current Outcome

- `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists `Molecule.molecule_h_orbit`.
