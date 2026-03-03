# PLAN 06 - Contract Consistency Refactor

Status: DONE
Progress: [##########] 100%
Scope: Remove contradictory global hypothesis contracts and introduce consistent, localizable hypothesis bundles.
Acceptance: Introduce consistent contract layer; no theorem requires the known-contradictory global `h_norm` form on the new path.
Dependencies: `Molecule/Conjecture.lean`, downstream theorem signatures
Stuck Rule: STUCK if contract edits force incompatible rewrites across core modules without a compilable migration layer.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Introduce normalized/invariant-set hypothesis bundle in code.
- [x] Add migration lemma(s) from old global contract to new local contract (compatibility path).
- [x] Add invariant slice-data migration layer.
- [x] Start rewiring first theorem to consume new contract bundle.

## Current Outcome

- Contract refactor artifacts are in place and first cutover theorem has been wired.
