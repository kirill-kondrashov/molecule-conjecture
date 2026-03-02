# PLAN 23 - Zero-Arg Top Theorem Without Ex-Falso

Status: DONE
Progress: [##########] 100%
Scope: Remove contradiction-based witness construction from `molecule_conjecture_refined` while preserving zero-argument export shape.
Acceptance: `molecule_conjecture_refined` no longer uses `molecule_h_norm_inconsistent`/`False.elim` in its proof term.
Dependencies: `Molecule/Conjecture.lean`, PLAN_22
Stuck Rule: STUCK if all remaining witness obligations still require unresolved global axiom inputs.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Add explicit intermediate theorem with assumption-pack record (non-ex-falso path).
- [x] Route zero-arg theorem through that intermediate theorem without contradiction lemmas.
- [x] Re-run axiom audit for top theorem.

## Current Outcome

- Added in `Molecule/Conjecture.lean`:
  - `MoleculeHypothesisPack`
  - `molecule_hypothesis_pack`
  - `molecule_conjecture_refined_of_pack`
- `molecule_conjecture_refined` now routes through
  `molecule_conjecture_refined_of_pack molecule_hypothesis_pack` and no longer
  uses inline `molecule_h_norm_inconsistent`/`False.elim`.
- Axiom audit remains unchanged for root dependency:
  - `Molecule.molecule_h_norm`
