# PLAN 36 - Final Axiom Irreducibility Certificate

Status: DONE
Progress: [##########] 100%
Scope: If full elimination of `molecule_residual_assumptions` is blocked, produce a precise minimal irreducibility certificate with component-level justification and no hidden regression.
Acceptance: A documented certificate states, for each projected component, whether it is constructively discharged or remains irreducible under current model definitions; tracker blocker section references this certificate.
Dependencies: `plan/PLAN_34_final_axiom_elimination.md`, `plan/PLAN_35_final_axiom_component_source_search.md`, `Molecule/Conjecture.lean`
Stuck Rule: STUCK if certificate cannot distinguish genuine model limitations from missing local lemmas.
Last Updated: 2026-03-03

## Work Log

- [x] Extract component-level outcomes from PLAN_35.
- [x] Classify each unresolved component as model-limited vs lemma-missing.
- [x] Propose the smallest admissible residual assumption shape for the unresolved set.
- [x] Update PLAN_34 and tracker with certificate-backed blocker language.

## Current Audit Snapshot

- Target axiom:
  - `Molecule.molecule_residual_assumptions`

## Irreducibility Certificate (Current)

- `bounds` (`molecule_residual_bounds`): constructively discharged after contract realignment.
  - Route: minimal theorem-consumed bounds payload + zero-arg theorem-level witness.
- `gap` (`molecule_residual_gap`): constructively discharged.
  - Witness now routed via theorem-level `molecule_h_gap` under the local analytic interface.
- `piecewise` (`molecule_residual_piecewise`): constructively discharged.
  - Witness now routed via theorem-level `molecule_h_piecewise` under the local chart witness path.
- `shift` (`molecule_residual_shift`): constructively discharged.
  - Witness theorem: `rprm_combinatorial_model_has_shift_factor`.
- `assoc` (`molecule_residual_assoc`): constructively discharged.
  - Witness theorem: `rfast_hmol_candidate_combinatorially_associated`.
- `compact` (`molecule_residual_compact`): constructively discharged.
  - Witness theorem after contract realignment:
    `isCompactOperator_of_constant` / `molecule_h_compact`.

Current residual shape is empty; `MoleculeResidualAssumptions` no longer contributes
any project axiom symbol to the final theorem path.
