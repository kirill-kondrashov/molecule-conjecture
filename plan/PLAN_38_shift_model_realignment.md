# PLAN 38 - Combinatorial Model Realignment

Status: DONE
Progress: [##########] 100%
Scope: Remove proven combinatorial dead-ends by realigning the combinatorial model (`Rprm_combinatorial_model`) and/or combinatorial contracts so shift/association components can become constructively satisfiable.
Acceptance: Either
1. a constructive theorem proves `∃ N, IsConjugateToShift Rprm_combinatorial_model N`, or
2. the conjecture interface is revised to mathematically defensible weaker symbolic/combinatorial relations with corresponding theorem-level witnesses and updated downstream usage.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FirstStepConstruction.lean`, `Molecule/Mol.lean`, `plan/PLAN_36_final_axiom_irreducibility_certificate.md`, `plan/PLAN_37_residual_component_attack_queue.md`
Stuck Rule: STUCK if both strict-conjugacy and revised-interface routes fail to produce a witnessable model contract.
Last Updated: 2026-03-03

## Work Log

- [ ] Option A (strict): redesign `Rprm_constructed` and horseshoe-side model interfaces so strict shift-conjugacy and combinatorial association are satisfiable and provable.
- [x] Option B (interface): replace strict `IsConjugateToShift`/`CombinatoriallyAssociated` requirements with weaker symbolic/combinatorial contracts that match currently constructible data.
- [x] Thread chosen contract through `molecule_conjecture_refined` path and re-run axiom audit.
- [x] Update PLAN_34/35/36 with the chosen unblocking route.

## Current Audit Snapshot

- Cutover result:
  - `rprm_combinatorial_model_has_shift_factor`
  - `rfast_hmol_candidate_combinatorially_associated`
  - `MoleculeResidualAssumptions` no longer includes `shift`/`assoc`.
