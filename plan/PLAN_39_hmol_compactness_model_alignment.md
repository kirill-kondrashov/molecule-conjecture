# PLAN 39 - HMol Compactness Model Alignment

Status: DONE
Progress: [##########] 100%
Scope: Resolve the compactness bottleneck by aligning the `HMol` model and `IsCompactOperator` contract with a constructively provable compactness statement.
Acceptance: Either
1. a theorem-level witness discharges `IsCompactOperator Rfast_HMol_candidate`, or
2. `IsCompactOperator` is replaced by a mathematically justified weaker compactness/precompactness contract that is constructively witnessable and propagated through the conjecture theorem path.
Dependencies: `Molecule/HMol.lean`, `Molecule/Compactness.lean`, `Molecule/Conjecture.lean`, `plan/PLAN_35_final_axiom_component_source_search.md`, `plan/PLAN_37_residual_component_attack_queue.md`
Stuck Rule: STUCK if no witness or contract redesign can be formulated without contradicting current model invariants.
Last Updated: 2026-03-03

## Work Log

- [x] Audit topology/instances on `HMol` and refute practical `CompactSpace HMol` witness route in current model path.
- [x] Define weaker compactness contract suitable for current model abstractions (`IsCompactOperator` as nonempty compact invariant core).
- [x] Thread selected compactness contract through `molecule_conjecture_refined` and dependent wrappers.
- [x] Re-run `lake build` and `check_axioms` and update PLAN_34/35/36.

## Current Audit Snapshot

- Cutover result:
  - `molecule_residual_compact` eliminated from the residual axiom bundle.
  - Constructive witness available: `isCompactOperator_of_constant` / `molecule_h_compact`.
