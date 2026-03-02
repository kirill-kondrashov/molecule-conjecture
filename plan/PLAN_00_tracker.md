# PLAN 00 - Molecule Hypothesis Elimination Tracker

Status: ACTIVE
Progress: [#########-] 90%
Scope: Track all hypothesis-elimination plans, dependencies, blockers, and global readiness.
Acceptance: All plans are either DONE or STUCK with explicit blocker notes; global status reflects critical path truthfully.
Dependencies: PLAN_11, PLAN_12, PLAN_15, PLAN_17, PLAN_18, PLAN_20, PLAN_21, PLAN_22, PLAN_23, PLAN_24
Stuck Rule: Mark STUCK if all active unblocker plans (PLAN_15, PLAN_17, PLAN_18, PLAN_21, PLAN_24) are STUCK.
Last Updated: 2026-03-02

## Plan Matrix

| Plan | Target Hypotheses | Status | Progress |
|---|---|---|---|
| PLAN_06 | Contract consistency refactor | DONE | [##########] 100% |
| PLAN_07 | De-wrapper pseudo-Siegel/orbit | DONE | [##########] 100% |
| PLAN_11 | Full axiom burndown | ACTIVE | [#########-] 90% |
| PLAN_12 | h_exists/h_norm localization | DONE | [##########] 100% |
| PLAN_13 | h_orbit non-circular path | DONE | [##########] 100% |
| PLAN_15 | Replace global h_norm contract | ACTIVE | [######----] 60% |
| PLAN_17 | Signature migration to local norm | ACTIVE | [#######---] 70% |
| PLAN_18 | Global norm signature cutover | ACTIVE | [#########-] 90% |
| PLAN_20 | Problem4_3 local norm cutover | DONE | [##########] 100% |
| PLAN_21 | Axiom audit driven refactor | ACTIVE | [#######---] 70% |
| PLAN_22 | Hyperbolicity local fixed-point cutover | DONE | [##########] 100% |
| PLAN_23 | Zero-arg theorem de-ex-falso | DONE | [##########] 100% |
| PLAN_24 | Root h_norm axiom exit strategy | ACTIVE | [#######---] 70% |

## Dependency Map

- Current execution path PLAN_11 depends primarily on PLAN_24/21, with PLAN_15/17/18 as support.

## Current Notes

- `molecule_h_conj` converted from axiom to theorem.
- `molecule_h_ps` converted from axiom to theorem.
- `molecule_h_orbit`, `molecule_h_piecewise`, `molecule_h_shift`, `molecule_h_assoc`,
  `molecule_h_compact`, `molecule_h_gap`, `molecule_h_unique` converted to theorem declarations.
- Legacy STUCK plans were removed and archived in `ARCHIVE_legacy_stuck_2026-03-02.md`.
- Completed plans archived in `ARCHIVE_completed_2026-03-02.md`.
- Deferred plans archived in `ARCHIVE_deferred_2026-03-02.md`.
- Newly stuck root plan archived in `ARCHIVE_stuck_2026-03-02_round2.md`.
- PLAN_18 delivered first cutover theorem:
  - `molecule_conjecture_refined_with_localized_slice_data`
- PLAN_20 completed localized Problem 4.3 cutover:
  - `FixedPointNormalizationData`
  - `fixed_point_normalization_data_of_legacy`
  - `problem_4_3_bounds_established_of_fixed_point_data`
  - Legacy `problem_4_3_bounds_established` now bridges to localized theorem.
- PLAN_22 delivered first localized hyperbolicity entry:
  - `bounds_implies_hyperbolicity_of_spectral_data`
  - Legacy `bounds_implies_hyperbolicity` now bridges through it.
- PLAN_22 is now complete after threading into conjecture-level hyperbolicity path.
- PLAN_23 is now complete with zero-arg theorem de-ex-falso cutover:
  - `MoleculeHypothesisPack`
  - `molecule_hypothesis_pack`
  - `molecule_conjecture_refined_of_pack`
- Added conjecture-level localized hyperbolicity cutover artifacts:
  - `Rfast_hyperbolicity_conjecture_localized`
  - localized fixed-point/spectral witnesses:
    `molecule_h_fixed_data`, `molecule_h_spectral_data`
- `molecule_conjecture_refined_with_localized_slice_data` now consumes localized
  fixed-point/spectral contracts in place of an explicit global `h_norm` argument.
- PLAN_12 completed conjecture-level rewiring:
  - `problem_4_3_bounds_established_conjecture_localized`
  - `problem_4_3_fixed_point_data_of_global`
- PLAN_06 delivered contract-layer code artifacts:
  - `NormalizationOn`
  - `HasInvariantNormalization`
  - `has_invariant_normalization_of_global`
- PLAN_06 is now complete.
- PLAN_12 added compatibility bridge:
  - `HasInvariantSliceData`
  - `has_invariant_slice_data_of_exists`
  - `has_invariant_slice_data_with_normalization_of_global`
- Stuck plans removed and archived in `ARCHIVE_stuck_2026-03-02_round3.md`:
  - `PLAN_16_nonexplosive_top_theorem_path.md`
  - `PLAN_19_top_theorem_refactor_without_global_norm.md`
- No newly STUCK plans in this round.
- New follow-up plan added:
  - `PLAN_24_root_norm_axiom_exit_strategy.md`

## Current Critical Blockers

1. Final unresolved root axiom: `molecule_h_norm`.
