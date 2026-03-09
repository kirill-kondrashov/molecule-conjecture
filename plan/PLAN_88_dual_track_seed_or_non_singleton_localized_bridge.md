# PLAN 88 - Dual-Track Seed Or Non-Singleton Localized Bridge

Status: ACTIVE
Progress: [#####-----] 45%
Scope: Coordination and gating plan for replacing the formally blocked global
witness-side route by pursuing the two genuinely live upstream targets in
parallel:

1. a non-circular critical seed source
2. a genuinely non-singleton localized bridge source

This plan is the critical revision of the current research program. It exists
because PLAN_87 was too narrow as a master program: seed search is only one
subtrack, not the whole live search space. It is not itself the owner of every
remaining theorem on the downstream branches.

Acceptance:
1. Treat either of the following only as a real upstream breakthrough:
   - `MoleculeResidualCriticalRenormalizableFixedSeedSource`
   - `MoleculeResidualNonSingletonLocalizedBridgeSources`
   both without `Molecule.molecule_h_norm`.
2. Do not count as progress any producer that is definitionally equivalent to:
   - the current canonical singleton route
   - the refined singleton-domain route
   - the current existence route
   - the formally blocked global `R` route
3. On the localized-side track, do not count as progress any `K` or bridge
   package that is defined from, or whose proof factors through:
   - `MoleculeResidualRenormalizableFixedSeedSource`
   - `MoleculeResidualCriticalRenormalizableFixedSeedSource`
   - any definition explicitly mentioning `IsFastRenormalizable`
   - the current singleton/canonical equivalence class
4. Keep the two tracks separate:
   - seed-side theorem search is owned by PLAN_87
   - larger-domain localized search is owned here directly
5. Treat fixed-point critical-value transfer and renormalizable-point `V`-bound
   control (`RV`) as external dependencies owned by existing plans:
   - `PLAN_80`
   - `PLAN_78`
   - `PLAN_53`
   This plan may coordinate with those carriers, but does not itself own their
   proof search.
6. Do not count an upstream breakthrough as downstream completion unless it is
   paired with:
   - fixed-point critical-value transfer, and
   - renormalizable-point `V`-bound control (`RV`)
   through the already exposed cutovers.
7. If one track collapses to an already-known equivalence class, keep the other
   track active rather than declaring the overall program stalled.
8. If both tracks collapse, record the exact obstruction and hand off to model
   redesign.

Dependencies: `Molecule/Conjecture.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_86_localized_or_reseeded_R_replacement.md`,
`plan/PLAN_87_non_circular_critical_seed_source.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`

Stuck Rule: STUCK only if both of the following are established:
- every seed-side candidate collapses to the singleton/canonical equivalence
  class, and
- every larger-domain candidate collapses to the singleton route or to a
  previously blocked obstruction.

Last Updated: 2026-03-09

## Critical Revision

- PLAN_87 isolated the exact seed target correctly.
- But as a full research program it was too narrow, because the repository now
  has a second co-equal live target:
  `MoleculeResidualNonSingletonLocalizedBridgeSources`.
- Treating larger-domain localization as a mere fallback would bias the search
  toward the singleton/canonical equivalence class that is already known to be
  structurally saturated.
- This plan also needed a second correction:
  an upstream breakthrough is not the same as a full route replacement.
  The downstream interface still requires critical-value transfer and `RV`.
- And a third correction:
  a “larger-domain” package is not meaningful if it secretly bakes in
  renormalizability or is recovered from the seed/singleton equivalence class.
- And a fourth correction:
  this plan should not pretend to own the sidecar carrier proofs already owned
  by `PLAN_80`, `PLAN_78`, and `PLAN_53`.

## Research Program

- [ ] Maintain two explicit theorem-search tracks:
  - seed-side: `MoleculeResidualCriticalRenormalizableFixedSeedSource`
  - localized-side: `MoleculeResidualNonSingletonLocalizedBridgeSources`
- [ ] For every candidate, first prove it escapes the current singleton /
  canonical equivalence class.
- [ ] For every localized-side candidate, prove it is non-circular in the
  stronger sense: the domain/bridge package is not defined from a seed route
  and does not smuggle in renormalizability.
- [ ] Treat critical-value transfer + `RV` as external readiness gates from
  `PLAN_80` / `PLAN_78` / `PLAN_53`, not as local proof obligations of this
  plan.
- [ ] If a seed-side candidate lands, record the exact downstream gate:
  re-enter fixed-data/local-witness through the existing cutovers once the
  sidecar carriers are available.
- [ ] If a localized-side candidate lands, record the exact downstream gate:
  re-enter existence/canonical/fixed-data/local-witness through the existing
  cutovers once the sidecar carriers are available.
- [ ] If both tracks collapse, write the exact obstruction and escalate to a
  model-redesign plan rather than continuing wrapper search.

## Priority Order

1. Non-equivalence screening for both tracks
2. Strong non-circularity screening for localized-side candidates
3. Seed-side producer inventory above the singleton/canonical class
4. Larger-domain producer inventory above the refined-singleton class
5. Coordinate exact downstream gate with `PLAN_80` / `PLAN_78` / `PLAN_53`
6. Obstruction certificate if both tracks collapse

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Seed-side track | Exact theorem target isolated, but no non-circular producer yet. | [##--------] 20% |
| Larger-domain localized track | Exact theorem target isolated, but no genuinely larger live domain source yet. | [##--------] 20% |
| Non-equivalence screening | Singleton localized / singleton seed / canonical seed collapse already recorded. | [######----] 60% |
| Strong non-circularity screening | Not yet enforced explicitly on the localized-side search. | [##--------] 20% |
| Downstream cutover readiness | Already complete structurally via PLAN_86. | [##########] 100% |
| External sidecar dependency gate | Exact downstream interface is known and now partially realized by common-midend cutovers from both upstream tracks into the stronger critical-seed contract and the canonical fixed-data/local-witness gate. | [########--] 80% |
| Redesign handoff | Ready if both tracks collapse. | [###-------] 30% |

## Notes

- Exact seed-side target:
  `MoleculeResidualCriticalRenormalizableFixedSeedSource`
- Exact localized-side target:
  `MoleculeResidualNonSingletonLocalizedBridgeSources`
- Exact downstream interface after either upstream breakthrough:
  - replacement existence,
  - fixed-point critical-value transfer,
  - renormalizable-point `V`-bound control (`RV`)
- Ownership correction:
  this plan owns the upstream replacement search only.
  The sidecar carriers remain owned by `PLAN_80`, `PLAN_78`, and `PLAN_53`.
- New checkpoint:
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer`
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer`
  - added
    `molecule_residual_fixed_point_data_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound`
    and
    `molecule_residual_fixed_point_local_witness_on_sources_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound`
  - targeted probes show all four new theorems are ground-axiom-only
  - this means the two PLAN_88 upstream tracks now share one exact common
    midpoint once critical-value transfer is available, and the seed-side
    canonical gate into fixed-data/local-witness is fully explicit
- The current refined singleton localized route cannot supply the larger-domain
  target:
  `no_nontrivial_member_of_refined_invariant_fixed_seed_singleton_domain_sources`
- Critical revision:
  a candidate larger-domain package is still invalid if it only repackages a
  seed theorem or encodes renormalizability directly in the domain.
- Therefore the next honest progress must either:
  - produce a genuinely non-circular seed, or
  - produce a genuinely non-singleton live localized domain.
