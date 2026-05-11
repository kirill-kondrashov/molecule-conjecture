# PLAN 87 - Non-Circular Critical Seed Source

Status: STUCK
Progress: [######----] 60%
Scope: Seed-side subtrack of the broader dual-track program. Produce the
stronger upstream seed theorem actually needed by the downstream rebase:

```text
MoleculeResidualCriticalRenormalizableFixedSeedSource
```

That is, exhibit a map `f_seed : BMol` with:
- `IsFastRenormalizable f_seed`
- `Rfast f_seed = f_seed`
- `criticalValue f_seed = 0`

without using the blocked current existence route.

Critical revision:
- As a standalone master research program, this plan is too narrow.
- PLAN_86 already exposed two structurally live upstream targets:
  1. a non-circular critical seed
  2. a genuinely non-singleton localized bridge source
- Current plausibility is asymmetric, however:
  the seed side has a concrete producer inventory, while the localized branch
  now needs a new producer class beyond the closed refined-chart route.
- So this file is now the seed-side subtrack only. The active master program is
  `PLAN_88_dual_track_seed_or_non_singleton_localized_bridge.md`.

Acceptance:
1. Produce a theorem of type
   `MoleculeResidualCriticalRenormalizableFixedSeedSource`
   whose `#print axioms` output does not contain `Molecule.molecule_h_norm`.
2. The proof must not go through:
   - `fixed_point_exists`
   - `selected_fixed_point`
   - current `molecule_residual_fixed_point_existence_source`
   - any theorem already shown equivalent to the blocked global `R` route.
3. Thread the result through the existing downstream cutovers:
   - `molecule_residual_fixed_point_data_source_of_critical_renormalizable_fixed_seed_source_and_renorm_vbound`
   - `molecule_residual_fixed_point_local_witness_on_sources_of_critical_renormalizable_fixed_seed_source_and_renorm_vbound`
4. If every candidate seed source collapses to the current canonical/current
   singleton route, record the exact obstruction and hand off to the larger-domain
   branch owned by PLAN_88.

Dependencies: `Molecule/Conjecture.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_86_localized_or_reseeded_R_replacement.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_78_non_h_norm_local_witness_on_sources_theorem.md`

Stuck Rule: STUCK if all candidate seed producers are either:
- definitionally equivalent to current canonical/current singleton routes, or
- `Molecule.molecule_h_norm`-backed, or
- blocked by the same `defaultBMol` obstruction as the old global route.

Last Updated: 2026-04-30

## Critical Audit Revision

- `PLAN_89` has already closed the current in-repository seed-producer
  inventory.
- No surviving non-`molecule_h_norm` seed producer class is currently named in
  the repository.
- So this plan is presently stuck in the honest sense:
  it should be reopened only if `PLAN_90` / `PLAN_91` yields a genuinely new
  operator-side producer class, or if a new external source family is encoded.

## Research Program

- [x] Enumerate current in-repository candidate non-circular seed producers
  above the singleton/canonical equivalence class.
- [x] Test the current in-repository candidates and record why they do not yield
  `MoleculeResidualCriticalRenormalizableFixedSeedSource`.
- [ ] Thread any successful seed into the existing fixed-data/local-witness
  cutovers.
- [x] Record the present obstruction and hand off to the redesign branch owned
  by `PLAN_88` / `PLAN_90`.

## Priority Order

1. Reopen only on a genuinely new producer class
2. Thread a successful seed through the existing downstream cutovers
3. Otherwise keep the redesign handoff explicit and avoid wrapper churn

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Candidate inventory | The current in-repository inventory is closed: no surviving non-`molecule_h_norm` seed producer class is presently named. | [##########] 100% |
| Seed theorem target | Exact target remains `MoleculeResidualCriticalRenormalizableFixedSeedSource`, but no live producer currently reaches it. | [###-------] 30% |
| Downstream cutover readiness | Already complete structurally via PLAN_86. | [##########] 100% |
| Handoff to redesign branch | Owned by PLAN_88 / PLAN_90 and already triggered by the closed current inventory. | [##########] 100% |

## Notes

- PLAN_86 completed the structural work:
  - singleton localized route
  - singleton reseeded route
  - canonical singleton route
  are now all compared explicitly.
- Critical revision:
  - this plan should not be used as the sole active research program
  - singleton localized and canonical seed routes have already been shown to
    collapse to the same upstream debt
  - therefore the broader program must still keep a localized escape hatch,
    but current operational priority should sit on seed-side inventory rather
    than abstract larger-domain wrapper search
- The exact remaining downstream requirement is already exposed:
  existence alone is not enough; fixed-data/local-witness need a critical seed
  plus `RV`.
- Critical correction:
  even a successful seed theorem is only an upstream hit. Full downstream
  progress still depends on fixed-point critical-value transfer and `RV`,
  tracked outside this file.
- Ownership correction:
  those sidecar carriers are not owned here; they stay with `PLAN_80`,
  `PLAN_78`, and `PLAN_53`.
- New checkpoint:
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer`
  - added
    `molecule_residual_fixed_point_data_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound`
    and
    `molecule_residual_fixed_point_local_witness_on_sources_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound`
  - targeted probes show all three are ground-axiom-only
  - this does not solve the seed-side theorem search, but it makes the exact
    canonical-side external gate fully explicit
- New checkpoint:
  - added
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_standard_siegel_fixed_point`
  - targeted probe shows it is ground-axiom-only
  - this exposes one concrete alternative seed-side producer family already
    present in the repository:
    the standard-Siegel / Feigenbaum fixed-point assumptions
  - but this family is not a valid non-circular hit for PLAN_87, because it
    explicitly factors through `h_norm`
- Therefore this plan owns only the theorem search for a non-circular critical
  seed source, under the broader PLAN_88 program.
