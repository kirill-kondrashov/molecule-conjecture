# PLAN 87 - Non-Circular Critical Seed Source

Status: ACTIVE
Progress: [##--------] 20%
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
- PLAN_86 already exposed two co-equal live upstream targets:
  1. a non-circular critical seed
  2. a genuinely non-singleton localized bridge source
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
- blocked by the same `defaultBMol` obstruction as the old global route.

Last Updated: 2026-03-09

## Research Program

- [ ] Enumerate candidate non-circular seed producers above the current
  singleton/canonical equivalence class.
- [ ] Test whether any candidate already yields
  `MoleculeResidualCriticalRenormalizableFixedSeedSource`.
- [ ] Thread any successful seed into the existing fixed-data/local-witness
  cutovers.
- [ ] If all candidate seed producers collapse to the same blocked equivalence
  class, write the exact obstruction and hand off to larger-domain localized
  redesign.

## Priority Order

1. Critical seed from canonical/bounds witness not equivalent to current route
2. Critical seed from alternative upstream package
3. Obstruction certificate if both collapse
4. Hand off immediately if all seed candidates collapse to the singleton class

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Candidate inventory | No non-circular producer isolated yet. | [##--------] 20% |
| Seed theorem target | Exact target is now `MoleculeResidualCriticalRenormalizableFixedSeedSource`; canonical + critical-value-transfer now exposes the exact external gate into it. | [####------] 40% |
| Downstream cutover readiness | Already complete structurally via PLAN_86. | [##########] 100% |
| Handoff to larger-domain branch | Owned by PLAN_88; ready if seed search collapses. | [########--] 80% |

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
  - therefore seed search must be paired with a live larger-domain search,
    rather than treated as primary by default
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
- Therefore this plan owns only the theorem search for a non-circular critical
  seed source, under the broader PLAN_88 program.
