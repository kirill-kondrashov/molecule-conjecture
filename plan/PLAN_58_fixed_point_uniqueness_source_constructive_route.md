# PLAN 58 - Fixed-Point Uniqueness Source Constructive Route

Status: ACTIVE
Progress: [##--------] 20%
Scope: Replace the current ex-falso uniqueness source (`molecule_residual_fixed_point_uniqueness_source`) with a theorem-level constructor route that does not depend on `molecule_h_norm`, and integrate it into fixed-point/orbit composition seams.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source` no longer carries `Molecule.molecule_h_norm` through uniqueness.
3. The replacement route is non-circular with respect to `molecule_residual_non_ground_sources`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if all available uniqueness constructors still require either `False.elim` from `molecule_h_norm_inconsistent` or a source that depends on the current `molecule_residual_non_ground_sources` chain.
Last Updated: 2026-03-04

## Work Plan

- [x] Open a focused uniqueness-source track and connect it to active fixed-point/orbit integration seams.
- [x] Inventory uniqueness constructors in `Molecule/Conjecture.lean` and imported uniqueness modules.
- [ ] Add explicit seam theorem(s) that project uniqueness from strictly weaker, non-circular assumptions.
- [ ] Rewire `molecule_residual_fixed_point_uniqueness_source` through the new seam path.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- Current theorem `molecule_residual_fixed_point_uniqueness_source` is still:
  `molecule_h_unique`, where `molecule_h_unique` is obtained by `False.elim molecule_h_norm_inconsistent`.
- The new integration seams from PLAN_49/53 make this blocker explicit at:
  - `molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_uniqueness_source`
  - `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source`.
- Inventory checkpoint:
  - `Molecule/RenormalizationFixedPointUniqueness.lean` currently exports
    uniqueness only as assumption-driven wrappers (`R_hybrid_unique_fixed_point`
    and `renormalization_fixed_point_unique`) and does not provide a standalone
    non-assumptive uniqueness constructor.
