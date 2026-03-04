# PLAN 53 - Fixed-Point Model Bottleneck Refactor

Status: ACTIVE
Progress: [########--] 87%
Scope: Resolve the model-level bottleneck exposed by `no_fixed_point_implies_renormalizable` so the fixed-point ingredient route can be rebuilt without `molecule_h_norm` and without relying on the false bridge contract.
Acceptance:
1. The fixed-point ingredient route no longer depends on `FixedPointImpliesRenormalizable`.
2. A non-circular theorem-level source provides
   `MoleculeResidualFixedPointExistenceSource` (or stronger ingredient data)
   without `molecule_h_norm`.
3. `molecule_residual_fixed_point_normalization_ingredients` can be rebuilt from
   the new source path.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FixedPointExistence.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationTheorem.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_64_upstream_direct_seam_constructive_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_63_upstream_hybrid_collapse_constructive_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_62_upstream_map_uniqueness_source_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_61_upstream_hybrid_class_uniqueness_source_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_60_hybrid_class_model_refactor_route.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_59_hybrid_unique_fixed_point_source_constructor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
Stuck Rule: STUCK if every non-circular witness candidate still forces the default fixed-point trap (`defaultBMol` fixed but non-renormalizable) without a model-level refactor path.
Last Updated: 2026-03-04

## Work Plan

- [x] Record feasibility gate theorem:
  - `no_fixed_point_implies_renormalizable`.
- [x] Identify minimal theorem/interface changes needed so fixed-point existence
  witness is not forced through the default fixed-point trap.
- [x] Introduce a replacement source seam for renormalizable fixed-point
  existence that does not require the false global bridge contract.
- [x] Route `molecule_residual_fixed_point_normalization_ingredients` through
  the replacement seam.
- [x] Re-run `make build`, `make check`, and targeted `#print axioms` probes.
- [x] Decouple current fixed-point existence/transfer source theorems from
  bridge+uniqueness routing:
  - `molecule_residual_fixed_point_existence_source`
  - `molecule_residual_fixed_point_transfer_source`
- [x] Decouple current fixed-point data source theorem from one-off fixed-data
  seed by composing from explicit source seams:
  - `molecule_residual_fixed_point_data_source_of_sources`.
- [x] Decouple current fixed-point assembly source theorem from fixed-data
  source dependency by routing through explicit existence + transfer seams:
  - `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
- [x] Decouple current fixed-point ingredient source theorem from direct
  normalization theorem dependency by routing through explicit existence +
  transfer seam composition:
  - `molecule_residual_fixed_point_ingredients_source_of_sources`.
- [x] Add fixed-data+uniqueness transfer-component projections and wire them
  into canonical orbit-debt composition seams for cross-track integration:
  - `fixed_point_critical_value_transfer_source_of_fixed_data_and_unique`
  - `fixed_point_vbound_transfer_source_of_fixed_data_and_unique`
  - `molecule_residual_canonical_vbound_source_of_fixed_data_and_unique`
  - `molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_unique`.
- [x] Add transport-wrapped integration seam for canonical orbit debt:
  - `molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_uniqueness_source`
  - current routed theorem
    `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source`.
- [ ] Replace `molecule_residual_fixed_point_data_source` with a non-circular
  non-`molecule_h_norm` theorem-level source.
- [ ] Re-run fixed-point and top-level axiom probes after replacing
  `molecule_residual_fixed_point_data_source`.

## Notes

- This plan supersedes PLAN_52, which is stuck because
  `FixedPointImpliesRenormalizable` is false in the current model.
- Implemented bridge-free ingredient routing in `Molecule/Conjecture.lean`:
  - `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`
  - `molecule_residual_fixed_point_normalization_ingredients` now routes through
    fixed-data + transfer, not through `FixedPointImpliesRenormalizable`.
- Current global-backed source routing no longer uses bridge/ex-falso path:
  - `molecule_residual_fixed_point_existence_source` now routes through
    `renormalizable_fixed_exists_of_global_norm`.
  - `molecule_residual_fixed_point_transfer_source` now routes through
    `fixed_point_local_normalization_transfer_of_global_norm`.
- Current fixed-point data/assembly source routing is now explicit-source
  composed:
  - `molecule_residual_fixed_point_data_source_of_sources`
  - `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
- Current fixed-point ingredient source routing is now explicit-source composed:
  - `molecule_residual_fixed_point_ingredients_source_of_sources`.
- Probe checkpoint:
  - `#print axioms Molecule.molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`
    is ground-axiom-only.
- Integration checkpoint:
  - fixed-data+uniqueness transfer-component projections and canonical
  orbit-debt composition seams are ground-axiom-only modulo source inputs.
  - transport-wrapped integration seam is ground-axiom-only modulo source
    inputs.
- PLAN_62 archived integration checkpoint (2026-03-04):
  - zero-arg map/hybrid uniqueness seams are now routed through
    `MoleculeResidualFixedPointUniquenessDirectSource`;
  - residual uniqueness-side blocker is concentrated at
    `molecule_residual_fixed_point_hybrid_class_collapse_source_direct`.
- PLAN_64 integration checkpoint (2026-03-04):
  - direct-seam anchor-source contracts and zero-arg cutover aliases are now
    explicit in `Molecule/Conjecture.lean`;
  - residual uniqueness-side blocker remains unchanged and still requires an
    upstream non-`molecule_h_norm` witness theorem.
