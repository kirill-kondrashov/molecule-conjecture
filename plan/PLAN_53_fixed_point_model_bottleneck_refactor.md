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
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FixedPointExistence.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationTheorem.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_71_non_h_norm_hybrid_class_collapse_source_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_70_non_h_norm_model_collapse_direct_source_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_69_non_h_norm_direct_source_witness_breakout.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_68_non_h_norm_direct_contract_source_constructor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_67_non_h_norm_direct_contract_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_66_canonical_uniqueness_constructive_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_65_canonical_to_anchor_constructive_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_64_upstream_direct_seam_constructive_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_63_upstream_hybrid_collapse_constructive_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_62_upstream_map_uniqueness_source_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_61_upstream_hybrid_class_uniqueness_source_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_60_hybrid_class_model_refactor_route.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_59_hybrid_unique_fixed_point_source_constructor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
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
  - zero-arg direct uniqueness now routes through a declaration-order-safe
    anchor constructor;
  - residual uniqueness-side blocker remains unchanged and still requires an
    upstream non-`molecule_h_norm` witness theorem.
- PLAN_65 integration checkpoint (2026-03-04):
  - source-level anchor/uniqueness equivalence is now explicit in
    `Molecule/Conjecture.lean` via
    `molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source`;
  - canonical/refined anchor contracts now have non-circular wrappers from a
    uniqueness source theorem;
  - canonical/refined anchor-contract goals are now explicitly equivalent to
    canonical/refined uniqueness-contract goals;
  - the model bottleneck is unchanged: a non-`molecule_h_norm` uniqueness
    source theorem is still the upstream requirement.
- PLAN_66 kickoff checkpoint (2026-03-04):
  - PLAN_65 archived as STUCK after conditional cutover layer completion.
  - active bottleneck is now isolated exactly at canonical/refined uniqueness
    theorem construction, with no remaining seam rearrangement debt.
  - candidate-source constructors into canonical/refined uniqueness contracts
    now exist from hybrid-class uniqueness/collapse source assumptions.
  - canonical/refined uniqueness contracts are now explicitly equivalent to
    canonical/refined hybrid-class-uniqueness contracts.
  - canonical/refined uniqueness contracts are now explicitly equivalent to
    canonical/refined hybrid-class-uniqueness model-collapse contracts.
  - canonical/refined uniqueness contracts are now explicitly equivalent to
    canonical/refined model-collapse-direct contracts, and canonical/refined
    anchor contracts are explicitly equivalent to those direct contracts.
  - canonical/refined constructor routes from model-collapse-direct contracts
    into anchor/direct seams are now explicit.
  - canonical/refined map-level uniqueness contracts are now explicitly
    equivalent to canonical/refined map-level direct-uniqueness contracts, with
    matching anchor-contract equivalences and constructor routes.
- PLAN_67 final archived checkpoint (2026-03-04):
  - wrapper/equivalence reductions completed, including order-safe
    direct-contract wrappers.
  - targeted probes confirmed wrapper layer is ground-axiom-only.
  - bottleneck unchanged: canonical/refined direct-contract theorems remained
    `Molecule.molecule_h_norm`-backed.
- PLAN_68 final archived checkpoint (2026-03-04):
  - added direct-contract cutover-source seam in `Molecule/Conjecture.lean`:
    `MoleculeResidualDirectContractCutoverSources` and its direct/anchor
    constructor routes from canonical/refined direct-contract assumptions.
  - targeted probes confirm the new cutover-source seam is ground-axiom-only;
    current canonical/refined direct-contract theorems remain
    `Molecule.molecule_h_norm`-backed.
  - added source-pack-to-contract constructors:
    `molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_direct_contract_cutover_sources`,
    `molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_direct_contract_cutover_sources`,
    both ground-axiom-only in targeted probes.
  - added obstruction-equivalence theorems:
    `molecule_residual_direct_contract_cutover_sources_iff_fixed_point_uniqueness_direct_source_of_canonical`,
    `molecule_residual_direct_contract_cutover_sources_iff_fixed_point_uniqueness_direct_source_of_refined`,
    showing this path still collapses to the current direct-source frontier.
- PLAN_69 final archived checkpoint (2026-03-04):
  - selected upstream candidate seam:
    `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`
    with canonical data.
  - added breakout-source interface and constructors:
    `MoleculeResidualDirectSourceBreakoutSources`,
    `molecule_residual_fixed_point_uniqueness_direct_source_of_direct_source_breakout_sources`,
    `molecule_residual_direct_seam_anchor_source_of_direct_source_breakout_sources`.
  - targeted probes confirm the new breakout-source declarations are
    ground-axiom-only.
  - this yields a non-`molecule_h_norm` direct-source witness theorem under the
    breakout interface.
  - added breakout equivalence/cutover layer, but current zero-arg breakout
    route remained `Molecule.molecule_h_norm`-backed through the current
    model-collapse-direct source theorem.
- PLAN_70 final archived checkpoint (2026-03-04):
  - introduced minimal interface:
    `MoleculeResidualModelCollapseDirectSourceWitnessSources`.
  - expanded interface/candidate decomposition and routed breakout-source
    assembly through this interface.
  - targeted probes confirm interface-level declarations are ground-axiom-only.
  - final stuck check:
    every current zero-arg candidate witness route remained
    `Molecule.molecule_h_norm`-backed.
- PLAN_71 kickoff checkpoint (2026-03-04):
  - active bottleneck is now upstream replacement of
    `MoleculeResidualFixedPointHybridClassCollapseSource` without
    `molecule_h_norm`.
  - introduced minimal interface:
    `MoleculeResidualHybridClassCollapseSourceWitnessSources`.
  - bridged PLAN_71 → PLAN_70 → PLAN_69 routes and added current-route aliases
    through the new interface.
  - targeted probes confirm interface-level declarations are ground-axiom-only,
    while current zero-arg PLAN_71 witness route remains
    `Molecule.molecule_h_norm`-backed.
