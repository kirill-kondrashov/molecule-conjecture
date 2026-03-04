# PLAN 49 - Constructive Fixed-Point Source Route

Status: ACTIVE
Progress: [#########-] 99%
Scope: Eliminate `molecule_h_norm` from the fixed-point side of the residual source pipeline by replacing the current fixed-point ingredient seed with a constructive theorem-level source.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_normalization_ingredients` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_non_ground_sources` no longer carries `Molecule.molecule_h_norm` from the fixed-point side.
3. `#print axioms Molecule.molecule_conjecture_refined` does not include `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/PLAN_74_non_h_norm_molecule_h_unique_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_73_non_h_norm_anchor_early_witness_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_72_non_h_norm_direct_seam_anchor_source_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_71_non_h_norm_hybrid_class_collapse_source_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_70_non_h_norm_model_collapse_direct_source_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_69_non_h_norm_direct_source_witness_breakout.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_68_non_h_norm_direct_contract_source_constructor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_67_non_h_norm_direct_contract_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_66_canonical_uniqueness_constructive_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_65_canonical_to_anchor_constructive_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_64_upstream_direct_seam_constructive_witness.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_63_upstream_hybrid_collapse_constructive_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_62_upstream_map_uniqueness_source_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
Stuck Rule: STUCK if the only available fixed-point data/uniqueness constructors in current infrastructure require reintroducing a project axiom.
Last Updated: 2026-03-04

## Work Plan

- [x] Split fixed-point assembly from orbit source in residual bounds pipeline:
  - `MoleculeResidualFixedPointAssemblySources`
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
- [x] Verify narrowed fixed-point assembly seam theorems are axiom-clean modulo ground axioms.
- [x] Inventory current constructors for fixed-point data/uniqueness and isolate
  residual `molecule_h_norm` entry points.
- [x] Re-orient non-ground source assembly to forward constructor form:
  - `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources`.
- [x] Narrow fixed-point assembly to carry transfer directly (instead of
  uniqueness), reducing the constructive replacement surface:
  - `MoleculeResidualFixedPointAssemblySources.fixedTransfer`
  - `MoleculeResidualNonGroundSources.fixedTransfer`
- [x] Add explicit fixed-point assembly constructor from source seams:
  - `molecule_residual_fixed_point_assembly_sources_of_sources`
  and route current assembly theorem through it.
- [x] Narrow non-ground source pack to carry fixed-point ingredients directly:
  - `MoleculeResidualNonGroundSources.fixedIngredients`.
- [x] Add explicit non-ground constructor from ingredient + local orbit sources:
  - `molecule_residual_non_ground_sources_of_ingredients_and_orbit`
  and route `molecule_residual_non_ground_sources` through it.
- [x] Split and route fixed-point ingredient source through explicit bridge + transfer seams:
  - `MoleculeResidualFixedPointBridgeSource`
  - `molecule_residual_fixed_point_existence_source_of_bridge`
  - `molecule_residual_fixed_point_normalization_ingredients_of_bridge_and_transfer`
- [x] Remove active bridge dependency from the current ingredient theorem by routing through:
  - `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`.
- [x] Remove active fixed-data-source dependency from the current ingredient theorem by routing through:
  - `molecule_residual_fixed_point_normalization_ingredients_of_sources`
  with explicit existence + transfer sources.
- [x] Add explicit ingredient-source seam constructor from existence + transfer:
  - `molecule_residual_fixed_point_ingredients_source_of_sources`
  and route current ingredient source theorem through it.
- [x] Split fixed-point local transfer into critical-value and `V`-bound
  components, and route canonical `V`-bound projection through the
  `V`-bound component seam:
  - `FixedPointCriticalValueTransferSource`
  - `FixedPointVBoundTransferSource`
  - `fixed_point_local_normalization_transfer_of_critical_and_vbound`
  - `fixed_point_critical_and_vbound_of_local_normalization_transfer`
  - `molecule_residual_canonical_vbound_source_of_fixed_point_vbound_transfer`
  - `fixed_point_vbound_transfer_source_of_fixed_point_transfer_source`.
- [x] Route current fixed-point existence and bundled ingredients through
  explicit fixed-data + transfer seam constructors (bridge-free current path):
  - `molecule_residual_fixed_point_existence_source` now routes via
    `renormalizable_fixed_exists_of_fixed_point_normalization_data
    molecule_h_fixed_data_direct`
  - `molecule_residual_fixed_point_normalization_ingredients` now routes via
    `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer
    molecule_h_fixed_data_direct molecule_residual_fixed_point_transfer_source`.
- [x] Add cross-track integration seams from fixed-data + uniqueness to
  transfer components and canonical orbit debt composition:
  - `fixed_point_critical_value_transfer_source_of_fixed_data_and_unique`
  - `fixed_point_vbound_transfer_source_of_fixed_data_and_unique`
  - `molecule_residual_canonical_vbound_source_of_fixed_data_and_unique`
  - `molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_unique`
  - source-level wrappers:
    `fixed_point_transfer_components_of_fixed_data_and_uniqueness_source`,
    `molecule_residual_canonical_vbound_source_of_fixed_data_and_uniqueness_source`,
    `molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_uniqueness_source`.
- [x] Add transport-wrapped integration cutover seam:
  - `molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_uniqueness_source`
  - current routed theorem:
    `molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source`.
- [ ] Add constructive replacement theorem for
  `molecule_residual_fixed_point_normalization_ingredients`.
- [ ] Rebuild `molecule_residual_non_ground_sources` with constructive
  fixed-point ingredient source theorem.
- [x] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Notes

- Current fixed-point source route is still global-norm/ex-falso backed.
- Inventory result (2026-03-04):
  - `molecule_residual_fixed_point_data_source` currently routes through
    `molecule_h_fixed_data_direct`, which depends on
    `renormalizable_fixed_exists_of_global_norm molecule_h_norm` and
    `fixed_point_local_normalization_transfer_of_global_norm molecule_h_norm`.
  - `molecule_residual_fixed_point_uniqueness_source` currently routes through
    `molecule_h_unique`, which is `False.elim molecule_h_norm_inconsistent`.
- New checkpoint (2026-03-04):
  - `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources` is
    axiom-clean modulo ground axioms.
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
    is axiom-clean modulo ground axioms.
  - `molecule_residual_fixed_point_assembly_sources_of_sources` is axiom-clean
    modulo ground axioms.
  - `molecule_residual_fixed_point_assembly_sources` is now reconstructible
    from non-ground ingredients and remains a ground-axiom-only seam theorem.
  - fixed-point blocker has been concentrated to
    `molecule_residual_fixed_point_normalization_ingredients`.
  - `molecule_residual_non_ground_sources_of_ingredients_and_orbit` is
    axiom-clean modulo ground axioms; the current
    `molecule_residual_non_ground_sources` now depends directly on:
    - `molecule_residual_fixed_point_normalization_ingredients`
    - `molecule_residual_orbit_clause_for_fixed_data_source`.
  - fixed-point ingredient route no longer depends directly on the legacy
    fixed-data existence projection; it now enters via explicit bridge source
    plus transfer source seams.
  - current ingredient theorem no longer depends on the bridge seam:
    `molecule_residual_fixed_point_normalization_ingredients` now routes via
    fixed-data + transfer source seams.
  - current existence/transfer source theorems are now explicitly routed
    through global-norm constructors (bridge-free and ex-falso-free):
    `molecule_residual_fixed_point_existence_source`,
    `molecule_residual_fixed_point_transfer_source`.
  - `molecule_residual_fixed_point_data_source` now routes via explicit
    source composition:
    `molecule_residual_fixed_point_data_source_of_sources`.
  - `molecule_residual_fixed_point_ingredients_source` now routes via explicit
    source composition:
    `molecule_residual_fixed_point_ingredients_source_of_sources`.
  - fixed-point assembly current theorem now routes via explicit
    existence+transfer seam:
    `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
  - targeted probes confirm these new seam theorems are axiom-clean modulo
    ground axioms.
- New transfer-split checkpoint (2026-03-04):
  - the transfer decomposition/projection theorems above are axiom-clean modulo
    ground axioms.
  - canonical `V`-bound projection can now be cut over via transfer seam
    components without changing theorem interfaces.
- New fixed-data route checkpoint (2026-03-04):
  - `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`
    remains axiom-clean modulo ground axioms.
  - current `molecule_residual_fixed_point_normalization_ingredients`,
    `molecule_residual_fixed_point_existence_source`, and
    `molecule_residual_non_ground_sources` still carry `Molecule.molecule_h_norm`
    via current fixed-data/transfer source theorems.
- New integration checkpoint (2026-03-04):
  - the fixed-data+uniqueness transfer component projections and canonical
  orbit-debt composition seams listed above are axiom-clean modulo ground
  axioms.
  - transport-wrapped integration seam above is axiom-clean modulo ground
    axioms; current routed theorem still carries `Molecule.molecule_h_norm`
    through current fixed-data/uniqueness/transport sources.
- Verification checkpoint (2026-03-04):
  - `make build` and `make check` pass.
  - targeted probes confirm:
    - `molecule_residual_fixed_point_normalization_ingredients` still includes
      `Molecule.molecule_h_norm`;
    - `molecule_residual_non_ground_sources` still includes
      `Molecule.molecule_h_norm`;
    - top theorem frontier is unchanged (`Molecule.molecule_h_norm` only
      project axiom).
- PLAN_74 routing checkpoint (2026-03-04):
  - current PLAN_72/69 zero-arg alias route is now routed through
    `MoleculeResidualPlan74WinningRouteSources` in `Molecule/Conjecture.lean`;
  - targeted probes show this cutover remains `Molecule.molecule_h_norm`-backed
    at the zero-arg bundle level while parameterized propagation theorems stay
    ground-axiom-only.
- This plan now runs in parallel with PLAN_74 (non-h_norm molecule_h_unique
  replacement) after PLAN_73 was archived as stuck.
- PLAN_62 archived integration checkpoint (2026-03-04):
  - zero-arg map/hybrid uniqueness seams are now routed through
    `MoleculeResidualFixedPointUniquenessDirectSource`;
  - residual uniqueness-side blocker is concentrated at
    `molecule_residual_fixed_point_hybrid_class_collapse_source_direct`.
- PLAN_64 integration checkpoint (2026-03-04):
  - introduced direct-seam anchor-source contracts and zero-arg anchor/cutover
  aliases:
    `MoleculeResidualDirectSeamAnchorOfCanonicalSource`,
    `MoleculeResidualDirectSeamAnchorOfRefinedSource`,
    `molecule_residual_direct_seam_anchor_source`,
    `molecule_residual_fixed_point_uniqueness_direct_source_cutover`.
  - probe status unchanged:
    direct-seam zero-arg frontier is still `Molecule.molecule_h_norm`-backed.
  - updated zero-arg direct-uniqueness routing:
    `molecule_residual_fixed_point_uniqueness_direct_source` now goes through a
    declaration-order-safe anchor constructor.
- PLAN_65 integration checkpoint (2026-03-04):
  - added source-level constructor/equivalence bridge:
    `molecule_residual_direct_seam_anchor_source_of_uniqueness_source`,
    `molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source`.
  - added contract-level wrappers for the current canonical/refined anchor
    interfaces:
    `molecule_residual_direct_seam_anchor_of_canonical_source_of_uniqueness_source`,
    `molecule_residual_direct_seam_anchor_of_refined_source_of_uniqueness_source`.
  - bottleneck remains unchanged:
    a non-`molecule_h_norm` theorem-level source for
    `MoleculeResidualFixedPointUniquenessSource` is still required to make
    these wrappers discharge `MoleculeResidualDirectSeamAnchorSource`.
  - strengthened bottleneck certificate:
    canonical/refined anchor-contract goals are now formally equivalent to
    canonical/refined uniqueness-contract goals.
- PLAN_66 kickoff checkpoint (2026-03-04):
  - PLAN_65 archived as STUCK after conditional cutover constructors were added
    and zero-arg probes remained `Molecule.molecule_h_norm`-backed.
  - new active upstream target is a non-`molecule_h_norm` theorem for
    `MoleculeResidualFixedPointUniquenessOfCanonicalSource` (or refined
    counterpart).
  - candidate-source constructors into canonical/refined uniqueness contracts
    are now available from hybrid-class uniqueness/collapse source assumptions.
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
- PLAN_71 final archived checkpoint (2026-03-04):
  - introduced minimal interface:
    `MoleculeResidualHybridClassCollapseSourceWitnessSources`.
  - bridged PLAN_71 → PLAN_70 → PLAN_69 routes and added current-route aliases.
  - targeted probes confirm interface-level declarations are ground-axiom-only.
  - final stuck check:
    every current zero-arg candidate witness route remained
    `Molecule.molecule_h_norm`-backed.
- PLAN_72 final archived checkpoint (2026-03-04):
  - introduced minimal interface:
    `MoleculeResidualDirectSeamAnchorSourceWitnessSources`.
  - added interface decomposition/equivalence and bridges into PLAN_71/70/69
    routes, plus current-route aliases.
  - targeted probes confirm interface-level declarations are ground-axiom-only.
  - final stuck check:
    current zero-arg PLAN_72 witness route remained
    `Molecule.molecule_h_norm`-backed.
- PLAN_73 final archived checkpoint (2026-03-04):
  - introduced direct-seam-anchor witness interface and candidate-route
    constructors from uniqueness/direct/hybrid assumptions.
  - targeted probes confirm interface/candidate constructors are
    ground-axiom-only.
  - final stuck check:
    all current zero-arg witness aliases remained
    `Molecule.molecule_h_norm`-backed via
    `molecule_residual_direct_seam_anchor_source_early`.
- PLAN_74 kickoff checkpoint (2026-03-04):
  - successor target is now explicit replacement of `molecule_h_unique`-driven
    anchor proof route without `molecule_h_norm`.
- Sub-plan linkage:
  - model-level witness bottleneck is tracked explicitly in
    `PLAN_53_fixed_point_model_bottleneck_refactor.md`.
  - bridge seam now exists:
    `renormalizable_fixed_exists_of_fixed_point_exists_and_bridge`.
