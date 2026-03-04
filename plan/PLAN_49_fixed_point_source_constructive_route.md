# PLAN 49 - Constructive Fixed-Point Source Route

Status: ACTIVE
Progress: [#########-] 99%
Scope: Eliminate `molecule_h_norm` from the fixed-point side of the residual source pipeline by replacing the current fixed-point ingredient seed with a constructive theorem-level source.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_normalization_ingredients` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_non_ground_sources` no longer carries `Molecule.molecule_h_norm` from the fixed-point side.
3. `#print axioms Molecule.molecule_conjecture_refined` does not include `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
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
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

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
- This plan now runs in parallel with PLAN_59 (hybrid unique fixed-point source constructor route) after PLAN_57 completion.
- Sub-plan linkage:
  - model-level witness bottleneck is tracked explicitly in
    `PLAN_53_fixed_point_model_bottleneck_refactor.md`.
  - bridge seam now exists:
    `renormalizable_fixed_exists_of_fixed_point_exists_and_bridge`.
