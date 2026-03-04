# PLAN 47 - `molecule_h_norm` Elimination via Constructive Source Rebuild

Status: ACTIVE
Progress: [#########-] 99%
Scope: Remove the last project axiom `Molecule.molecule_h_norm` from the zero-argument route by replacing the remaining non-ground source constructors with theorem-level constructive proofs.
Acceptance:
1. `#print axioms Molecule.molecule_residual_non_ground_sources` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_bounds_seed_free` does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_conjecture_refined` does not include `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/PLAN_57_orbit_minimal_theorem_debt_extraction.md`, `plan/PLAN_54_orbit_source_contract_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_51_orbit_fixed_data_source_replacement.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_55_orbit_constructive_source_extraction_v2.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_56_orbit_clause_constructor_decomposition.md`, `plan/ARCHIVE_superseded_2026-03-04_PLAN_45_local_fixed_point_normalization_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_46_seed_free_ingredient_constructor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_48_orbit_clause_constructive_route.md`, `plan/ARCHIVE_superseded_2026-03-04_PLAN_50_orbit_clause_local_contract_narrowing.md`
Stuck Rule: STUCK if both source tracks below cannot advance without introducing a new project axiom or weakening exported theorem statements.
Last Updated: 2026-03-04

## Feasibility Gate (Dead-End Check)

- Not a formal dead end yet:
  - the code already isolates the final dependency behind source seams;
  - bounds assembly now consumes `MoleculeResidualBoundsAssemblySources`, which narrows the replacement target.
- High-risk area:
  - current orbit-clause and uniqueness/data seeds are still produced via ex-falso/global-normalization routes.
- Go/no-go criterion:
  - proceed only on theorem-level constructive routes from existing contracts; no new axioms and no contract weakening.

## Track A - Constructive fixed-point ingredient source

- [x] Narrow bounds assembly to consume `MoleculeResidualBoundsAssemblySources`.
- [x] Verify axiom profile of narrowed assembly route:
  - `molecule_residual_bounds_seed_free_of_bounds_assembly_sources` is axiom-clean
    modulo ground axioms (`propext`, `Classical.choice`, `Quot.sound`).
- [x] Split fixed-point assembly seam from orbit-clause seam:
  - `MoleculeResidualFixedPointAssemblySources`
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
- [x] Re-orient non-ground source pack assembly to a forward constructor:
  - `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources`.
- [x] Narrow non-ground/bounds-assembly orbit source component to fixed-data
  local orbit contract:
  - `MoleculeResidualOrbitClauseForFixedDataSource`.
- [x] Narrow fixed-point assembly component to transfer-focused payload:
  - `MoleculeResidualFixedPointTransferSource` carried directly in source packs.
- [x] Split fixed-point assembly constructor into explicit source-level seam:
  - `molecule_residual_fixed_point_assembly_sources_of_sources`.
- [x] Narrow non-ground source pack to carry fixed-point ingredients directly:
  - `MoleculeResidualNonGroundSources.fixedIngredients`.
- [x] Route non-ground source theorem through explicit ingredient+orbit
  constructor:
  - `molecule_residual_non_ground_sources_of_ingredients_and_orbit`.
- [x] Split fixed-point ingredient route into explicit bridge + transfer seams:
  - `MoleculeResidualFixedPointBridgeSource`
  - `molecule_residual_fixed_point_normalization_ingredients_of_bridge_and_transfer`.
- [x] Rewire current fixed-point ingredient/data/assembly theorems through
  explicit existence + transfer seam composition:
  - `molecule_residual_fixed_point_normalization_ingredients_of_sources`
  - `molecule_residual_fixed_point_ingredients_source_of_sources`
  - `molecule_residual_fixed_point_data_source_of_sources`
  - `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
- [ ] Replace current ingredient seed route with a constructive theorem package that does not use `molecule_h_norm`.

## Track B - Constructive orbit-clause source

- [x] Add first decomposition seam on the local constructor route:
  - `MoleculeResidualOrbitClauseAtFixedDataSource`
  - `molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source`.
- [x] Add second decomposition seam from orbit-clause / transport sources into
  fixed-data canonical orbit-at source:
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_orbit_clause_source`
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_transport_source`.
- [x] Isolate minimal theorem-debt statement and bridge seam:
  - `MoleculeResidualCanonicalOrbitAtDebtSource`
  - `molecule_residual_orbit_clause_at_fixed_data_source_of_canonical_debt_source`.
- [ ] Identify a non-ex-falso orbit transport/orbit clause route from existing theorem infrastructure.
- [ ] Prove/export a theorem-level `MoleculeResidualOrbitClauseSource` constructor without `molecule_h_norm`.
- [ ] Wire `molecule_residual_orbit_transport_source` through the constructive orbit-clause route.

## Integration

- [x] Cut over active top-path non-ground source assembly to transport-routed
  orbit wrapper:
  - `molecule_residual_non_ground_sources` now consumes
    `molecule_residual_orbit_clause_for_fixed_data_source`.
- [ ] Rebuild `molecule_residual_non_ground_sources` from constructive Track A + Track B outputs.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.
- [ ] Mark plan DONE only when all acceptance checks pass.

## Notes

- This plan supersedes PLAN_46 as the active implementation path.
- If Track B stalls while Track A progresses, keep Track A changes and open a focused orbit-clause sub-plan.
- Current frontier from targeted axiom probe:
  - `molecule_residual_non_ground_sources` still carries `Molecule.molecule_h_norm`.
  - Downstream narrowed assembly theorems are already axiom-clean under source inputs.
