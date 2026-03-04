# PLAN 00 - Molecule Hypothesis Elimination Tracker

Status: ACTIVE
Progress: [#########-] 99%
Scope: Track hypothesis-elimination plans, dependencies, blockers, and readiness.
Acceptance: Active plans are current; completed plans are marked DONE; blocker status reflects `check_axioms`.
Dependencies: PLAN_11, PLAN_12, PLAN_15, PLAN_17, PLAN_18, PLAN_20, PLAN_21, PLAN_22, PLAN_23, PLAN_24, PLAN_25, PLAN_26, PLAN_27, PLAN_28, PLAN_29, PLAN_30, PLAN_31, PLAN_32, PLAN_33, PLAN_34, PLAN_35, PLAN_36, PLAN_37, PLAN_38, PLAN_39, PLAN_40, PLAN_41, PLAN_42, PLAN_43, PLAN_47, PLAN_49, PLAN_53, PLAN_54, PLAN_56
Stuck Rule: STUCK if PLAN_26 becomes STUCK without an alternative decomposition route.
Last Updated: 2026-03-04

## Plan Matrix

| Plan | Target Hypotheses | Status | Progress |
|---|---|---|---|
| PLAN_06 | Contract consistency refactor | DONE | [##########] 100% |
| PLAN_07 | De-wrapper pseudo-Siegel/orbit | DONE | [##########] 100% |
| PLAN_11 | Full `molecule_h_*` axiom burndown | DONE | [##########] 100% |
| PLAN_12 | h_exists/h_norm localization | DONE | [##########] 100% |
| PLAN_13 | h_orbit non-circular path | DONE | [##########] 100% |
| PLAN_15 | Replace global h_norm contract | DONE | [##########] 100% |
| PLAN_17 | Signature migration to local norm | DONE | [##########] 100% |
| PLAN_18 | Global norm signature cutover | DONE | [##########] 100% |
| PLAN_20 | Problem4_3 local norm cutover | DONE | [##########] 100% |
| PLAN_21 | Axiom audit driven refactor | DONE | [##########] 100% |
| PLAN_22 | Hyperbolicity local fixed-point cutover | DONE | [##########] 100% |
| PLAN_23 | Zero-arg theorem de-ex-falso | DONE | [##########] 100% |
| PLAN_24 | Root h_norm axiom exit strategy | DONE | [##########] 100% |
| PLAN_25 | Core assumption decomposition | DONE | [##########] 100% |
| PLAN_26 | Decomposed core axiom burndown | DONE | [##########] 100% |
| PLAN_27 | Local fixed-point data witness construction | DONE | [##########] 100% |
| PLAN_28 | Local fixed-point seed burndown | DONE | [##########] 100% |
| PLAN_29 | Core axiom interface partition | DONE | [##########] 100% |
| PLAN_30 | Analytic core wrapper burndown | DONE | [##########] 100% |
| PLAN_31 | Combinatorial core wrapper burndown | DONE | [##########] 100% |
| PLAN_32 | Unified local seed elimination | DONE | [##########] 100% |
| PLAN_33 | Final wrapper burndown sequence | DONE | [##########] 100% |
| PLAN_34 | Final axiom elimination | DONE | [##########] 100% |
| PLAN_35 | Final axiom component source search | DONE | [##########] 100% |
| PLAN_36 | Final axiom irreducibility certificate | DONE | [##########] 100% |
| PLAN_37 | Residual component attack queue | DONE | [##########] 100% |
| PLAN_38 | Combinatorial model realignment | DONE | [##########] 100% |
| PLAN_39 | HMol compactness model alignment | DONE | [##########] 100% |
| PLAN_40 | Analytic residual triple elimination | DONE | [##########] 100% |
| PLAN_41 | Residual bounds elimination | DONE | [##########] 100% |
| PLAN_42 | Post-axiom contract hardening | DONE | [##########] 100% |
| PLAN_43 | Post-cutover hygiene pass | PROPOSED | [----------] 0% |
| PLAN_47 | `molecule_h_norm` elimination via constructive source rebuild | ACTIVE | [#########-] 99% |
| PLAN_49 | Constructive fixed-point source route | ACTIVE | [#########-] 99% |
| PLAN_53 | Fixed-point model bottleneck refactor | ACTIVE | [########--] 80% |
| PLAN_54 | Orbit source contract refactor | DONE | [##########] 100% |
| PLAN_56 | Orbit clause constructor decomposition | ACTIVE | [##--------] 20% |

## Dependency Map

- Primary elimination path PLAN_34/37/40/41 is complete.
- Current queue is PLAN_47 (integration) + PLAN_49 (fixed-point source track) + PLAN_53 (model bottleneck refactor) + PLAN_56 (orbit constructor decomposition), then PLAN_43.
- Legacy `molecule_h_*` elimination path (PLAN_11/15/17/21/24) is complete.

## Current Notes

- `check_axioms` for `Molecule.molecule_conjecture_refined` currently reports:
  - `Molecule.molecule_h_norm`
- The previous placeholder `PseudoSiegelAPrioriBounds := True` has been replaced by
  `PseudoSiegelAPrioriBoundsStatement`, and bounds/canonical extraction now consume
  this stronger contract.
- `molecule_residual_bounds` has been rewired to a seed-free source path
  (`molecule_residual_bounds_seed_free`) that no longer uses `molecule_h_data`.
- New obstruction theorem in `Molecule/Conjecture.lean`:
  `has_invariant_slice_data_forces_univ_finite`, exposing the current
  constant-chart/finiteness mismatch that blocks constructive `h_exists`.
- New feasibility gate theorems in `Molecule/Conjecture.lean`:
  - `global_normalization_contract_inconsistent`
  - `no_global_normalization_contract`
  These certify the current global-normalization seam is inconsistent in this model.
- `PLAN_44` has started with refined chart scaffolding in `Molecule/BanachSlice.lean`
  (`slice_chart_refined`, `refined_singleton_slice_witness`), and a new
  chart-parameterized package in `Molecule/Conjecture.lean`
  (`HasInvariantSliceDataWith`, `has_invariant_slice_data_with_refined`,
  `has_invariant_slice_data_with_refined_default`,
  `InvariantSliceDataWithNormalizationWith`,
  `invariant_slice_data_with_normalization_with_refined_of_local`,
  `invariant_slice_data_with_normalization_with_refined_of_global_norm`), plus
  global-to-local normalization bridges
  (`normalization_at_point_of_global`,
  `fixed_point_normalization_data_of_fixed_exists_and_global_norm`) and a
  narrowed bounds interface
  (`problem_4_3_bounds_established_conjecture_from_fixed_exists_and_global_norm`,
  `molecule_residual_fixed_exists`, `problem_4_3_bounds_established_conjecture_from_local_fixed_norm`,
  `MoleculeOrbitTransportData`,
  `problem_4_3_bounds_established_conjecture_from_global_norm_and_transport`,
  `MoleculeOrbitClause`,
  `MoleculeOrbitOnlyData`,
  `molecule_orbit_transport_data_of_orbit_only`).
  `molecule_residual_fixed_exists` is now routed through
  `renormalizable_fixed_exists_of_fixed_point_normalization_data`.
  `molecule_h_fixed_data` is now routed through the explicit source seam
  `molecule_residual_fixed_point_normalization_source`.
- Archived STUCK plan:
  - `ARCHIVE_stuck_2026-03-04_PLAN_44_constructive_slice_witness_refactor.md`
    (replaced by PLAN_45).
- Archived SUPERSEDED plan:
  - `ARCHIVE_superseded_2026-03-04_PLAN_45_local_fixed_point_normalization_source.md`
    (handoff to PLAN_47/49).
- `PLAN_45` delivered:
  - Added local bounds seam
    `problem_4_3_bounds_established_conjecture_from_fixed_data_and_transport`.
  - Rewired `molecule_residual_bounds_seed_free` through
    `molecule_residual_bounds_from_fixed_data` using `molecule_h_fixed_data`.
  - Rewired `molecule_residual_fixed_exists` through
    `renormalizable_fixed_exists_of_fixed_point_normalization_data`.
  - Isolated the last blocker behind one explicit replacement seam:
    `molecule_residual_fixed_point_normalization_source`.
  - Removed unused wrapper `molecule_h_data_refined_seed_free`; residual
    blocker surface is now concentrated at the fixed-data source seam.
  - Factored the fixed-data source into explicit sub-contracts:
    `FixedPointLocalNormalizationTransfer` and
    `fixed_point_normalization_data_of_fixed_exists_and_transfer`.
  - Added an explicit ingredient bundle seam:
    `MoleculeResidualFixedPointNormalizationIngredients` and
    `molecule_residual_fixed_point_normalization_ingredients`.
  - Verification rerun completed (`make build`, `make check`, `#print axioms`);
    frontier unchanged: `molecule_h_norm` is still the residual blocker.
- Archived STUCK plan:
  - `ARCHIVE_stuck_2026-03-04_PLAN_46_seed_free_ingredient_constructor.md`
    (superseded by PLAN_47).
- Archived STUCK plan:
  - `ARCHIVE_stuck_2026-03-04_PLAN_48_orbit_clause_constructive_route.md`
    (superseded by PLAN_50).
- Archived SUPERSEDED plan:
  - `ARCHIVE_superseded_2026-03-04_PLAN_50_orbit_clause_local_contract_narrowing.md`
    (superseded by PLAN_51).
- Archived STUCK plan:
  - `ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
    (superseded by PLAN_53 after bridge infeasibility gate).
- Archived STUCK plan:
  - `ARCHIVE_stuck_2026-03-04_PLAN_51_orbit_fixed_data_source_replacement.md`
    (superseded by PLAN_54 orbit source contract refactor).
- Archived STUCK plan:
  - `ARCHIVE_stuck_2026-03-04_PLAN_55_orbit_constructive_source_extraction_v2.md`
    (superseded by PLAN_56 decomposition track).
- `PLAN_47` progress:
  - Introduced narrowed residual bounds-assembly source pack in
    `Molecule/Conjecture.lean`:
    `MoleculeResidualBoundsAssemblySources`.
  - Added bridge theorem:
    `molecule_residual_bounds_assembly_sources_of_non_ground_sources`.
  - Added current narrowed source constructor:
    `molecule_residual_bounds_assembly_sources`.
  - Rewired `molecule_residual_bounds_seed_free` through
    `molecule_residual_bounds_seed_free_of_bounds_assembly_sources`.
  - Split fixed-point assembly path from orbit-clause path via:
    `MoleculeResidualFixedPointAssemblySources` and
    `molecule_residual_bounds_assembly_sources_of_fixed_point_and_orbit_sources`.
  - Re-oriented non-ground source assembly to forward constructor form:
    `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources`.
  - Narrowed orbit source component in non-ground/bounds-assembly packs to
    fixed-data local orbit contract:
    `MoleculeResidualOrbitClauseForFixedDataSource`.
  - Narrowed fixed-point component in non-ground/bounds-assembly packs to carry
    fixed-point transfer source directly.
  - Split fixed-point assembly constructor to explicit source-level seam:
    `molecule_residual_fixed_point_assembly_sources_of_sources`.
  - Narrowed non-ground source pack to carry fixed-point ingredients directly.
  - Routed non-ground source theorem through explicit ingredient+orbit
    constructor:
    `molecule_residual_non_ground_sources_of_ingredients_and_orbit`.
  - Split fixed-point ingredient route into explicit bridge + transfer seams
    and routed ingredient assembly through that path.
  - Rewired current fixed-point ingredient/data/assembly theorems through
    explicit existence + transfer seam composition:
    `molecule_residual_fixed_point_normalization_ingredients_of_sources`,
    `molecule_residual_fixed_point_ingredients_source_of_sources`,
    `molecule_residual_fixed_point_data_source_of_sources`,
    `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
  - Cut over active top-path non-ground source assembly to transport-routed
    orbit wrapper:
    `molecule_residual_non_ground_sources` now consumes
    `molecule_residual_orbit_clause_for_fixed_data_source`.
  - Added local orbit-obligation seam in `Molecule/Conjecture.lean`:
    `MoleculeOrbitClauseAt` and
    `molecule_orbit_clause_at_of_orbit_clause`.
  - Targeted axiom probe confirms:
    `molecule_residual_bounds_seed_free_of_bounds_assembly_sources` and
    `molecule_residual_bounds_seed_free_of_non_ground_sources` are axiom-clean
    modulo ground axioms; only
    `molecule_residual_non_ground_sources` still carries `molecule_h_norm`.
  - Residual blocker remains concentrated in constructive replacement of:
    - ingredient source route, and
    - orbit-clause source route.
- `PLAN_49` progress:
  - Added fixed-point-only assembly seam and bridge theorems:
    `molecule_residual_fixed_point_assembly_sources_of_non_ground_sources`,
    `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`.
  - Targeted axiom probe confirms these fixed-point assembly seam theorems are
    axiom-clean modulo ground axioms.
  - Completed constructor inventory for fixed-point source route:
    `molecule_residual_fixed_point_data_source` is currently global-norm backed,
    and `molecule_residual_fixed_point_uniqueness_source` is currently ex-falso.
  - Added forward constructor seam checkpoint:
    `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources`
    is axiom-clean modulo ground axioms.
  - Narrowed fixed-point source packs to carry transfer directly (instead of
    uniqueness), reducing replacement surface.
  - Added and routed through explicit source-level fixed-point assembly
    constructor:
    `molecule_residual_fixed_point_assembly_sources_of_sources`.
  - Narrowed non-ground source pack to carry fixed-point ingredients directly,
    concentrating the fixed-point blocker at ingredient source construction.
  - Added explicit non-ground constructor from ingredient + local-orbit
    sources and routed `molecule_residual_non_ground_sources` through it.
  - Added explicit fixed-point bridge source seam and routed fixed-point
    existence/ingredient assembly through bridge + transfer seams.
  - Verified
    `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
    remains axiom-clean modulo ground axioms after the refactor.
  - Current fixed-point blocker is concentrated at:
    `molecule_residual_fixed_point_normalization_ingredients`.
  - Current ingredient theorem now routes through fixed-data + transfer seam:
    `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`,
    removing active dependence on `FixedPointImpliesRenormalizable`.
  - Current existence/transfer source theorems are bridge-free and ex-falso-free:
    `molecule_residual_fixed_point_existence_source`,
    `molecule_residual_fixed_point_transfer_source`.
  - Current fixed-point data source theorem now routes via explicit source
    composition:
    `molecule_residual_fixed_point_data_source_of_sources`.
  - Current fixed-point ingredient source theorem now routes via explicit
    source composition:
    `molecule_residual_fixed_point_ingredients_source_of_sources`.
  - Current fixed-point assembly source theorem now routes via explicit
    existence+transfer seam:
    `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
  - Next target is constructive replacement of:
    `molecule_residual_fixed_point_normalization_ingredients`.
- `PLAN_53` progress:
  - Opened replacement track for the fixed-point witness bottleneck after
    proving infeasibility gate:
    `no_fixed_point_implies_renormalizable`.
  - Added bridge-free ingredient routing checkpoint:
    `molecule_residual_fixed_point_normalization_ingredients` now routes through
    `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`.
  - Decoupled current existence/transfer source theorems from bridge+uniqueness
    routing:
    `molecule_residual_fixed_point_existence_source`,
    `molecule_residual_fixed_point_transfer_source`.
  - Decoupled current fixed-point data/assembly source theorems from one-off
    fixed-data seed routing:
    `molecule_residual_fixed_point_data_source_of_sources`,
    `molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer`.
  - Decoupled current fixed-point ingredient source theorem from direct
    normalization theorem dependency:
    `molecule_residual_fixed_point_ingredients_source_of_sources`.
  - Targeted probe confirms
    `molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer`
    is axiom-clean modulo ground axioms.
  - Next target is constructive replacement of
    `molecule_residual_fixed_point_data_source`.
- `PLAN_54` progress:
  - Opened replacement orbit-side track after archiving PLAN_51 as stuck.
  - Added localized residual-bounds wrapper seam:
    `molecule_residual_bounds_from_fixed_data_localized`.
  - Rewired `molecule_residual_bounds_from_fixed_data` to consume the local
    fixed-data orbit source route (no direct transport theorem dependency).
  - Added explicit orbit-source composition seam theorems:
    `molecule_residual_orbit_clause_for_fixed_data_source_of_orbit_clause_source`,
    `molecule_residual_orbit_clause_for_fixed_data_source_of_transport_source`.
  - Targeted probe confirms
    `molecule_residual_orbit_clause_for_fixed_data_source_of_orbit_clause_source`,
    `molecule_residual_orbit_clause_for_fixed_data_source_of_transport_source`,
    `molecule_residual_bounds_from_fixed_data_localized`,
    and `molecule_residual_bounds_from_fixed_data_and_local_orbit_source`
    are axiom-clean modulo ground axioms.
  - Cut over the active top-path non-ground source assembly:
    `molecule_residual_non_ground_sources` now consumes
    `molecule_residual_orbit_clause_for_fixed_data_source`.
  - Completed declaration-order cleanup:
    `molecule_residual_orbit_clause_for_fixed_data_source` now routes through
    the transport-source composition theorem directly.
  - Probe checkpoint:
    `molecule_residual_bounds_from_fixed_data_localized` is axiom-clean modulo
    ground axioms, while `molecule_residual_bounds_from_fixed_data` now carries
    `Molecule.molecule_h_norm` only via the current orbit source theorem.
  - Plan outcome: done; single canonical orbit-source theorem name retained.
- `PLAN_56` progress:
  - Opened decomposition-first replacement track after PLAN_55 was archived as
    stuck.
  - Baseline remains the PLAN_54 canonicalized single-frontier route:
    `molecule_residual_orbit_clause_for_fixed_data_source`.
  - Next target is the first decomposition seam theorem that reduces constructor
    input contracts below the full global orbit clause.

## Current Critical Blockers

1. Root blocker: `Molecule.molecule_h_norm` remains in the zero-arg theorem path.
2. Active mitigation: PLAN_47 integration track, PLAN_49 fixed-point source track, PLAN_53 model bottleneck track, PLAN_56 orbit decomposition track.
