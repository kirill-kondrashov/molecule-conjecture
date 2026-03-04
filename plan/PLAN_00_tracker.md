# PLAN 00 - Molecule Hypothesis Elimination Tracker

Status: ACTIVE
Progress: [#########-] 97%
Scope: Track hypothesis-elimination plans, dependencies, blockers, and readiness.
Acceptance: Active plans are current; completed plans are marked DONE; blocker status reflects `check_axioms`.
Dependencies: PLAN_11, PLAN_12, PLAN_15, PLAN_17, PLAN_18, PLAN_20, PLAN_21, PLAN_22, PLAN_23, PLAN_24, PLAN_25, PLAN_26, PLAN_27, PLAN_28, PLAN_29, PLAN_30, PLAN_31, PLAN_32, PLAN_33, PLAN_34, PLAN_35, PLAN_36, PLAN_37, PLAN_38, PLAN_39, PLAN_40, PLAN_41, PLAN_42, PLAN_43, PLAN_47, PLAN_49, PLAN_50
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
| PLAN_47 | `molecule_h_norm` elimination via constructive source rebuild | ACTIVE | [######----] 60% |
| PLAN_49 | Constructive fixed-point source route | ACTIVE | [####------] 45% |
| PLAN_50 | Orbit-clause local contract narrowing | ACTIVE | [########--] 80% |

## Dependency Map

- Primary elimination path PLAN_34/37/40/41 is complete.
- Current queue is PLAN_47 (integration) + PLAN_49 (fixed-point source track) + PLAN_50 (orbit local-contract track), then PLAN_43.
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
  - Current fixed-point blocker is concentrated at:
    `molecule_residual_fixed_point_assembly_sources`.
  - Next target is constructive replacement of:
    `molecule_residual_fixed_point_data_source` and
    `molecule_residual_fixed_point_uniqueness_source`.
- `PLAN_50` progress:
  - Replaced stalled global-only orbit route with a local-contract narrowing route.
  - Introduced local seam primitives:
    `MoleculeOrbitClauseAt` and `molecule_orbit_clause_at_of_orbit_clause`.
  - Added local-source routing seam:
    `MoleculeResidualOrbitClauseAtSource`,
    `molecule_residual_orbit_clause_source_of_local`,
    and rewired `molecule_residual_orbit_clause_source` through that seam.
  - Added fixed-data-local orbit source contract and constructor:
    `MoleculeResidualOrbitClauseForFixedDataSource`,
    `molecule_residual_orbit_clause_for_fixed_data_source_of_local`.
  - Rewired residual bounds assembly through local-orbit conversion path:
    `molecule_residual_bounds_from_fixed_data_and_local_orbit_source`,
    with `molecule_residual_bounds_seed_free_of_bounds_assembly_sources` now
    consuming the local-orbit contract route.
  - Narrowed non-ground and bounds-assembly source packs to carry fixed-data
    local orbit source directly.
  - Verified local seam and source-constructor theorem axiom profiles are
    ground-only; the current local witness theorem remains `molecule_h_norm`-backed.
  - Next target is wiring local orbit obligations into residual constructors so
    `molecule_residual_orbit_clause_source` can be rebuilt non-circularly.

## Current Critical Blockers

1. Root blocker: `Molecule.molecule_h_norm` remains in the zero-arg theorem path.
2. Active mitigation: PLAN_47 integration track, PLAN_49 fixed-point source track, PLAN_50 orbit local-contract track.
