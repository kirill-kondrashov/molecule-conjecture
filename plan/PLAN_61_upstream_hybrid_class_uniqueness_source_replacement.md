# PLAN 61 - Upstream Hybrid-Class Uniqueness Source Replacement

Status: ACTIVE
Progress: [###-------] 30%
Scope: Replace `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct` with a non-`molecule_h_norm` theorem-level source produced upstream, then cut that source through the model-collapse/model-source path.
Acceptance:
1. `#print axioms Molecule.molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source` does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_hybrid_unique_fixed_point_source` does not include `Molecule.molecule_h_norm` through the class-uniqueness branch.
4. `make build`, `make check`, and targeted probe matrix pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_60_hybrid_class_model_refactor_route.md`
Stuck Rule: STUCK if every upstream candidate for `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct` is equivalent (under active bounds) to map-level uniqueness with no non-`molecule_h_norm` constructor and no contract-preserving refactor path.
Last Updated: 2026-03-04

## Work Plan

- [x] Record handoff obstruction/equivalence theorem from PLAN_60:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_iff_uniqueness_source_of_bounds`.
- [x] Keep model-collapse probe matrix wrappers to track each current zero-arg route.
- [x] Identify the first upstream-constructor target:
  replace the assembly-backed direct source once PLAN_49/53 delivers a
  non-`molecule_h_norm` fixed-point uniqueness constructor.
- [x] Introduce a dedicated replacement source seam for
  `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`.
- [x] Add explicit upstream constructor hook from map-level uniqueness into the
  direct-source seam and route current direct theorem through it:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_via_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`.
- [ ] Prove/export one non-`molecule_h_norm` theorem into that seam.
- [ ] Rewire:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources`
- [ ] Re-run probes and update PLAN_47/49/53 integration notes.

## Notes

- PLAN_60 isolated the active blocker to a single direct source theorem:
  `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`.
- All current zero-arg model-collapse routes are still `Molecule.molecule_h_norm`-backed.
- This plan is the successor focused on replacing that direct source from upstream constructive tracks, without introducing new axioms or weakening contracts.
- Dedicated replacement seam now exists:
  - `MoleculeResidualHybridClassFixedPointUniquenessDirectSource`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_assembly_sources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct_of_source`
  and current `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`
  is routed through this seam.
- New hook theorem
  `molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source`
  is axiom-clean modulo ground axioms; current zero-arg route
  `..._direct_source_via_uniqueness_source_direct` remains
  `Molecule.molecule_h_norm`-backed.
