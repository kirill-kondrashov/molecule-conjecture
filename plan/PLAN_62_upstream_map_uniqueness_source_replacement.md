# PLAN 62 - Upstream Map-Uniqueness Source Replacement

Status: ACTIVE
Progress: [#########-] 90%
Scope: Replace `molecule_residual_fixed_point_uniqueness_source_direct` with a non-`molecule_h_norm` theorem-level constructor from upstream fixed-point tracks, then feed that constructor into PLAN_61 replacement seams.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source_direct` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct` does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_hybrid_unique_fixed_point_source` does not include `Molecule.molecule_h_norm` through uniqueness.
4. `make build`, `make check`, and targeted probe matrix pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FixedPointExistence.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_47_h_norm_elimination_constructive_source_rebuild.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_61_upstream_hybrid_class_uniqueness_source_replacement.md`
Stuck Rule: STUCK if every candidate constructor for `molecule_residual_fixed_point_uniqueness_source_direct` is equivalent (under active bounds/current contracts) to existing `molecule_h_norm`-backed routes with no contract-preserving refactor path.
Last Updated: 2026-03-04

## Work Plan

- [x] Record PLAN_61 handoff obstruction:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_iff_uniqueness_source_of_bounds`.
- [x] Confirm direct/model-collapse seam layer is ready to consume a replacement map-level uniqueness theorem.
- [x] Identify the first concrete upstream constructor candidate for
  `MoleculeResidualFixedPointUniquenessSource` from PLAN_49/53 assets.
- [x] Introduce a dedicated replacement seam for
  `molecule_residual_fixed_point_uniqueness_source_direct`.
- [x] Prove/export one non-`molecule_h_norm` theorem into that seam.
- [x] Add source-parameterized PLAN_61 seam routing hooks from the map-level
  direct uniqueness seam:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_fixed_point_uniqueness_direct_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_fixed_point_uniqueness_direct_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_fixed_point_uniqueness_direct_source`.
- [x] Rewire through PLAN_61 seams:
  - `molecule_residual_fixed_point_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source`
  - `molecule_residual_hybrid_unique_fixed_point_source`.
- [x] Re-run probes and sync PLAN_47/49/53 integration notes.
- [ ] Replace current upstream constructor for
  `molecule_residual_fixed_point_uniqueness_direct_source`
  (`molecule_residual_fixed_point_hybrid_class_collapse_source_direct`) with a
  non-`molecule_h_norm` theorem-level source.

## Notes

- PLAN_61 is archived as STUCK: direct-source seam is now fully isolated but remains equivalent to map-level uniqueness under active bounds.
- This successor moves replacement upstream to the map-level uniqueness direct source, which is now the minimal non-ground replacement point for the active zero-arg route.
- Checkpoint (2026-03-04):
  - added dedicated direct-source seam alias and routed wrappers:
    `MoleculeResidualFixedPointUniquenessDirectSource`,
    `molecule_residual_fixed_point_uniqueness_direct_source`,
    `molecule_residual_fixed_point_uniqueness_source_direct_routed`.
  - identified first upstream constructor candidate route:
    `MoleculeResidualFixedPointHybridClassCollapseSource`
    -> `molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source`.
- Checkpoint (2026-03-04, constructor export):
  - exported non-`molecule_h_norm` constructors into the direct seam:
    - `molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_source`
    - `molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_assembly_sources`
    - `molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_model_collapse_source`
  - probe result:
    these three constructors are ground-axiom-only (`propext`, `Classical.choice`,
    `Quot.sound`), while current zero-arg
    `molecule_residual_fixed_point_uniqueness_direct_source` and
    `molecule_residual_fixed_point_uniqueness_source_direct_routed` remain
    `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, seam routing hooks):
  - added source-parameterized seam-routing hooks that propagate from
    `MoleculeResidualFixedPointUniquenessDirectSource` into PLAN_61 seam outputs:
    - hybrid-class uniqueness source,
    - hybrid-class model-collapse source,
    - hybrid-unique source under bounds.
  - probe result:
    all three hooks are ground-axiom-only (`propext`, `Classical.choice`,
    `Quot.sound`).
- Checkpoint (2026-03-04, zero-arg cutover):
  - rewired current zero-arg theorems through the new direct-seam hooks:
    - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`
    - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source`
    - `molecule_residual_hybrid_unique_fixed_point_source`
  - probe result:
    frontier unchanged; the rewired zero-arg theorems above and
    `molecule_residual_fixed_point_uniqueness_source_direct` still carry
    `Molecule.molecule_h_norm`.
- Checkpoint (2026-03-04, base direct-source cutover):
  - rewired `molecule_residual_fixed_point_uniqueness_source_direct` itself to
    route via `MoleculeResidualFixedPointUniquenessDirectSource`.
  - current frontier is unchanged (`Molecule.molecule_h_norm` only), now
    concentrated at:
    `molecule_residual_fixed_point_hybrid_class_collapse_source_direct`.
