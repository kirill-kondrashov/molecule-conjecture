# PLAN 63 - Upstream Hybrid-Collapse Constructive Source

Status: ACTIVE
Progress: [#######---] 70%
Scope: Replace `molecule_residual_fixed_point_hybrid_class_collapse_direct_source` with a non-`molecule_h_norm` theorem-level constructor, then propagate that replacement through the already cut-over PLAN_62 seam path.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_hybrid_class_collapse_direct_source` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source_direct` does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct` and `#print axioms Molecule.molecule_residual_hybrid_unique_fixed_point_source` do not include `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_62_upstream_map_uniqueness_source_replacement.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate constructor for `MoleculeResidualFixedPointHybridClassCollapseDirectSource` still requires an assumption equivalent to map-level fixed-point uniqueness with no independently provable upstream source.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_62 seam cutover outputs and isolate the concentrated blocker at:
  - `MoleculeResidualFixedPointHybridClassCollapseDirectSource`.
- [x] Identify the minimal upstream theorem statement that can yield collapse on
  fast-renormalizable fixed points without assuming map-level uniqueness.
- [x] Add a source-level constructor theorem into
  `MoleculeResidualFixedPointHybridClassCollapseDirectSource` from that minimal
  upstream statement.
- [x] Add dedicated direct-source seam for the hybrid-class-uniqueness
  model-collapse route and cut over the current model-collapse theorem through
  it:
  - `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source`.
- [x] Prove direct seam equivalence certificate:
  - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_hybrid_class_uniqueness_model_collapse_direct_source`.
- [ ] Rewire current direct collapse theorem through the new constructor and
  remove the `molecule_h_norm`-backed direct body from the active path.
- [ ] Re-run targeted `#print axioms` probes for the full direct-seam chain and
  sync PLAN_49/53 integration notes.

## Notes

- PLAN_62 was archived as STUCK after full seam cutover because the remaining
  constructor space for
  `MoleculeResidualFixedPointHybridClassCollapseSource` in current code was:
  - direct theorem (`molecule_h_norm`-backed),
  - constructor from map-level uniqueness source (circular for elimination),
  - constructor from hybrid-unique source (reduces to the same uniqueness
    bottleneck under active bounds/canonical route).
- This successor is explicitly upstream: it targets a new constructive theorem
  source, not additional seam rearrangement.
- Checkpoint (2026-03-04):
  - minimal upstream statement now isolated as hybrid-class fixed-point
    uniqueness source input:
    `MoleculeResidualHybridClassFixedPointUniquenessSource`
    (or model-collapse input for it).
  - added constructive constructors:
    - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source`
    - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_model_collapse_source`
    - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_hybrid_class_uniqueness_source`
    - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_hybrid_class_uniqueness_model_collapse_source`
  - probe result:
    these constructors are ground-axiom-only (`propext`, `Classical.choice`,
    `Quot.sound`); current zero-arg
    `molecule_residual_fixed_point_hybrid_class_collapse_source_direct` remains
    `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, target equivalence sharpening):
  - added theorem:
    `molecule_residual_fixed_point_hybrid_class_collapse_source_iff_hybrid_class_uniqueness_source`.
  - probe result:
    this equivalence theorem is ground-axiom-only; both current zero-arg
    collapse source and zero-arg hybrid-class uniqueness source remain
    `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, model-collapse direct seam cutover):
  - added dedicated direct seam for current hybrid-class-uniqueness
    model-collapse theorem and routed zero-arg model-collapse source through it.
  - probe result:
    source-level constructors/projections are ground-axiom-only; current zero-arg
    model-collapse source remains `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, direct seam equivalence):
  - added equivalence theorem between direct collapse and direct model-collapse
    seams:
    `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_hybrid_class_uniqueness_model_collapse_direct_source`.
  - probe result:
    the equivalence theorem is ground-axiom-only; both current zero-arg direct
    seams remain `Molecule.molecule_h_norm`-backed.
