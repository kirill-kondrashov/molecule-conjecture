# PLAN 64 - Upstream Direct-Seam Constructive Witness

Status: STUCK (ARCHIVED)
Progress: [##########] 100%
Scope: Prove one non-`molecule_h_norm` zero-arg constructor for the direct-seam equivalence class identified in PLAN_63, then propagate that cutover through collapse/uniqueness/model-collapse direct seams.
Acceptance:
1. At least one anchor theorem in the direct-seam class is non-`molecule_h_norm`:
   - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source`, or
   - `molecule_residual_fixed_point_uniqueness_direct_source`, or
   - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source`.
2. Via equivalence/cutover, all three direct-seam zero-arg theorems above no longer include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source_direct` no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_63_upstream_hybrid_collapse_constructive_source.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate anchor constructor still requires one of the three direct seams from the same equivalence class with no independent upstream theorem source.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_63 seam reductions and equivalence certificates for:
  - collapse direct seam,
  - map-level uniqueness direct seam,
  - hybrid-class model-collapse direct seam.
- [x] Select anchor seam for constructive replacement:
  - `MoleculeResidualDirectSeamAnchorSource :=
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`.
- [x] Add projection constructors from anchor seam to the other direct seams:
  - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source`
  - `molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source`.
- [x] Define minimal upstream theorem statement that yields the anchor seam from
  refined/canonical packages without `molecule_h_norm`:
  - `MoleculeResidualDirectSeamAnchorOfCanonicalSource`
  - `MoleculeResidualDirectSeamAnchorOfRefinedSource`.
- [x] Implement anchor zero-arg theorem:
  - `molecule_residual_direct_seam_anchor_source`.
- [x] Implement anchor zero-arg theorem and route later direct-chain theorems
  through it:
  - `molecule_residual_direct_seam_anchor_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`.
- [x] Propagate cutover through direct-seam equivalence constructors for the
  early direct seam theorems:
  - `molecule_residual_fixed_point_uniqueness_direct_source`
    (via `..._of_anchor_source_early`)
  - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source`
    (via `..._of_anchor_source_early`).
- [x] Re-run full direct-chain axiom probes and sync PLAN_49/53 notes.

## Notes

- PLAN_63 completed seam isolation but was archived as STUCK because all three
  direct seams remained `molecule_h_norm`-backed despite ground-axiom-only
  equivalence/cutover scaffolding.
- This successor is the first plan that requires a genuinely new upstream
  theorem-level witness, not additional seam refactoring.
- Checkpoint (2026-03-04):
  - introduced explicit PLAN_64 anchor seam and conversion constructors into the
    direct collapse/uniqueness seams.
  - probe result:
    anchor conversion constructors are ground-axiom-only (`propext`,
    `Classical.choice`, `Quot.sound`); current zero-arg direct seams remain
    `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, upstream contract formalization):
  - added canonical/refined anchor-source contracts and conversion/projection
    constructors:
    - `molecule_residual_direct_seam_anchor_of_refined_source_of_canonical_source`
    - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_canonical_anchor_source`
    - `molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_anchor_source`
    - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_refined_anchor_source`
    - `molecule_residual_fixed_point_uniqueness_direct_source_of_refined_anchor_source`.
  - probe result:
    all new source-level constructors are ground-axiom-only.
- Checkpoint (2026-03-04, anchor zero-arg cutover):
  - added current zero-arg anchor theorem:
    `molecule_residual_direct_seam_anchor_source`.
  - routed later direct-chain theorems through anchor aliases:
    `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_via_anchor_source`,
    `molecule_residual_fixed_point_uniqueness_direct_source_via_anchor_source`,
    `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source`,
    `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`.
  - probe result:
    current zero-arg anchor and routed aliases remain
    `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, cutover aliases):
  - added canonical cutover aliases:
    - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_cutover`
    - `molecule_residual_fixed_point_uniqueness_direct_source_cutover`
  - rewired
    `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`
    through the uniqueness cutover alias.
  - probe result:
    cutover aliases and rewired downstream theorem remain
    `Molecule.molecule_h_norm`-backed.
- Checkpoint (2026-03-04, declaration-order refinement):
  - moved the anchor theorem declaration earlier (before the direct-uniqueness
    source block) and added compatibility alias:
    `molecule_residual_direct_seam_anchor_source_via_uniqueness_direct_source`.
  - declaration-order constraint still prevents directly rebinding the original
    early zero-arg direct theorem names without a wider reorder.
- Checkpoint (2026-03-04, integration sync):
  - reran direct-chain probes (`anchor`, `cutover`, `source_direct` theorems);
  - synced PLAN_49 and PLAN_53 integration notes with current PLAN_64
    anchor/cutover status.
- Checkpoint (2026-03-04, early direct uniqueness cutover):
  - added declaration-order-safe constructor:
    `molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source_early`.
  - rewired zero-arg
    `molecule_residual_fixed_point_uniqueness_direct_source`
    through this constructor and the anchor source.
  - probe result:
    constructor is ground-axiom-only; zero-arg theorem remains
    `Molecule.molecule_h_norm`-backed because anchor currently is.
- Checkpoint (2026-03-04, early direct collapse cutover):
  - added declaration-order-safe constructor:
    `molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source_early`.
  - rewired zero-arg
    `molecule_residual_fixed_point_hybrid_class_collapse_direct_source`
    through this constructor and the early anchor theorem.
  - probe result:
    constructor is ground-axiom-only; zero-arg theorem remains
    `Molecule.molecule_h_norm`-backed because anchor currently is.
- Final stuck check (2026-03-04):
  - both early zero-arg direct theorems are now routed through anchor-based
    constructors.
  - remaining blocker is purely upstream witness content:
    no theorem currently derives
    `MoleculeResidualDirectSeamAnchorSource` from canonical/refined data
    without using `molecule_h_norm` (only contract placeholders exist).
  - successor work must construct that witness theorem (PLAN_65).
