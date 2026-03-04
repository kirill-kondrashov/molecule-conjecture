# PLAN 65 - Canonical-To-Anchor Constructive Witness

Status: ACTIVE
Progress: [#####-----] 50%
Scope: Construct a non-`molecule_h_norm` theorem yielding `MoleculeResidualDirectSeamAnchorSource` from canonical/refined packages, then cut over the direct-seam chain through that witness.
Acceptance:
1. `#print axioms` for at least one of the following no longer includes `Molecule.molecule_h_norm`:
   - `molecule_residual_direct_seam_anchor_source`,
   - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source`,
   - `molecule_residual_fixed_point_uniqueness_direct_source`.
2. After cutover propagation, both:
   - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source`,
   - `molecule_residual_fixed_point_uniqueness_direct_source`
   are free of `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source_direct` no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_64_upstream_direct_seam_constructive_witness.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate theorem for canonical/refined-to-anchor witness still requires a direct-seam theorem already known `molecule_h_norm`-backed.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_64 seam cutover outputs and equivalence/cutover constructors.
- [x] Enumerate candidate witness theorem statements from canonical/refined
  packages to anchor seam that avoid direct-seam circularity.
- [x] Implement one witness theorem into:
  - `MoleculeResidualDirectSeamAnchorOfCanonicalSource`, or
  - `MoleculeResidualDirectSeamAnchorOfRefinedSource`.
- [ ] Cut over `molecule_residual_direct_seam_anchor_source` to the new witness.
- [x] Re-run direct-chain probes and sync PLAN_49/53 integration notes.

## Notes

- PLAN_64 completed direct-seam cutover scaffolding and was archived as STUCK
  because the only missing piece is an upstream theorem-level witness from
  canonical/refined data to anchor seam.
- Candidate witness inventory implemented in `Molecule/Conjecture.lean`:
  - source-level bridge and bottleneck certificate:
    `molecule_residual_direct_seam_anchor_source_of_uniqueness_source`,
    `molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source`;
  - contract-level wrappers:
    `molecule_residual_direct_seam_anchor_of_canonical_source_of_uniqueness_source`,
    `molecule_residual_direct_seam_anchor_of_refined_source_of_uniqueness_source`.
- Contract-equivalence checkpoint:
  - canonical/refined anchor contracts are now explicitly equivalent to
    canonical/refined uniqueness contracts via:
    `molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_of_canonical_source`,
    `molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_of_refined_source`.
  - targeted `#print axioms` probes for these new contract-level theorems are
    ground-axiom-only (`propext`, `Classical.choice`, `Quot.sound`).
- Current mathematical status:
  canonical/refined packaging now has the right cutover hooks, but no
  non-`molecule_h_norm` theorem producing
  `MoleculeResidualFixedPointUniquenessSource` yet, so zero-arg anchor cutover
  is still blocked.
- This successor contains no additional seam rearrangement goals; it is focused
  on witness theorem construction only.
