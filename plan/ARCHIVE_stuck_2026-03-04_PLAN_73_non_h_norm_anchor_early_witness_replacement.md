# PLAN 73 - Non-h_norm Anchor-Early Witness Replacement

Status: STUCK (ARCHIVED)
Progress: [########--] 80%
Scope: Replace the current zero-arg theorem `molecule_residual_direct_seam_anchor_source_early` (which drives PLAN_72/71/70/69) with a non-circular, non-`molecule_h_norm` witness route.
Acceptance:
1. `#print axioms` for at least one theorem implementing
   `MoleculeResidualDirectSeamAnchorSource` does not include
   `Molecule.molecule_h_norm`.
2. The theorem above does not route through
   `molecule_residual_direct_seam_anchor_source_early` or `molecule_h_unique`.
3. `#print axioms` for:
   - `molecule_residual_fixed_point_hybrid_class_collapse_source`
   - `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
   no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_72_non_h_norm_direct_seam_anchor_source_witness.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate direct-seam-anchor source theorem still reduces to the current `molecule_h_unique`-based route or equivalent `molecule_h_norm`-backed uniqueness seams.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_72/71/70/69 decomposition and obstruction checkpoints.
- [x] Enumerate upstream candidate theorem routes for
  `MoleculeResidualDirectSeamAnchorSource` that avoid
  `molecule_residual_direct_seam_anchor_source_early`.
- [x] Introduce a minimal witness interface for the winning route.
- [x] Implement a non-`molecule_h_norm` witness theorem against that interface
  and run targeted `#print axioms` probes.
- [x] Cut over PLAN_72/71/70/69 zero-arg routes through the new witness theorem
  and verify axiom frontier improvement.

## Notes

- PLAN_72 is archived STUCK: interface-level decomposition around
  `MoleculeResidualDirectSeamAnchorSource` is complete and ground-axiom-only
  under assumptions, but the current zero-arg witness still routes through
  `molecule_residual_direct_seam_anchor_source_early`.
- Current explicit bottleneck theorem:
  `molecule_residual_direct_seam_anchor_source_early` (proof body calls
  `molecule_h_unique`).
- Final candidate-route checkpoint (2026-03-04):
  - introduced direct-seam-anchor witness interface and candidate-route
    constructors from uniqueness, direct-uniqueness, hybrid-unique,
    hybrid-class-uniqueness, and hybrid-class-collapse assumptions.
  - targeted probes confirm interface/candidate constructors are
    ground-axiom-only.
  - final stuck check:
    all current zero-arg witness aliases remained
    `Molecule.molecule_h_norm`-backed via
    `molecule_residual_direct_seam_anchor_source_early`.
  - successor plan:
    `PLAN_74_non_h_norm_molecule_h_unique_replacement.md`.
