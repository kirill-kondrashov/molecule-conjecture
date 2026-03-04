# PLAN 72 - Non-h_norm Direct-Seam-Anchor Source Witness

Status: STUCK (ARCHIVED)
Progress: [########--] 85%
Scope: Replace the current zero-arg `MoleculeResidualDirectSeamAnchorSource` / `molecule_residual_direct_seam_anchor_source_early` route with a non-circular, non-`molecule_h_norm` witness so downstream PLAN_71/70/69 cutovers can become non-`molecule_h_norm`.
Acceptance:
1. `#print axioms` for at least one theorem implementing one of:
   - `MoleculeResidualDirectSeamAnchorSource`,
   - `MoleculeResidualFixedPointUniquenessSource`,
   does not include `Molecule.molecule_h_norm`.
2. The theorem above does not route through current
   `molecule_residual_direct_seam_anchor_source_early`.
3. `#print axioms` for:
   - `molecule_residual_fixed_point_hybrid_class_collapse_source`
   - `molecule_residual_direct_source_breakout_sources_via_hybrid_class_collapse_witness_sources`
   no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_71_non_h_norm_hybrid_class_collapse_source_witness.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate direct-seam-anchor source theorem still routes through current uniqueness/hybrid-unique/direct source theorems that are `molecule_h_norm`-backed.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_71/70/69 decomposition and obstruction checkpoints.
- [x] Enumerate upstream candidate theorem routes for
  `MoleculeResidualDirectSeamAnchorSource` that avoid current zero-arg anchor
  and uniqueness theorems.
- [x] Introduce a minimal witness interface for the winning candidate route.
- [x] Implement a non-`molecule_h_norm` witness theorem against that interface
  and run targeted `#print axioms` probes.
- [x] Cut over PLAN_71/70/69 zero-arg routes through the new witness theorem
  and verify axiom frontier improvement.

## Notes

- PLAN_71 is archived STUCK: interface-level decomposition around
  `MoleculeResidualFixedPointHybridClassCollapseSource` is complete and
  ground-axiom-only, but every current zero-arg candidate witness route remains
  `Molecule.molecule_h_norm`-backed.
- Upstream bottleneck is now explicit in the current model:
  `molecule_residual_direct_seam_anchor_source_early` (current zero-arg anchor
  source theorem) remains `Molecule.molecule_h_norm`-backed.
- Final candidate-route checkpoint (2026-03-04):
  - introduced minimal interface:
    `MoleculeResidualDirectSeamAnchorSourceWitnessSources`.
  - added interface decomposition/equivalence and bridges into PLAN_71/70/69
    routes, plus current-route aliases.
  - targeted probes confirm interface-level declarations are ground-axiom-only.
  - final stuck check:
    current zero-arg PLAN_72 witness
    `molecule_residual_direct_seam_anchor_source_witness_sources` and routed
    downstream aliases remain `Molecule.molecule_h_norm`-backed through
    `molecule_residual_direct_seam_anchor_source_early`.
  - successor plan:
    `PLAN_73_non_h_norm_anchor_early_witness_replacement.md`.
