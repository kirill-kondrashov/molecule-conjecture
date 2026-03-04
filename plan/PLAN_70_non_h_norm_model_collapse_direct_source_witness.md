# PLAN 70 - Non-h_norm Model-Collapse-Direct Source Witness

Status: ACTIVE
Progress: [##--------] 20%
Scope: Eliminate `molecule_h_norm` from the PLAN_69 breakout cutover by replacing the upstream theorem `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource` with a non-circular, non-`molecule_h_norm` witness source.
Acceptance:
1. `#print axioms` for at least one theorem implementing one of:
   - `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`,
   - `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource`,
   - `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource`,
   does not include `Molecule.molecule_h_norm`.
2. `molecule_residual_direct_source_breakout_sources` can be instantiated from
   the theorem above without `Molecule.molecule_h_norm`.
3. `#print axioms` for:
   - `molecule_residual_direct_seam_anchor_source_via_direct_source_breakout_sources`
   - `molecule_residual_fixed_point_uniqueness_direct_source_via_direct_source_breakout_sources`
   no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_69_non_h_norm_direct_source_witness_breakout.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate model-collapse-direct source theorem still routes through current direct/anchor seams that are `molecule_h_norm`-backed.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_69 breakout cutover layer and obstruction checkpoints.
- [ ] Enumerate upstream candidate theorem routes for
  `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`
  that avoid current direct/anchor seam aliases.
- [ ] Introduce a minimal source interface for the winning candidate route.
- [ ] Implement a non-`molecule_h_norm` witness theorem against that interface
  and run targeted `#print axioms` probes.
- [ ] Cut over breakout zero-arg routes through the new witness theorem and
  verify axiom frontier improvement.

## Notes

- PLAN_69 is archived STUCK: breakout-source interface and cutover aliases are
  explicit and ground-axiom-only under assumptions, but the current zero-arg
  breakout source theorem is still `molecule_h_norm`-backed through
  `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source`.
- Immediate target is now upstream replacement of that model-collapse-direct
  source theorem, not further rearrangement of direct-source wrappers.
