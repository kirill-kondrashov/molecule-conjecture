# PLAN 74 - Non-h_norm molecule_h_unique Replacement

Status: ACTIVE
Progress: [##--------] 20%
Scope: Replace the current `molecule_h_unique`-driven anchor proof route with a non-circular, non-`molecule_h_norm` theorem-level uniqueness witness that can discharge `MoleculeResidualDirectSeamAnchorSource`.
Acceptance:
1. `#print axioms` for at least one theorem implementing one of:
   - `MoleculeResidualDirectSeamAnchorSource`,
   - `MoleculeResidualFixedPointUniquenessSource`,
   does not include `Molecule.molecule_h_norm`.
2. The theorem above does not route through `molecule_h_unique` or
   `molecule_residual_direct_seam_anchor_source_early`.
3. `#print axioms` for:
   - `molecule_residual_fixed_point_hybrid_class_collapse_source`
   - `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
   no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_73_non_h_norm_anchor_early_witness_replacement.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate uniqueness/anchor theorem still reduces to `molecule_h_unique` or equivalent `molecule_h_norm`-backed seams.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_73/72/71/70/69 decomposition and obstruction checkpoints.
- [ ] Enumerate candidate non-circular uniqueness/anchor theorem routes that
  avoid `molecule_h_unique`.
- [ ] Introduce minimal witness interface for the winning route.
- [ ] Implement and probe a non-`molecule_h_norm` witness theorem against that
  interface.
- [ ] Cut over PLAN_73/72/71/70/69 zero-arg routes through the new witness and
  verify axiom frontier improvement.

## Notes

- PLAN_73 is archived STUCK: direct-seam-anchor witness interfaces and
  candidate-route constructors are ground-axiom-only under assumptions, but all
  current zero-arg witness routes remained `Molecule.molecule_h_norm`-backed.
- Current explicit bottleneck in code:
  `molecule_residual_direct_seam_anchor_source_early` proof body invokes
  `molecule_h_unique`.
