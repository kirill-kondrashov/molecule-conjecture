# PLAN 74 - Non-h_norm molecule_h_unique Replacement

Status: STUCK
Progress: [#####-----] 50%
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

Superseded By: `plan/ARCHIVE_stuck_2026-03-04_PLAN_75_non_h_norm_anchor_witness_source_cutover.md` (active successor: `plan/PLAN_76_non_h_norm_anchor_witness_bottleneck_break.md`)

## Work Plan

- [x] Inherit PLAN_73/72/71/70/69 decomposition and obstruction checkpoints.
- [x] Enumerate candidate non-circular uniqueness/anchor theorem routes that
  avoid `molecule_h_unique`.
- [x] Introduce minimal witness interface for the winning route.
  - `MoleculeResidualPlan74WinningRouteSources`
  - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_plan74_winning_route_sources`
  - `molecule_residual_direct_source_breakout_sources_of_plan74_winning_route_sources`
- [x] Cut over current PLAN_72/69 zero-arg alias routing through the winning
  route bundle:
  - `molecule_residual_direct_seam_anchor_source_witness_sources`
  - `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
- [ ] Implement and probe a non-`molecule_h_norm` witness theorem against that
  interface.
- [ ] Cut over PLAN_73/72/71/70/69 zero-arg routes through the new witness and
  verify axiom frontier improvement.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Winning-route bundle (`MoleculeResidualPlan74WinningRouteSources`) | New bundle and parameterized propagation theorems added; constructor/projection seams are ground-axiom-only in targeted probes. | [#######---] 70% |
| Collapse propagation (`...direct_seam_anchor_witness_sources` -> `...fixed_point_hybrid_class_collapse_source...`) | Parameterized propagation path validated as ground-axiom-only in targeted probes. | [#####-----] 50% |
| Breakout propagation (`...canonical_and_direct_seam_anchor_witness_sources`) | Parameterized breakout path validated as ground-axiom-only in targeted probes. | [######----] 60% |
| Zero-arg cutover (`molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`) | Routed through winning-route bundle; still `Molecule.molecule_h_norm`-backed. | [###-------] 30% |

## Notes

- PLAN_73 is archived STUCK: direct-seam-anchor witness interfaces and
  candidate-route constructors are ground-axiom-only under assumptions, but all
  current zero-arg witness routes remained `Molecule.molecule_h_norm`-backed.
- Current explicit bottleneck in code:
  `molecule_residual_direct_seam_anchor_source_early` proof body invokes
  `molecule_h_unique`.
- Verification checkpoint (2026-03-04):
  - `make build` and `make check` pass.
  - Targeted probes still show `Molecule.molecule_h_norm` in:
    - `molecule_residual_direct_seam_anchor_source`
    - `molecule_residual_fixed_point_uniqueness_source`
    - `molecule_residual_fixed_point_hybrid_class_collapse_source`
    - `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`.
  - Current zero-arg PLAN_72/69 alias routing is now explicitly cut over through
    `MoleculeResidualPlan74WinningRouteSources`; axiom frontier unchanged.
  - Targeted probes confirm the selected parameterized winning-route seams are
    ground-axiom-only:
    - `molecule_residual_plan74_winning_route_sources_of_canonical_and_anchor_witness`
    - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_plan74_winning_route_sources`
    - `molecule_residual_direct_source_breakout_sources_of_plan74_winning_route_sources`
    - `molecule_residual_hybrid_class_collapse_witness_sources_of_direct_seam_anchor_witness_sources`
    - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_collapse_witness_sources`
    - `molecule_residual_direct_source_breakout_sources_of_canonical_and_direct_seam_anchor_witness_sources`.
