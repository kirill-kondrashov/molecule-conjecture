# PLAN 75 - Non-h_norm Anchor Witness Source Cutover

Status: ACTIVE
Progress: [####------] 40%
Scope: Replace the zero-arg anchor-witness source feeding `MoleculeResidualPlan74WinningRouteSources` with a non-circular theorem that does not depend on `Molecule.molecule_h_norm`, then propagate that cutover through the breakout and top-level paths.
Acceptance:
1. `#print axioms` for at least one new zero-arg theorem implementing
   `MoleculeResidualDirectSeamAnchorSource` (or
   `MoleculeResidualDirectSeamAnchorSourceWitnessSources`) does not include
   `Molecule.molecule_h_norm`.
2. `#print axioms`
   `Molecule.molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
   does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source` and
   `#print axioms Molecule.molecule_conjecture_refined` do not include
   `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_74_non_h_norm_molecule_h_unique_replacement.md`
Stuck Rule: STUCK if every candidate zero-arg anchor-witness theorem is provably equivalent to the current `molecule_residual_direct_seam_anchor_source_early` route with no net axiom reduction.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_74 route decomposition and winning-route bundle:
  - `MoleculeResidualPlan74WinningRouteSources`
  - `molecule_residual_fixed_point_hybrid_class_collapse_source_of_plan74_winning_route_sources`
  - `molecule_residual_direct_source_breakout_sources_of_plan74_winning_route_sources`.
- [x] Keep zero-arg PLAN_72/69 aliases routed through the winning-route bundle:
  - `molecule_residual_direct_seam_anchor_source_witness_sources`
  - `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`.
- [x] Isolate a minimal non-`molecule_h_norm` source theorem target for:
  - `MoleculeResidualDirectSeamAnchorSourceWitnessSources` (preferred), or
  - `MoleculeResidualDirectSeamAnchorSource`.
  - `MoleculeResidualAnchorWitnessZeroArgSource`
  - `molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source_witness_sources`
  - `molecule_residual_plan74_winning_route_sources_of_canonical_and_zero_arg_anchor_witness_source`.
- [x] Prove bottleneck equivalence certificates for the PLAN_75 target:
  - `molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source`
  - `molecule_residual_anchor_witness_zero_arg_source_iff_fixed_point_uniqueness_source`.
- [ ] Implement a new zero-arg theorem for that target and run targeted axiom probes.
- [ ] Rewire current-route aliases to the new source theorem.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Winning-route bundle (`MoleculeResidualPlan74WinningRouteSources`) | In place and used by zero-arg alias routing; constructor/projection seams are ground-axiom-only in targeted probes. | [#######---] 70% |
| Zero-arg anchor witness source | Target interface is explicit and formally equivalent to direct-seam-anchor/uniqueness sources; current theorem remains `Molecule.molecule_h_norm`-backed. | [###-------] 30% |
| Zero-arg breakout alias cutover | Routed through winning-route bundle and zero-arg source interface; still `Molecule.molecule_h_norm`-backed. | [####------] 40% |

## Notes

- PLAN_74 is archived as STUCK after route decomposition and alias cutover were completed but axiom frontier was unchanged.
- Current explicit bottleneck remains the source theorem behind
  `molecule_residual_direct_seam_anchor_source`/`...witness_sources`.
- Verification checkpoint (2026-03-04):
  - `make build` and `make check` pass.
  - bottleneck equivalence certificates are ground-axiom-only:
    - `molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source`
    - `molecule_residual_anchor_witness_zero_arg_source_iff_fixed_point_uniqueness_source`.
  - `#print axioms` still include `Molecule.molecule_h_norm` in:
    - `molecule_residual_anchor_witness_zero_arg_source`
    - `molecule_residual_direct_seam_anchor_source_witness_sources`
    - `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
    - `molecule_residual_fixed_point_uniqueness_source`
    - `molecule_conjecture_refined`.
