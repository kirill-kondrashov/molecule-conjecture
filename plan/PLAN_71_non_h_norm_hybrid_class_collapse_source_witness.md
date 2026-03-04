# PLAN 71 - Non-h_norm Hybrid-Class-Collapse Source Witness

Status: ACTIVE
Progress: [#######---] 75%
Scope: Replace the current zero-arg `MoleculeResidualFixedPointHybridClassCollapseSource` path with a non-circular, non-`molecule_h_norm` witness so PLAN_70/69 breakout cutovers can become non-`molecule_h_norm`.
Acceptance:
1. `#print axioms` for at least one theorem implementing one of:
   - `MoleculeResidualFixedPointHybridClassCollapseSource`,
   - `MoleculeResidualLiftedHybridFixedPointCollapseSource`,
   does not include `Molecule.molecule_h_norm`.
2. `molecule_residual_model_collapse_direct_witness_sources` can be
   instantiated from that theorem without `Molecule.molecule_h_norm`.
3. `#print axioms` for:
   - `molecule_residual_direct_source_breakout_sources_via_model_collapse_direct_witness_sources`
   - `molecule_residual_fixed_point_uniqueness_direct_source_via_direct_source_breakout_sources`
   no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_70_non_h_norm_model_collapse_direct_source_witness.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate hybrid-class-collapse source theorem still routes through current uniqueness/hybrid-unique/direct seams that are `molecule_h_norm`-backed.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_70 witness-interface and breakout-cutover obstruction checkpoints.
- [x] Enumerate upstream candidate theorem routes for
  `MoleculeResidualFixedPointHybridClassCollapseSource` that avoid current
  uniqueness/hybrid-unique/direct seam aliases.
- [x] Introduce minimal source interface for the winning candidate route.
- [x] Implement a non-`molecule_h_norm` witness theorem against that interface
  and run targeted `#print axioms` probes.
- [x] Cut over PLAN_70/69 zero-arg breakout routes through the new witness
  theorem and verify axiom frontier improvement.

## Notes

- PLAN_70 is archived STUCK: interface-level decomposition around
  `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`
  is complete and ground-axiom-only, but every current zero-arg candidate route
  for interface witnesses remains `Molecule.molecule_h_norm`-backed.
- Next upstream target is now explicit:
  replace the zero-arg hybrid-class-collapse source theorem route.
- New checkpoint (2026-03-04):
  - introduced minimal upstream interface:
    `MoleculeResidualHybridClassCollapseSourceWitnessSources`.
  - added interface decomposition and equivalence:
    `molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_collapse_witness_sources`,
    `molecule_residual_hybrid_class_collapse_witness_sources_of_fixed_point_hybrid_class_collapse_source`,
    `molecule_residual_hybrid_class_collapse_witness_sources_iff_fixed_point_hybrid_class_collapse_source`.
  - bridged PLAN_71 → PLAN_70 → PLAN_69 routes:
    `molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_collapse_witness_sources`,
    `molecule_residual_direct_source_breakout_sources_of_canonical_and_hybrid_class_collapse_witness_sources`,
    `molecule_residual_direct_source_breakout_sources_via_hybrid_class_collapse_witness_sources`.
  - added current-route PLAN_71/70 aliases:
    `molecule_residual_hybrid_class_collapse_witness_sources`,
    `molecule_residual_model_collapse_direct_witness_sources_via_hybrid_class_collapse_witness_sources`.
  - targeted probes confirm interface-level decomposition is ground-axiom-only.
  - residual blocker remains: current zero-arg PLAN_71 witness
    `molecule_residual_hybrid_class_collapse_witness_sources` is still
    `Molecule.molecule_h_norm`-backed.
