# PLAN 69 - Non-h_norm Direct-Source Witness Breakout

Status: ACTIVE
Progress: [#####-----] 55%
Scope: Break out of the direct-source circular path by constructing a non-`molecule_h_norm` theorem for `MoleculeResidualFixedPointUniquenessDirectSource` (or stronger upstream source) that does not route through the current direct-source theorem.
Acceptance:
1. `#print axioms` for at least one theorem implementing one of:
   - `MoleculeResidualFixedPointUniquenessDirectSource`,
   - `MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource`,
   - `MoleculeResidualFixedPointUniquenessDirectOfRefinedSource`,
   does not include `Molecule.molecule_h_norm`.
2. The theorem above is not definitionally routed through current
   `molecule_residual_fixed_point_uniqueness_direct_source`.
3. `molecule_residual_fixed_point_uniqueness_direct_source` and
   `molecule_residual_direct_seam_anchor_source` can be cut over through the new
   theorem.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_68_non_h_norm_direct_contract_source_constructor.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate upstream source theorem collapses to the PLAN_68 equivalence frontier and still depends on current `molecule_h_norm`-backed direct-source theorems.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_68 obstruction checkpoint:
  `molecule_residual_direct_contract_cutover_sources_iff_fixed_point_uniqueness_direct_source_of_canonical`
  and refined counterpart.
- [x] Enumerate upstream candidate source theorems that do not reduce through
  current direct-source contracts.
- [x] Introduce minimal non-circular source interface for the winning upstream
  candidate.
- [ ] Implement a non-`molecule_h_norm` witness theorem against that interface
  and run targeted `#print axioms` probes.
- [ ] Cut over direct/anchor zero-arg seams via the new witness theorem.

## Notes

- PLAN_68 is archived STUCK: direct-contract cutover-source seam and
  constructors are fully explicit and ground-axiom-only, but they are
  equivalent (under canonical/refined data) to the same map-level direct-source
  theorem that remains `Molecule.molecule_h_norm`-backed.
- Immediate focus shifts upstream: construct a witness theorem that is not
  routed through current direct-source declarations.
- New checkpoint (2026-03-04):
  - selected upstream candidate seam:
    `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource`
    + canonical data.
  - added breakout-source interface:
    `MoleculeResidualDirectSourceBreakoutSources`.
  - added breakout-source constructors and seam projections:
    `molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct`,
    `molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct`,
    `molecule_residual_fixed_point_uniqueness_direct_source_of_direct_source_breakout_sources`,
    `molecule_residual_direct_seam_anchor_source_of_direct_source_breakout_sources`.
  - targeted probes confirm these new declarations are ground-axiom-only.
  - residual blocker is unchanged: current
    `molecule_residual_fixed_point_uniqueness_direct_source` remains
    `Molecule.molecule_h_norm`-backed.
