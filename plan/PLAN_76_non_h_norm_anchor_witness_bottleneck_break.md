# PLAN 76 - Non-h_norm Anchor Witness Bottleneck Break

Status: ACTIVE
Progress: [#########-] 85%
Scope: Break the PLAN_75 equivalence bottleneck by introducing a genuinely new zero-arg source theorem for `MoleculeResidualAnchorWitnessZeroArgSource` that does not depend on `Molecule.molecule_h_norm`, then propagate that cutover through breakout and top-level paths.
Acceptance:
1. `#print axioms` for the active zero-arg source theorem implementing
   `MoleculeResidualAnchorWitnessZeroArgSource` does not include
   `Molecule.molecule_h_norm`.
2. `#print axioms`
   `Molecule.molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
   does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source` and
   `#print axioms Molecule.molecule_conjecture_refined` do not include
   `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_75_non_h_norm_anchor_witness_source_cutover.md`
Stuck Rule: STUCK if every candidate zero-arg replacement theorem is provably equivalent to the current `molecule_residual_anchor_witness_zero_arg_source` route without reducing project axioms.
Last Updated: 2026-03-05

## Work Plan

- [x] Inherit PLAN_75 interface/equivalence outputs:
  - `MoleculeResidualAnchorWitnessZeroArgSource`
  - `molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source`
  - `molecule_residual_anchor_witness_zero_arg_source_iff_fixed_point_uniqueness_source`.
- [x] Build a focused candidate inventory for a non-`molecule_h_norm`
  zero-arg theorem route that does not fold back to
  `molecule_residual_direct_seam_anchor_source_early`.
- [x] Introduce a minimal replacement-source interface and
  constructor(s) into `MoleculeResidualAnchorWitnessZeroArgSource`.
- [x] Implement at least one candidate theorem and run targeted `#print axioms`
  probes.
- [x] Rewire zero-arg breakout aliases through the new theorem and verify top
  theorem propagation.
- [x] Re-run `make build`, `make check`, and targeted `#print axioms` probes.
- [x] Route the current zero-arg theorem
  `molecule_residual_anchor_witness_zero_arg_source` through the PLAN_76
  cutover-source seam.
- [x] Add source-level constructors from:
  - `MoleculeResidualCanonicalFastFixedPointDataSource`
  - `MoleculeResidualFixedPointUniquenessDirectSource`
  into both cutover-source and zero-arg source theorems.
- [ ] Replace `molecule_residual_canonical_fast_fixed_point_data_source` with a
  non-`molecule_h_norm` theorem-level source.
- [ ] Replace `molecule_residual_fixed_point_uniqueness_direct_source` with a
  non-`molecule_h_norm` theorem-level source.
- [ ] Replace `molecule_residual_anchor_witness_zero_arg_source` with a
  non-`molecule_h_norm` zero-arg theorem using the now-explicit canonical-
  parametric breakout route.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| PLAN_75 interface/equivalence inheritance | Complete and archived; zero-arg target interface and bottleneck equivalences are explicit and ground-axiom-only. | [#########-] 90% |
| New non-`molecule_h_norm` zero-arg source theorem | Candidate A implemented (`MoleculeResidualAnchorWitnessDirectContractCutoverSource`) with ground-axiom-only canonical-parametric conversion/equivalence; source-level constructors from canonical+direct-uniqueness into cutover/zero-arg routes are now explicit and ground-axiom-only, while the current zero-arg theorem remains `Molecule.molecule_h_norm`-backed. | [#######---] 70% |
| Breakout/top-level cutover via new theorem | Added canonical-parametric breakout constructor (`molecule_residual_direct_source_breakout_sources_of_canonical_and_zero_arg_anchor_witness_source`) and routed current alias through it; route constructor is ground-axiom-only but current zero-arg alias remains `Molecule.molecule_h_norm`-backed. | [######----] 60% |

## Notes

- PLAN_75 is archived as STUCK: it successfully isolated the bottleneck but did
  not deliver a non-`molecule_h_norm` zero-arg source theorem.
- New checkpoint (2026-03-04):
  - Added candidate-A interface in `Molecule/Conjecture.lean`:
    `MoleculeResidualAnchorWitnessDirectContractCutoverSource`.
  - Added candidate-A constructors/equivalences:
    `molecule_residual_anchor_witness_zero_arg_source_of_direct_contract_cutover_source`,
    `molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_zero_arg_source`,
    `molecule_residual_anchor_witness_zero_arg_source_iff_direct_contract_cutover_source_of_canonical`,
    `molecule_residual_anchor_witness_direct_contract_cutover_source_of_zero_arg_source`,
    `molecule_residual_anchor_witness_zero_arg_source_iff_direct_contract_cutover_source`.
  - Targeted probes:
    canonical-parametric conversion/equivalence are ground-axiom-only;
    unconditional reverse/equivalence still carry `Molecule.molecule_h_norm`
    via the active canonical-data source.
- New checkpoint (2026-03-04, step-1 attempt):
  - Added canonical-data source seam in `Molecule/Conjecture.lean`:
    `MoleculeResidualCanonicalFastFixedPointDataSource`.
  - Added source constructors:
    `molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source`,
    `molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_data_source`,
    and current theorem
    `molecule_residual_canonical_fast_fixed_point_data_source`.
  - Rewired current-route canonical-data consumers from
    `canonical_fast_fixed_point_data_from_bounds` to
    `molecule_residual_canonical_fast_fixed_point_data_source`, including
    breakout aliases and `molecule_hypothesis_pack_of_final_assumptions`.
  - Targeted probes:
    source constructors from existence/data assumptions are ground-axiom-only;
    current canonical-data source remains `Molecule.molecule_h_norm`-backed via
    `molecule_residual_fixed_point_existence_source`.
- New checkpoint (2026-03-05, step-2 attempt):
  - Added canonical-parametric breakout constructor:
    `molecule_residual_direct_source_breakout_sources_of_canonical_and_zero_arg_anchor_witness_source`.
  - Routed current breakout alias
    `molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources`
    through that constructor.
  - Targeted probes:
    canonical-parametric breakout constructor is ground-axiom-only;
    current breakout alias remains `Molecule.molecule_h_norm`-backed.
- New checkpoint (2026-03-05, step-3 attempt):
  - Added current cutover-source theorem:
    `molecule_residual_anchor_witness_direct_contract_cutover_source`.
  - Routed current zero-arg theorem
    `molecule_residual_anchor_witness_zero_arg_source` through the PLAN_76
    cutover-source seam instead of the earlier direct witness-source route.
  - Targeted probes:
    - `molecule_residual_anchor_witness_direct_contract_cutover_source` still
      carries `Molecule.molecule_h_norm`.
    - `molecule_residual_direct_source_breakout_sources_of_canonical_and_zero_arg_anchor_witness_source`
      is ground-axiom-only.
- New checkpoint (2026-03-05, step-4 attempt):
  - Added source-level constructors:
    `molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_uniqueness_direct_source`,
    `molecule_residual_anchor_witness_zero_arg_source_of_canonical_and_uniqueness_direct_source`.
  - Rebased current canonical-data source onto fixed-point data source:
    `molecule_residual_canonical_fast_fixed_point_data_source` now routes via
    `molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_data_source`.
  - Targeted probes:
    - both new source-level constructors are ground-axiom-only;
    - current canonical source, cutover source, zero-arg source, and breakout
      alias still carry `Molecule.molecule_h_norm`.
- Immediate milestone for PLAN_76 is to land one candidate theorem with a
  strictly improved axiom signature at the zero-arg source seam.
