# PLAN 76 - Non-h_norm Anchor Witness Bottleneck Break

Status: ACTIVE
Progress: [#####-----] 50%
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
Last Updated: 2026-03-04

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
- [ ] Rewire zero-arg breakout aliases through the new theorem and verify top
  theorem propagation.
- [x] Re-run `make build`, `make check`, and targeted `#print axioms` probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| PLAN_75 interface/equivalence inheritance | Complete and archived; zero-arg target interface and bottleneck equivalences are explicit and ground-axiom-only. | [#########-] 90% |
| New non-`molecule_h_norm` zero-arg source theorem | Candidate A implemented (`MoleculeResidualAnchorWitnessDirectContractCutoverSource`) with ground-axiom-only canonical-parametric conversion/equivalence; unconditional route still carries `Molecule.molecule_h_norm`. | [###-------] 30% |
| Breakout/top-level cutover via new theorem | Awaiting previous route; aliases still use current `molecule_h_norm`-backed source. | [#---------] 10% |

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
    via `canonical_fast_fixed_point_data_from_bounds`.
- Immediate milestone for PLAN_76 is to land one candidate theorem with a
  strictly improved axiom signature at the zero-arg source seam.
