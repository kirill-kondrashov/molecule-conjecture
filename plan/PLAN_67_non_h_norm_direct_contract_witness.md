# PLAN 67 - Non-h_norm Direct Contract Witness

Status: ACTIVE
Progress: [###-------] 30%
Scope: Construct a non-`molecule_h_norm` theorem for canonical/refined map-level direct-uniqueness contract (`MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource` or refined counterpart), then instantiate inherited cutover constructors to clear anchor/direct zero-arg seams.
Acceptance:
1. `#print axioms` for a theorem implementing one of:
   - `MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource`,
   - `MoleculeResidualFixedPointUniquenessDirectOfRefinedSource`,
   does not include `Molecule.molecule_h_norm`.
2. Using that theorem, constructor routes to:
   - `molecule_residual_direct_seam_anchor_source`, and
   - `molecule_residual_fixed_point_uniqueness_direct_source`
   can be instantiated without `Molecule.molecule_h_norm`.
3. `#print axioms` for both zero-arg targets above no longer includes
   `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_66_canonical_uniqueness_constructive_source.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate direct-contract witness theorem still instantiates only through current `molecule_residual_fixed_point_uniqueness_direct_source` / model-collapse direct sources that are already `molecule_h_norm`-backed.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_66 contract/equivalence/cutover scaffolding:
  - uniqueness contracts ↔ hybrid uniqueness/model-collapse/model-collapse-direct contracts;
  - uniqueness contracts ↔ direct-uniqueness contracts;
  - anchor contracts ↔ direct/model-collapse-direct contracts;
  - constructor routes from these contracts into anchor/direct seams.
- [x] Enumerate candidate non-circular witness theorems for
  `MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource` (or refined).
- [ ] Implement one non-`molecule_h_norm` witness theorem.
- [ ] Instantiate inherited cutover constructors with the new witness theorem
  and route current zero-arg anchor/direct theorems.
- [ ] Re-run direct-chain probes and sync PLAN_49/53 integration notes.

## Notes

- PLAN_66 is archived STUCK: contract-level reductions are complete, but the
  current direct-contract theorems remain `Molecule.molecule_h_norm`-backed.
- Immediate upstream target is now explicit and minimal:
  a non-`molecule_h_norm` direct-contract witness theorem for canonical/refined
  packages.
- Candidate inventory checkpoint:
  - added direct-contract constructors from model-collapse-direct source and
    from map-level direct-source seams:
    `molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_model_collapse_direct_source`,
    `molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_model_collapse_direct_source`,
    `molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_fixed_point_uniqueness_direct_source`,
    `molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_fixed_point_uniqueness_direct_source`.
  - added current canonical/refined direct-contract theorems:
    `molecule_residual_fixed_point_uniqueness_direct_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_direct_of_refined_source`.
  - probe checkpoint:
    constructors are ground-axiom-only; current direct-contract theorems remain
    `Molecule.molecule_h_norm`-backed.
