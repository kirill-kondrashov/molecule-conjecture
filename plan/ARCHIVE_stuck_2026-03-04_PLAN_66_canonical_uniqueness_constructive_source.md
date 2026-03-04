# PLAN 66 - Canonical Uniqueness Constructive Source

Status: STUCK (ARCHIVED)
Progress: [##########] 100%
Scope: Construct a non-`molecule_h_norm` theorem for canonical/refined map-level uniqueness (`MoleculeResidualFixedPointUniquenessOfCanonicalSource` or refined counterpart), then route PLAN_65 anchor/direct seams through it.
Acceptance:
1. `#print axioms` for one of:
   - `molecule_residual_fixed_point_uniqueness_of_canonical_source_of_anchor_of_canonical_source`,
   - a new theorem implementing `MoleculeResidualFixedPointUniquenessOfCanonicalSource`,
   does not include `Molecule.molecule_h_norm`.
2. Using that theorem, the conditional cutover constructors from PLAN_65 can instantiate a non-`molecule_h_norm` anchor/direct-seam route.
3. After propagation, `#print axioms` for:
   - `molecule_residual_direct_seam_anchor_source`, and
   - `molecule_residual_fixed_point_uniqueness_direct_source`
   no longer include `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_65_canonical_to_anchor_constructive_witness.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate canonical/refined uniqueness theorem still reduces to current zero-arg uniqueness source routes known `molecule_h_norm`-backed.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_65 equivalence/cutover scaffolding:
  - anchor-source <-> uniqueness-source equivalences at source and contract layers;
  - canonical/refined conditional cutover constructors into anchor/direct seams.
- [x] Enumerate candidate non-circular uniqueness-source theorem statements from
  canonical/refined packages.
- [x] Implement contract-layer canonical/refined uniqueness/direct/anchor
  equivalence and cutover constructors.
- [ ] Implement one theorem into:
  - `MoleculeResidualFixedPointUniquenessOfCanonicalSource`, or
  - `MoleculeResidualFixedPointUniquenessOfRefinedSource`.
- [ ] Instantiate PLAN_65 conditional cutovers with the new theorem and route
  current anchor/direct zero-arg theorems through that path.
- [ ] Re-run direct-chain probes and sync PLAN_49/53 integration notes.

## Notes

- PLAN_65 is archived STUCK after proving that canonical/refined anchor goals
  are equivalent to canonical/refined uniqueness goals and adding all
  conditional cutover constructors.
- Immediate upstream target is now explicit and minimal:
  a non-`molecule_h_norm` witness for
  `MoleculeResidualFixedPointUniquenessOfCanonicalSource`
  (or refined counterpart).
- Candidate inventory checkpoint:
  - implemented contract constructors from hybrid-class source candidates:
    `molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_uniqueness_source`,
    `molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_collapse_source`,
    `molecule_residual_fixed_point_uniqueness_of_refined_source_of_hybrid_class_uniqueness_source`,
    `molecule_residual_fixed_point_uniqueness_of_refined_source_of_hybrid_class_collapse_source`.
  - targeted probes show these are ground-axiom-only; zero-arg direct
    uniqueness remains `Molecule.molecule_h_norm`-backed.
- Contract-equivalence checkpoint:
  - canonical/refined map-level uniqueness contracts are now explicitly
  equivalent to canonical/refined hybrid-class-uniqueness contracts via:
    `molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_hybrid_class_fixed_point_uniqueness_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_of_refined_source_iff_hybrid_class_fixed_point_uniqueness_of_refined_source`.
  - targeted probes confirm these equivalence theorems are ground-axiom-only.
- Model-collapse equivalence checkpoint:
  - canonical/refined map-level uniqueness contracts are now explicitly
    equivalent to canonical/refined hybrid-class-uniqueness model-collapse
    contracts via:
    `molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_of_refined_source`.
  - targeted probes confirm these equivalence theorems are ground-axiom-only.
- Model-collapse-direct/anchor equivalence checkpoint:
  - canonical/refined map-level uniqueness contracts are now explicitly
    equivalent to canonical/refined model-collapse-direct contracts via:
    `molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_direct_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_direct_of_refined_source`.
  - canonical/refined anchor contracts are explicitly equivalent to those
    model-collapse-direct contracts via:
    `molecule_residual_direct_seam_anchor_of_canonical_source_iff_model_collapse_direct_of_canonical_source`,
    `molecule_residual_direct_seam_anchor_of_refined_source_iff_model_collapse_direct_of_refined_source`.
  - targeted probes confirm these equivalence theorems are ground-axiom-only.
- Direct cutover constructor checkpoint:
  - added canonical/refined constructor routes from model-collapse-direct
    contracts into anchor/direct seams:
    `molecule_residual_direct_seam_anchor_source_of_canonical_and_model_collapse_direct_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_and_model_collapse_direct_of_canonical_source`,
    `molecule_residual_direct_seam_anchor_source_of_refined_and_model_collapse_direct_of_refined_source`,
    `molecule_residual_fixed_point_uniqueness_direct_source_of_refined_and_model_collapse_direct_of_refined_source`.
  - targeted probes confirm these constructor routes are ground-axiom-only.
- Direct-uniqueness contract checkpoint:
  - canonical/refined map-level uniqueness contracts are now explicitly
    equivalent to canonical/refined map-level direct-uniqueness contracts via:
    `molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_fixed_point_uniqueness_direct_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_of_refined_source_iff_fixed_point_uniqueness_direct_of_refined_source`.
  - canonical/refined anchor contracts are explicitly equivalent to those
    direct-uniqueness contracts via:
    `molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_direct_of_canonical_source`,
    `molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_direct_of_refined_source`.
  - added canonical/refined constructor routes from direct-uniqueness contracts
    into anchor seams (and thus direct seams).
  - targeted probes confirm these equivalence and constructor theorems are
    ground-axiom-only.
- Final stuck check (2026-03-04):
  - current canonical/refined direct-uniqueness contract theorems
    (`molecule_residual_fixed_point_uniqueness_direct_of_canonical_source`,
    `molecule_residual_fixed_point_uniqueness_direct_of_refined_source`)
    still include `Molecule.molecule_h_norm` in `#print axioms`.
  - no remaining candidate in this plan scope yields a non-`molecule_h_norm`
    witness theorem; all added routes are contract-level equivalence/cutover
    reductions.
  - successor plan: `PLAN_67_non_h_norm_direct_contract_witness.md`.
