# PLAN 68 - Non-h_norm Direct Contract Source Constructor

Status: ACTIVE
Progress: [##--------] 20%
Scope: Build a non-`molecule_h_norm` source-constructor path for direct-uniqueness contracts, then cut over the zero-arg direct/anchor seams through that source.
Acceptance:
1. `#print axioms` for at least one theorem implementing one of:
   - `MoleculeResidualFixedPointUniquenessDirectSource`,
   - `MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource`,
   - `MoleculeResidualFixedPointUniquenessDirectOfRefinedSource`,
   does not include `Molecule.molecule_h_norm`.
2. `molecule_residual_fixed_point_uniqueness_direct_source` and
   `molecule_residual_direct_seam_anchor_source` can be instantiated from that
   theorem without `Molecule.molecule_h_norm`.
3. `#print axioms` for both zero-arg targets above no longer includes
   `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_67_non_h_norm_direct_contract_witness.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every available source constructor for direct-contract goals still requires current `molecule_h_norm`-backed direct-source theorems.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit order-safe direct-contract wrappers from PLAN_67:
  - `molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_iff_direct_source_of_canonical`
  - `molecule_residual_fixed_point_uniqueness_direct_of_refined_source_iff_direct_source_of_refined`
  - `molecule_residual_fixed_point_uniqueness_direct_source_via_canonical_direct_contract`
  - `molecule_residual_fixed_point_uniqueness_direct_source_via_refined_direct_contract`
  - `molecule_residual_direct_seam_anchor_source_via_canonical_direct_contract`
- [ ] Introduce a minimal direct-contract source pack that isolates exactly the
  upstream constructive obligations still missing.
- [ ] Implement a constructor from that pack to canonical/refined
  direct-contract goals and to direct/anchor source seams.
- [ ] Attempt non-circular witness candidates against the source pack and
  record targeted `#print axioms` outputs.
- [ ] If witness candidates remain `molecule_h_norm`-backed, extract an
  explicit obstruction theorem and spin the next successor plan.

## Notes

- PLAN_67 is archived STUCK: contract/equivalence/wrapper reductions completed,
  but no non-`molecule_h_norm` witness theorem was found.
- Probe checkpoint inherited from PLAN_67 closeout:
  - wrappers and constructors are ground-axiom-only;
  - current direct-contract theorems remain `Molecule.molecule_h_norm`-backed.
- Immediate objective is to replace theorem-level source construction, not add
  new axioms.
