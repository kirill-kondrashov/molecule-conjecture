# PLAN 60 - Hybrid-Class Model Refactor Route

Status: ACTIVE
Progress: [##--------] 20%
Scope: Break the current identity-model bottleneck (`HybridClass := BMol`) so the hybrid-level unique-fixed-point source can be constructed from a genuinely hybrid-level source, not by recycling map-level uniqueness.
Acceptance:
1. Export a nontrivial hybrid-class abstraction seam (or quotient interface) that does not force `toHybridClass f = toHybridClass g ↔ f = g` in the active route.
2. Provide a theorem-level constructor route to `MoleculeResidualHybridUniqueFixedPointSource` that does not assume `MoleculeResidualFixedPointUniquenessSource`.
3. Rewire `molecule_residual_hybrid_unique_fixed_point_source` to that route.
4. `#print axioms Molecule.molecule_residual_hybrid_unique_fixed_point_source` no longer includes `Molecule.molecule_h_norm`.
5. Re-run `make build`, `make check`, and targeted `#print axioms` probes for uniqueness/orbit wrappers.
Dependencies: `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/Conjecture.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/HyperbolicityTheorems.lean`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_59_hybrid_unique_fixed_point_source_constructor.md`
Stuck Rule: STUCK if every candidate hybrid-class abstraction still collapses to definitional equality of `BMol` in the active theorem path, or requires introducing a new project axiom.
Last Updated: 2026-03-04

## Work Plan

- [x] Add dead-end certificates in the current model:
  - `toHybridClass_injective`
  - `toHybridClass_eq_iff`
  - `molecule_residual_fixed_point_hybrid_class_collapse_source_iff_uniqueness_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_canonical`
  - `molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_bounds`.
- [x] Archive PLAN_59 as STUCK under its own stuck rule and open this successor.
- [ ] Introduce a nontrivial hybrid-class abstraction seam that can replace the identity-model bottleneck in the active route.
- [ ] Refactor hybrid-collapse / rigidity lemmas to consume the new abstraction seam.
- [ ] Reconstruct hybrid-unique source constructor route without map-level uniqueness assumption.
- [ ] Rewire the public current-route theorem names and rerun axiom probes.

## Notes

- Under current bounds (hence canonical fixed-point existence), the target source and map-level uniqueness are equivalent; this blocks a theorem-only rewrite.
- The next viable route is model/interface refactor in `RenormalizationFixedPointUniqueness` and its consumers.
