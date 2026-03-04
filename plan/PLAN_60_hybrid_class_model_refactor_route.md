# PLAN 60 - Hybrid-Class Model Refactor Route

Status: ACTIVE
Progress: [#########-] 90%
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
- [x] Introduce first-pass hybrid-class abstraction seam scaffold:
  - `HybridProjectionSeam`
  - `currentHybridProjectionSeam`
  - `current_hybrid_projection_seam_proj_injective`
  - `current_hybrid_projection_seam_proj_eq_iff`.
- [x] Refactor first rigidity consumer to the abstraction seam:
  - `HybridProjectionInjective`
  - `map_eq_of_hybrid_projection_eq`
  - `fixed_points_in_same_class_eq` now routes through `currentHybridProjectionSeam`.
- [x] Reconstruct theorem-level hybrid-unique constructor route without
  map-level uniqueness assumption:
  - `MoleculeResidualHybridProjectionInjectiveSource`
  - `MoleculeResidualHybridClassFixedPointUniquenessSource`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_projection_injective_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_uniqueness_source`
  - and rewired
    `molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source`
    through this route.
- [x] Rewire the public current-route theorem names and rerun axiom probes.
- [ ] Replace the current theorem-level source
  `molecule_residual_hybrid_class_fixed_point_uniqueness_source` with a
  constructor from a nontrivial hybrid abstraction seam (not tied to the
  current identity-model collapse path), then re-run probes.
- [x] Generalize seam-level uniqueness machinery to collapse + lift contracts in
  `Molecule/RenormalizationFixedPointUniqueness.lean`:
  - `HybridFixedPointCollapseIn`
  - `HybridClassFixedPointLiftSource`
  - `HybridClassFixedPointUniquenessIn`
  - `hybrid_class_fixed_point_uniqueness_in_of_collapse_and_lift`
  - `hybrid_unique_fixed_point_in_of_exists_and_collapse_and_lift`.
- [x] Rewire `Molecule/Conjecture.lean` constructors to consume lift-based
  route:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_lift_source`
  - `molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source`
  - current `molecule_residual_hybrid_class_fixed_point_uniqueness_source`.
- [x] Introduce direct seam-level collapse source in `Molecule/Conjecture.lean`
  and rewire constructors through it:
  - `MoleculeResidualHybridFixedPointCollapseSource`
  - `molecule_residual_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_lift_source`.

## Notes

- Under current bounds (hence canonical fixed-point existence), the target source and map-level uniqueness are equivalent; this blocks a theorem-only rewrite.
- The next viable route is model/interface refactor in `RenormalizationFixedPointUniqueness` and its consumers.
- Targeted probe confirms the new seam scaffold is axiom-clean modulo ground
  axioms; active current-route theorem
  `molecule_residual_hybrid_unique_fixed_point_source` still carries
  `Molecule.molecule_h_norm`.
- Targeted probe confirms the new hybrid-class uniqueness constructor route
  theorems are axiom-clean modulo ground axioms; the remaining blocker is
  still the current theorem-level source
  `molecule_residual_hybrid_unique_fixed_point_source`.
- Public current-route theorem names are now rewired through the hybrid-class
  uniqueness wrapper; probes were rerun and show the wrapper is clean while the
  current source theorem still carries `Molecule.molecule_h_norm`.
- The active route no longer requires projection injectivity for hybrid-class
  uniqueness; it now uses a seam-level fixed-point lift contract. The remaining
  blocker is that the current lift source is still the identity-model instance.
- The active `molecule_residual_hybrid_class_fixed_point_uniqueness_source`
  still inherits `Molecule.molecule_h_norm` via the current collapse source,
  even though the seam-level collapse/lift constructors are individually clean.
