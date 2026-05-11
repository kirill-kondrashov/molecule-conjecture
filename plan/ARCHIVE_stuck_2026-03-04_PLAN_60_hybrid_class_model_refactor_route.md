# PLAN 60 - Hybrid-Class Model Refactor Route

Status: STUCK (ARCHIVED)
Progress: [##########] 100%
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
- [x] Add model-source abstraction layer over hybrid projection seams and route
  the current uniqueness theorem through it:
  - `MoleculeResidualHybridClassFixedPointUniquenessModelSources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_assembly_sources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources`
  - current `molecule_residual_hybrid_class_fixed_point_uniqueness_source`
    now consumes the model-source route.
- [x] Replace the current theorem-level source
  `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources` with a
  constructor from a nontrivial hybrid abstraction seam (not tied to the
  current identity-model collapse path), then re-run probes.
- [ ] Replace the current map-level collapse input for the lifted model-source
  route with a non-`molecule_h_norm` source and re-run probes:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source`
  - `molecule_residual_hybrid_unique_fixed_point_source`.
- [x] Add lifted-seam model-source constructors from alternative source seams to
  unblock input replacement work:
  - `molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_unique_fixed_point_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_hybrid_unique_fixed_point_source`
  - `molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_uniqueness_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_uniqueness_source`.
- [x] Add lifted-seam model-source constructors from hybrid-class uniqueness:
  - `molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_uniqueness_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_hybrid_class_uniqueness_source`.
- [x] Rewire current lifted model-source instantiation to consume a direct
  hybrid-class uniqueness source seam (instead of direct collapse input):
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources`.
- [x] Introduce explicit model-collapse source seam and route current
  model-source assembly through it:
  - `MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_*`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source`
  - current `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source`
    and `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources`.
- [x] Add current-route model-collapse probe-matrix wrappers and rerun targeted
  axiom probes:
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_hybrid_class_collapse_source`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_hybrid_class_uniqueness_source_direct`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_hybrid_unique_fixed_point_source`.
- [x] Introduce and route through explicit assembly-source pack:
  - `MoleculeResidualHybridClassFixedPointUniquenessAssemblySources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_assembly_sources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_assembly_sources_of_hybrid_class_collapse_source`
  - current `molecule_residual_hybrid_class_fixed_point_uniqueness_source`
    now consumes `molecule_residual_hybrid_class_fixed_point_uniqueness_assembly_sources`.
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
  - `molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_collapse_and_lift_sources`
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
- The new assembly-source theorem layer is axiom-clean modulo ground axioms; the
  current assembled source theorem remains `molecule_h_norm`-backed.
- The new model-source constructor theorem
  `molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources`
  and current-seam packaging theorem
  `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_assembly_sources`
  are axiom-clean modulo ground axioms.
- The current model-source value theorem
  `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources` still
  carries `Molecule.molecule_h_norm` because it is instantiated from the current
  identity-model collapse source.
- The current model-source value theorem now routes through a non-identity
  lifted seam (`liftedHybridProjectionSeam`) via:
  - `MoleculeResidualLiftedHybridFixedPointCollapseSource`
  - `MoleculeResidualLiftedHybridClassFixedPointLiftSource`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources`
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_hybrid_class_collapse_source`.
- Targeted probes confirm the lifted-seam constructors above are axiom-clean
  modulo ground axioms; the remaining `Molecule.molecule_h_norm` dependency is
  inherited from the current map-level collapse source input.
- Targeted probes confirm the new alternative lifted-seam constructors from
  hybrid-unique and uniqueness-source assumptions are also axiom-clean modulo
  ground axioms.
- Targeted probes confirm the new lifted-seam constructors from hybrid-class
  uniqueness are axiom-clean modulo ground axioms.
- Targeted probes confirm the new direct uniqueness-source seam theorem
  (`molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct`) still
  carries `Molecule.molecule_h_norm`, while the lifted model-source constructor
  from class-uniqueness inputs remains axiom-clean modulo ground axioms.
- Targeted probes confirm all model-collapse source projection constructors and
  `molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source`
  are axiom-clean modulo ground axioms; the current
  `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source`
  still carries `Molecule.molecule_h_norm`.
- Probe matrix checkpoint: all current zero-arg model-collapse routes above are
  still `Molecule.molecule_h_norm`-backed, so remaining progress on this plan is
  blocked on replacing the direct source theorem
  `molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct` with a
  non-`molecule_h_norm` source produced upstream.
- Final stuck check (2026-03-04):
  - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_iff_uniqueness_source_of_bounds`
    is axiom-clean and shows the remaining model-collapse input is equivalent
    (under active bounds) to map-level uniqueness.
  - Current zero-arg route remains `Molecule.molecule_h_norm`-backed on all
    probe-matrix branches.
  These satisfy the PLAN_60 stuck rule and hand off to PLAN_61.
