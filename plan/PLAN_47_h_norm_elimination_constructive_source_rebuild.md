# PLAN 47 - `molecule_h_norm` Elimination via Constructive Source Rebuild

Status: ACTIVE
Progress: [#####-----] 50%
Scope: Remove the last project axiom `Molecule.molecule_h_norm` from the zero-argument route by replacing the remaining non-ground source constructors with theorem-level constructive proofs.
Acceptance:
1. `#print axioms Molecule.molecule_residual_non_ground_sources` does not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_bounds_seed_free` does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_conjecture_refined` does not include `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `plan/PLAN_48_orbit_clause_constructive_route.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/ARCHIVE_superseded_2026-03-04_PLAN_45_local_fixed_point_normalization_source.md`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_46_seed_free_ingredient_constructor.md`
Stuck Rule: STUCK if both source tracks below cannot advance without introducing a new project axiom or weakening exported theorem statements.
Last Updated: 2026-03-04

## Feasibility Gate (Dead-End Check)

- Not a formal dead end yet:
  - the code already isolates the final dependency behind source seams;
  - bounds assembly now consumes `MoleculeResidualBoundsAssemblySources`, which narrows the replacement target.
- High-risk area:
  - current orbit-clause and uniqueness/data seeds are still produced via ex-falso/global-normalization routes.
- Go/no-go criterion:
  - proceed only on theorem-level constructive routes from existing contracts; no new axioms and no contract weakening.

## Track A - Constructive fixed-point ingredient source

- [x] Narrow bounds assembly to consume `MoleculeResidualBoundsAssemblySources`.
- [x] Verify axiom profile of narrowed assembly route:
  - `molecule_residual_bounds_seed_free_of_bounds_assembly_sources` is axiom-clean
    modulo ground axioms (`propext`, `Classical.choice`, `Quot.sound`).
- [x] Split fixed-point assembly seam from orbit-clause seam:
  - `MoleculeResidualFixedPointAssemblySources`
  - `molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources`
- [x] Re-orient non-ground source pack assembly to a forward constructor:
  - `molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources`.
- [ ] Replace current ingredient seed route with a constructive theorem package that does not use `molecule_h_norm`.
- [ ] Export theorem-level bridge:
  - constructive `MoleculeResidualFixedPointNormalizationIngredients`.

## Track B - Constructive orbit-clause source

- [ ] Identify a non-ex-falso orbit transport/orbit clause route from existing theorem infrastructure.
- [ ] Prove/export a theorem-level `MoleculeResidualOrbitClauseSource` constructor without `molecule_h_norm`.
- [ ] Wire `molecule_residual_orbit_transport_source` through the constructive orbit-clause route.

## Integration

- [ ] Rebuild `molecule_residual_non_ground_sources` from constructive Track A + Track B outputs.
- [ ] Re-run `make build`, `make check`, and targeted `#print axioms` probes.
- [ ] Mark plan DONE only when all acceptance checks pass.

## Notes

- This plan supersedes PLAN_46 as the active implementation path.
- If Track B stalls while Track A progresses, keep Track A changes and open a focused orbit-clause sub-plan.
- Current frontier from targeted axiom probe:
  - `molecule_residual_non_ground_sources` still carries `Molecule.molecule_h_norm`.
  - Downstream narrowed assembly theorems are already axiom-clean under source inputs.
