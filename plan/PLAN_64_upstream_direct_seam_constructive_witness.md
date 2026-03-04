# PLAN 64 - Upstream Direct-Seam Constructive Witness

Status: ACTIVE
Progress: [#---------] 10%
Scope: Prove one non-`molecule_h_norm` zero-arg constructor for the direct-seam equivalence class identified in PLAN_63, then propagate that cutover through collapse/uniqueness/model-collapse direct seams.
Acceptance:
1. At least one anchor theorem in the direct-seam class is non-`molecule_h_norm`:
   - `molecule_residual_fixed_point_hybrid_class_collapse_direct_source`, or
   - `molecule_residual_fixed_point_uniqueness_direct_source`, or
   - `molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source`.
2. Via equivalence/cutover, all three direct-seam zero-arg theorems above no longer include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_source_direct` no longer includes `Molecule.molecule_h_norm`.
4. `make build` and `make check` pass.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/RenormalizationFixedPointUniqueness.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/FixedPointExistence.lean`, `plan/ARCHIVE_stuck_2026-03-04_PLAN_63_upstream_hybrid_collapse_constructive_source.md`, `plan/PLAN_49_fixed_point_source_constructive_route.md`, `plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`
Stuck Rule: STUCK if every candidate anchor constructor still requires one of the three direct seams from the same equivalence class with no independent upstream theorem source.
Last Updated: 2026-03-04

## Work Plan

- [x] Inherit PLAN_63 seam reductions and equivalence certificates for:
  - collapse direct seam,
  - map-level uniqueness direct seam,
  - hybrid-class model-collapse direct seam.
- [ ] Select anchor seam for constructive replacement (prefer model-collapse
  direct seam if upstream theorem fits naturally there).
- [ ] Define minimal upstream theorem statement that yields the anchor seam from
  refined/canonical packages without `molecule_h_norm`.
- [ ] Implement and cut over the anchor zero-arg theorem.
- [ ] Propagate cutover through direct-seam equivalence constructors.
- [ ] Re-run full direct-chain axiom probes and sync PLAN_49/53 notes.

## Notes

- PLAN_63 completed seam isolation but was archived as STUCK because all three
  direct seams remained `molecule_h_norm`-backed despite ground-axiom-only
  equivalence/cutover scaffolding.
- This successor is the first plan that requires a genuinely new upstream
  theorem-level witness, not additional seam refactoring.
