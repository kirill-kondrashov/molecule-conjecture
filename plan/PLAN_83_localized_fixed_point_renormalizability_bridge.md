# PLAN 83 - Localized Fixed-Point Renormalizability Bridge

Status: STUCK
Progress: [#########-] 95%
Scope: Replace the false full-domain fixed-point renormalizability contract
with one non-circular local bridge of the form
`FixedPointImpliesRenormalizableOn K`, where the domain `K` is produced from an
upstream domain package and not from fixed-data, normalization data, or any
definition mentioning `IsFastRenormalizable`.
Acceptance:
1. A theorem-level source in `Molecule/Conjecture.lean` (or an upstream module)
   yields a concrete `K : Set BMol` together with
   `∃ f : BMol, f ∈ K ∧ Rfast f = f` from upstream domain data that does not
   mention `IsFastRenormalizable`, `FixedPointNormalizationData`,
   `MoleculeResidualFixedPointDataSource`, or `molecule_h_fixed_data_direct`.
2. Combined with a fixed-point-in-`K` witness, that localized bridge yields a
   theorem `FixedPointImpliesRenormalizableOn K` that is proved without using
   `Molecule.molecule_h_norm`, `NormalizationOn K`,
   `InvariantSliceDataWithNormalization`, `FixedPointNormalizationData`, or any
   definition of `K` that already contains `IsFastRenormalizable`.
3. That localized bridge replaces
   `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`
   and removes `Molecule.molecule_h_norm` from
   `molecule_residual_fixed_point_existence_source`.
4. `make build` and `make check` pass after the replacement is threaded into
   the active existence route.
Dependencies: `Molecule/Conjecture.lean`,
`Molecule/FixedPointExistence.lean`,
`Molecule/FeigenbaumFixedPoint.lean`,
`Molecule/RenormalizationTheorem.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`,
`plan/PLAN_80_non_h_norm_fixed_point_data_source.md`,
`plan/PLAN_81_single_reference_fixed_point_data_witness.md`,
`plan/PLAN_82_canonical_fast_fixed_point_data_witness.md`,
`plan/ARCHIVE_stuck_2026-03-04_PLAN_52_fixed_point_renorm_witness_extraction.md`
Stuck Rule: STUCK if every candidate domain `K` either:
- collapses back to the false full-domain contract;
- requires the dead normalized invariant-slice-data seam;
- forces the constant-slice obstruction
  `has_invariant_slice_data_forces_univ_finite`;
- is defined in a way that already mentions `IsFastRenormalizable`; or
- gets `FixedPointImpliesRenormalizableOn K` only by factoring through
  `NormalizationOn K` or downstream fixed-data.
Last Updated: 2026-03-08

## Work Plan

- [x] Record that the literal global contract
  `forall f, Rfast f = f -> IsFastRenormalizable f`
  is not viable in the current scaffold.
- [x] Record the reusable local bridge interface and composition theorem:
  - `FixedPointImpliesRenormalizableOn`
  - `renormalizable_fixed_exists_of_fixed_point_exists_in_and_bridge_on`
- [x] Record explicit non-goals:
  - do not define `K` using `IsFastRenormalizable`;
  - do not use `NormalizationOn K` as the bridge proof;
  - do not route through `FixedPointNormalizationData` or
    `molecule_h_fixed_data_direct`.
- [ ] Identify one concrete upstream source of `K` that avoids both the dead
  normalized seam and the constant-slice obstruction.
- [ ] State one exact new theorem replacing `NormalizationOn K` on that chosen
  source route.
- [ ] Prove a non-`Molecule.molecule_h_norm` theorem producing
  `FixedPointImpliesRenormalizableOn K` from that weaker source theorem.
- [ ] Thread that localized bridge into the active existence route and rerun
  targeted axiom probes.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Feasibility gate | The repository now explicitly records that the full-domain bridge is false in the current model; only a localized bridge can be a live target. | [##########] 100% |
| Circularity guard | The admissible proof shape is now explicit: `K` may not be defined using `IsFastRenormalizable`, and the bridge may not be obtained from `NormalizationOn K` or downstream fixed-data. | [########--] 80% |
| Domain source search | A concrete refined singleton-domain source now exists from `fixed_point_exists` plus `refined_singleton_slice_witness`; this avoids the dead normalized seam and the legacy constant-chart route. | [##########] 100% |
| Local bridge proof | The singleton refined route is now reduced further to exact hybrid-class fixed-point uniqueness, and that exact theorem is now certified equivalent to selected hybrid-class identification. This route is now blocked: exact hybrid-class fixed-point uniqueness implies there is no renormalizable fixed point at all in the current scaffold. | [#########-] 95% |
| Downstream cutover readiness | Clean candidate bridge/existence routes now exist from the exact one-point source, from canonical data plus renormalizable-fixed-point identification, from canonical data plus fixed-point-only identification, and from the exact hybrid-class fixed-point uniqueness source. The exact hybrid-class uniqueness and selected-class identification formulations are now interchangeable. | [##########] 100% |
| Dead-end inventory | The tempting reduction to “every fixed hybrid class is renormalizable” is now explicitly ruled out: in the current identity-model seam it is equivalent to the false global bridge `(R)`. | [##########] 100% |
| Obstruction proof | The current exact target now formally implies `¬ MoleculeResidualFixedPointExistenceSource`, so it cannot satisfy the acceptance criterion of removing `Molecule.molecule_h_norm` from the active existence theorem. | [##########] 100% |

## Notes

- This plan is the viable successor to the old global `(R)` objective.
- This plan is not the single-reference witness search. That remains PLAN_81.
  PLAN_83 targets a domain theorem, not a one-point witness theorem.
- The literal full-domain target
  `forall f : BMol, Rfast f = f -> IsFastRenormalizable f`
  is blocked in the current scaffold by
  `no_fixed_point_implies_renormalizable`.
- Existing reusable bridge infrastructure is already present:
  - `FixedPointImpliesRenormalizableOn`
  - `renormalizable_fixed_exists_of_fixed_point_exists_in_and_bridge_on`
  - `molecule_residual_invariant_slice_fixed_point_source_of_invariant_slice_data_source`
- A concrete upstream candidate domain is now available from the refined route:
  - `molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists`
  - `molecule_residual_invariant_slice_fixed_point_source_of_refined_invariant_fixed_point_domain_sources`
- Hard obstructions to avoid are already known:
  - `no_molecule_residual_invariant_slice_data_with_normalization_source`
  - `has_invariant_slice_data_forces_univ_finite`
- The current plan would be vacuous if it allowed domains of the form
  `{f | Rfast f = f ∧ IsFastRenormalizable f}` or any equivalent downstream
  package. Those domains are explicitly forbidden here.
- The current generic bridge constructor
  `fixed_point_implies_renormalizable_on_of_normalization_on` is not an
  acceptable proof target for this plan. If the argument still needs
  `NormalizationOn K`, then the plan has not escaped the old bottleneck.
- Existing renormalizable fixed-point existence theorems in upstream modules are
  only assumption-parametric; they still require inputs such as global
  normalization or the full refined theorem, so they do not solve this plan.
- The current direct uniqueness theorems are not sufficient for this plan:
  they still compare only pairs of renormalizable fixed points, so they cannot
  identify `selected_fixed_point` unless its renormalizability is already known.
- No unconditional fixed-point uniqueness theorem is currently available in the
  repository, so the fixed-point-only identification source is still a missing
  theorem, not something that can be assembled from existing seams.
- Operational success for this plan means replacing
  `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`.
  If that happens, the active frontier shrinks to `(V)` on the witness side,
  `(C)` on the transfer side, and `(O)` on the canonical side.
- Step-1 kickoff checkpoint (2026-03-08):
  - opened the localized-bridge research track after the frontier reduction
    made clear that global `(R)` is not the right constructive target;
  - recorded the exact compositional interface already available in the code:
    fixed-point-in-domain plus `FixedPointImpliesRenormalizableOn K`;
  - active proof search now moves from theorem-routing to identifying a viable
    domain `K` and a theorem that proves renormalizability of `Rfast`-fixed
    points inside that domain.
- Step-2 plan-tightening checkpoint (2026-03-08):
  - strengthened acceptance to forbid circular local choices of `K`;
  - made explicit that a proof through `NormalizationOn K` does not count as
    progress for this plan;
  - separated this domain-bridge program from the single-reference witness
    search in PLAN_81;
  - added an early fail condition: if every candidate `K` comes only from the
    legacy constant-slice route or from downstream fixed-data, this plan should
    be marked STUCK quickly rather than expanded further.
- Step-3 refined-domain checkpoint (2026-03-08):
  - added a concrete refined singleton-domain source from the ground theorem
    `fixed_point_exists` plus `refined_singleton_slice_witness`;
  - added a projection from that source into the existing
    fixed-point-in-domain seam;
  - this completes the domain-search part of the plan on one live route, but
    also shows that the remaining bridge target on that route is now exactly a
    one-point renormalizability theorem for the designated fixed point;
  - `make build` passed;
  - `make check` passed;
  - targeted `#print axioms` probes show:
    `molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists`
    and
    `molecule_residual_invariant_slice_fixed_point_source_of_refined_invariant_fixed_point_domain_sources`
    are ground-axiom-only, while
    `molecule_residual_fixed_point_existence_source`
    still carries `Molecule.molecule_h_norm`.
- Step-4 singleton-bridge checkpoint (2026-03-08):
  - added the exact singleton bridge constructor
    `fixed_point_implies_renormalizable_on_singleton_of_renorm`;
  - added the exact reduction theorem
    `fixed_point_implies_renormalizable_on_singleton_iff`;
  - added candidate bridge/existence routes
    `molecule_residual_fixed_point_bridge_on_source_of_fixed_point_exists_and_singleton_renorm`
    and
    `molecule_residual_fixed_point_existence_source_of_fixed_point_exists_and_singleton_renorm`;
  - this proves the remaining bridge debt on the refined singleton route is no
    longer vague: it is exactly renormalizability of the fixed point chosen by
    `fixed_point_exists`.
- Step-5 exact-target checkpoint (2026-03-08):
  - named the designated point selected by `fixed_point_exists`:
    `selected_fixed_point`;
  - named the exact live theorem target:
    `MoleculeResidualSelectedFixedPointRenormalizableSource`;
  - added exact bridge/existence routes from that named source;
  - result: the remaining PLAN_83 theorem is now a single explicit proposition,
    not an unnamed existential or bridge pattern.
- Step-6 identification checkpoint (2026-03-08):
  - added the stronger exact integration source
    `MoleculeResidualSelectedFixedPointIdentificationSource`;
  - added a candidate route from PLAN_82 canonical fixed-point data plus that
    identification source into
    `MoleculeResidualSelectedFixedPointRenormalizableSource` and then the
    active existence theorem;
  - this shows the next missing theorem is not generic uniqueness, but a
    stronger identification statement for the selected point.
- Step-7 fixed-point-only identification checkpoint (2026-03-08):
  - added the stronger source
    `MoleculeResidualSelectedFixedPointFixedIdentificationSource`;
  - added the projection from that stronger source to the renormalizable
    identification source;
  - added a candidate existence route from PLAN_82 canonical fixed-point data
  plus fixed-point-only identification;
  - result: the remaining theorem target is now stated in fixed-point-only
    terms, and existing renormalizable-fixed-point uniqueness seams are
    confirmed to be insufficient.
- Step-8 hybrid-class identification checkpoint (2026-03-08):
  - added the sharper source
    `MoleculeResidualSelectedHybridClassFixedIdentificationSource`;
  - proved that this class-level statement already implies the map-level
    fixed-point-only identification target in the current identity-model
    hybrid seam;
  - added a candidate existence route from PLAN_82 canonical fixed-point data
    plus hybrid-class fixed identification;
  - result: the remaining PLAN_83 frontier is now aligned with the
    hybrid-class side of the repository, rather than quantifying directly over
    fixed maps;
  - `make build` passed;
  - `make check` passed;
  - targeted `#print axioms` probes show:
    `molecule_residual_selected_fixed_point_fixed_identification_of_hybrid_class_fixed_identification`
    and
    `molecule_residual_fixed_point_existence_source_of_selected_hybrid_class_fixed_identification_and_canonical`
    are ground-axiom-only, while
    `molecule_residual_fixed_point_existence_source`
    still carries `Molecule.molecule_h_norm`.
- Step-9 direct class-level continuation checkpoint (2026-03-08):
  - added `selected_fixed_point_hybrid_fixed`;
  - added the direct continuation
    `molecule_residual_selected_fixed_point_renormalizable_of_hybrid_class_fixed_identification_and_canonical`;
  - rerouted the candidate existence theorem from hybrid-class fixed
    identification to use that direct class-level continuation rather than
    factoring through the intermediate map-level fixed-identification wrapper;
  - result: the PLAN_83 candidate route now matches the exact remaining
    theorem frontier more closely;
  - `make build` passed;
  - `make check` passed;
  - targeted `#print axioms` probes show
    `selected_fixed_point_hybrid_fixed`,
    `molecule_residual_selected_fixed_point_renormalizable_of_hybrid_class_fixed_identification_and_canonical`,
    and
    `molecule_residual_fixed_point_existence_source_of_selected_hybrid_class_fixed_identification_and_canonical`
    are ground-axiom-only, while
    `molecule_residual_fixed_point_existence_source`
    still carries `Molecule.molecule_h_norm`.
- Step-10 exact hybrid-class uniqueness checkpoint (2026-03-08):
  - added the sharper source
    `MoleculeResidualHybridClassFixedPointExactUniquenessSource`;
  - proved that exact hybrid-class fixed-point uniqueness implies the selected
    hybrid-class identification target;
  - added a candidate existence route from exact hybrid-class fixed-point
    uniqueness plus canonical fixed-point data;
  - result: the remaining PLAN_83 frontier is now a pure class-level
    fixed-point uniqueness theorem with no renormalizability side condition;
  - `make build` passed;
  - `make check` passed;
  - targeted `#print axioms` probes show
    `molecule_residual_selected_hybrid_class_fixed_identification_of_exact_uniqueness`
    and
    `molecule_residual_fixed_point_existence_source_of_hybrid_class_fixed_point_exact_uniqueness_and_canonical`
    are ground-axiom-only, while
    `molecule_residual_fixed_point_existence_source`
    still carries `Molecule.molecule_h_norm`.
- Step-11 equivalence checkpoint (2026-03-08):
  - proved that
    `MoleculeResidualHybridClassFixedPointExactUniquenessSource`
    and
    `MoleculeResidualSelectedHybridClassFixedIdentificationSource`
    are equivalent;
  - result: the PLAN_83 target is now certified structurally saturated at the
    hybrid-class level, and any further progress must come from a theorem proof
    rather than more target reshaping;
  - `make build` passed;
  - `make check` passed;
  - targeted `#print axioms` probes show the two directions of the equivalence,
    the equivalence theorem itself, and the exact-uniqueness candidate
    existence route are all ground-axiom-only, while
    `molecule_residual_fixed_point_existence_source`
    still carries `Molecule.molecule_h_norm`.
- Step-12 dead-end checkpoint (2026-03-08):
  - defined the tempting next reduction target
    `MoleculeResidualHybridClassFixedPointRenormalizableSource`;
  - proved it is equivalent to the false global bridge
    `FixedPointImpliesRenormalizable`;
  - proved `no_molecule_residual_hybrid_class_fixed_point_renormalizable_source`;
  - result: the “all fixed hybrid classes are renormalizable” branch is now
    formally closed and should not be pursued as a successor to PLAN_83.
- Step-13 obstruction checkpoint (2026-03-08):
  - proved
    `no_molecule_residual_fixed_point_existence_source_of_hybrid_class_fixed_point_exact_uniqueness`;
  - `make build` passed;
  - `make check` passed;
  - targeted `#print axioms` probes show that obstruction theorem is
    ground-axiom-only;
  - result: the current exact target
    `MoleculeResidualHybridClassFixedPointExactUniquenessSource`
    cannot discharge the plan acceptance criterion, because in the current
    scaffold it implies there is no renormalizable fixed point witness at all;
  - PLAN_83 is therefore STUCK as an existence-side elimination route unless
    the ground fixed-point witness `fixed_point_exists` is changed or the route
    is redesigned around a different target.
