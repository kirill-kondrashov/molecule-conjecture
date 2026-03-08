# PLAN 83 - Localized Fixed-Point Renormalizability Bridge

Status: ACTIVE
Progress: [###-------] 30%
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
| Domain source search | A concrete refined singleton-domain source now exists from `fixed_point_exists` plus `refined_singleton_slice_witness`; this avoids the dead normalized seam and the legacy constant-chart route, but it collapses the remaining bridge target to renormalizability of one designated fixed point. | [#######---] 70% |
| Local bridge proof | No current theorem produces `FixedPointImpliesRenormalizableOn K` from a weaker premise than `NormalizationOn K`. | [#---------] 10% |
| Downstream cutover readiness | The active existence branch is already reduced to the direct renormalizability carrier, so a localized bridge would plug in immediately once available. | [#######---] 70% |

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
