# PLAN 89 - Non-h_norm Seed Producer Inventory

Status: DONE
Progress: [##########] 100%
Scope: Concrete operational subplan under `PLAN_88`. Search for a genuinely
non-circular seed-side producer class yielding
`MoleculeResidualCriticalRenormalizableFixedSeedSource` without passing through
`Molecule.molecule_h_norm`.

Acceptance:
1. Isolate at least one seed-side producer family whose resulting theorem can
   target
   `MoleculeResidualCriticalRenormalizableFixedSeedSource`
   without going through:
   - `fixed_point_exists`
   - `selected_fixed_point`
   - current `molecule_residual_fixed_point_existence_source`
   - `h_norm`
   - any route already shown equivalent to the canonical/singleton class.
2. Or else prove that every currently encoded seed-side producer family in the
   designated inventory collapses to:
   - the canonical/singleton equivalence class, or
   - an `h_norm`-backed route.
3. Record the exact downstream gate for any surviving producer:
   - fixed-point critical-value transfer
   - renormalizable-point `V`-bound control (`RV`)
4. If all inventoried seed-side producers collapse, hand off cleanly to:
   - a different seed producer class search, or
   - model redesign / new localized producer-class search under `PLAN_88`.

Dependencies: `Molecule/Conjecture.lean`,
`Molecule/FeigenbaumFixedPoint.lean`,
`Molecule/FeigenbaumFixedPointAssumptions.lean`,
`Molecule/Problem4_3.lean`,
`Molecule/BoundsToHyperbolicity.lean`,
`Molecule/HyperbolicityTheorems.lean`,
`Molecule/RenormalizationTheorem.lean`,
`README.md`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_87_non_circular_critical_seed_source.md`,
`plan/PLAN_88_dual_track_seed_or_non_singleton_localized_bridge.md`

Stuck Rule: STUCK if every producer family in the explicit inventory either:
- factors through `h_norm`, or
- collapses to the canonical/singleton equivalence class.

Last Updated: 2026-03-11

## Research Program

- [x] Enumerate the explicit seed-side producer families currently present in
  the designated repository inventory.
- [x] Classify each inventoried family as canonical/singleton equivalent,
  `h_norm`-backed, or blocked for another exact reason.
- [x] Record the exact obstruction theorem or exact dependency causing
  rejection for each blocked family.
- [x] Encode and then reject the current in-repo Banach-neighborhood operator
  producer class as a genuinely new seed source under the placeholder chart /
  operator scaffold.
- [x] Record the exact downstream gate for any hypothetical surviving source:
  `FixedPointCriticalValueTransferSource` plus
  `MoleculeResidualRenormVBoundSource`.
- [x] Since no live candidate survived, escalate cleanly back to `PLAN_88`
  with an inventory-closure statement and redesign handoff.

## Priority Order

1. `FeigenbaumFixedPoint*` producer family
2. `Problem4_3` / bounds-to-hyperbolicity producer family
3. `HyperbolicityTheorems` spectral/fixed-point producer family
4. `RenormalizationTheorem` producer family
5. exact obstruction inventory

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Producer inventory | The designated inventory is now explicit, and the broader repo-wide scan found no additional in-repo seed constructor beyond it. | [##########] 100% |
| Non-circular screening | No surviving non-`h_norm` producer class remains in the designated inventory or in the broader in-repo scan. | [##########] 100% |
| Exact obstruction inventory | Exact rejection reasons are now recorded family-by-family, including the upstream ingredient/template modules and the current chart/operator redesign obstruction. | [##########] 100% |
| Reference-guided next target | The Banach-neighborhood operator route from DLS17 Theorem 3.16 / Corollary 3.17 is now split exactly: the legacy `slice_chart` blocks separation, and the current `slice_operator` blocks genuine operator-side action even if the chart is changed. | [##########] 100% |
| Downstream gate readiness | Already complete structurally. | [##########] 100% |

## Notes

- This plan is now DONE as an inventory/handoff plan.
- It closed the in-repository seed producer inventory under the current model
  and handed the next live redesign work to
  `PLAN_90_separated_operator_action_redesign.md`.
- Inventory checkpoint (2026-03-11):
  - canonical fast fixed-point data is not a new producer family:
    `molecule_residual_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source`
    and
    `molecule_residual_renormalizable_fixed_seed_source_iff_canonical_fast_fixed_point_data_source`
    show that this route is exactly the PLAN_84 seed interface.
  - refined singleton-domain localization is not a new producer family:
    `molecule_residual_renormalizable_fixed_seed_source_of_refined_invariant_fixed_seed_singleton_domain_sources`
    and
    `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_renormalizable_fixed_seed_source`
    show that it is definitionally equivalent to the same seed route.
  - the Feigenbaum / standard-Siegel family is `h_norm`-backed at the source:
    `exists_standard_siegel_fixed_point`,
    `feigenbaum_fixed_point_existence`,
    and
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_standard_siegel_fixed_point`
    all explicitly consume `h_norm`.
  - the `Problem4_3`, bounds-to-hyperbolicity, hyperbolicity, and
    renormalization-theorem families do not introduce a new seed producer:
    they remain downstream of the same legacy fixed-point normalization spine,
    via
    `fixed_point_normalization_data_of_legacy`,
    `problem_4_3_bounds_established`,
    `bounds_imply_hyperbolicity_proof`,
    and
    `renormalizable_fixed_point_exists`.
  - current result:
    no surviving non-`h_norm` producer class has been found in the designated
    inventory.
- Broader repo scan checkpoint (2026-03-11):
  - `FixedPointExistence.lean` does not provide a seed producer:
    `fixed_point_exists` only yields a fixed point with `criticalValue = 0`,
    and in fact witnesses `defaultBMol`, which is separately proved
    non-renormalizable.
  - `PseudoSiegelDisk.lean` is downstream only:
    `exists_pseudo_siegel_disk` consumes an already renormalizable fixed point
    and therefore cannot initiate the seed-side search.
  - `RenormalizationFixedPointUniqueness.lean` is downstream only:
    its fixed-point collapse/uniqueness theorems still consume the same
    Feigenbaum-style existence spine and do not expose a new seed constructor.
  - current stronger result:
    the first broader repo-wide scan has not found any additional in-repo
    non-`h_norm` seed producer class beyond the already classified inventory.
- Upstream ingredient scan checkpoint (2026-03-11):
  - `Schauder.lean` contains a parametric fixed-point constructor
    `schauder_fixed_point_on_invariant_compact`, but it only turns an already
    supplied invariant compact set package into a fixed point; it does not
    furnish a new zero-argument producer.
  - `FeigenbaumFixedPoint.lean` packages the same shape in
    `rfast_invariant_compact_set`, but still explicitly consumes
    `h_exists`, `h_conj`, and `h_norm`.
  - `BanachSlice.lean` provides only chart/operator templates and the already
    closed refined-singleton witness `refined_singleton_slice_witness`.
  - `FeigenbaumFixedPointAssumptions.lean` only repackages assumptions and
    therefore does not introduce a new theorem-level source.
  - `Compactness.lean` only exposes `IsCompactOperator` on `HMol`; no bridge
    from that compactness seam to the BMol critical-seed contract is encoded.
- Reference-guided checkpoint (2026-03-11):
  - local reference `refs/1703.01206v3.pdf` points to a different upstream
    producer-class shape than the wrappers currently encoded in the repo:
    Theorem 3.16 gives a compact analytic pacman renormalization self-operator
    `R : B -> B` around a fixed Siegel pacman `f*`, with `R f* = f*`; Corollary
    3.17 adds a finite-dimensional unstable manifold.
  - this suggests the next honest seed-side target is not another downstream
    wrapper theorem, but an encoded source package representing that Banach
    neighborhood / compact analytic self-operator route.
  - code checkpoint:
    added
    `MoleculeResidualBanachNeighborhoodOperatorSeedSources`,
    `molecule_residual_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources`,
    and
    `molecule_residual_critical_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources_and_critical_value_transfer`
    so the paper-guided route is now a first-class theorem target in the
    repository rather than only a prose note.
  - collapse checkpoint:
    added
    `molecule_residual_banach_neighborhood_operator_seed_sources_of_renormalizable_fixed_seed_source`
    and
    `molecule_residual_banach_neighborhood_operator_seed_sources_iff_renormalizable_fixed_seed_source`
    showing that, with the current placeholder `slice_chart` / `slice_operator`
    scaffold, the Banach-neighborhood operator route is not yet a genuinely new
    in-repo producer class.
  - separation checkpoint:
    added
    `MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSources`
    and
    `no_molecule_residual_separated_banach_neighborhood_operator_seed_sources`,
    isolating the exact missing ingredient:
    the current scaffold cannot realize any nontrivial chart direction in a
    Banach-neighborhood operator package because `slice_chart` is constant.
  - minimal-redesign-target checkpoint:
    added
    `MoleculeResidualSeparatedSliceChartSource`,
    `molecule_residual_separated_slice_chart_source_of_separated_banach_neighborhood_operator_seed_sources`,
    and
    `no_molecule_residual_separated_slice_chart_source`
    so the next missing ingredient is now explicit at the smallest source
    interface: the slice chart itself must become nonconstant.
  - parameterized-redesign checkpoint:
    added
    `MoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith`,
    `MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith`,
    and
    `MoleculeResidualSeparatedSliceChartSourceWith`
    to separate the operator-route shape from the legacy chart choice itself.
  - refined-chart checkpoint:
    added
    `molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_of_renormalizable_fixed_seed_source`,
    `molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_iff_renormalizable_fixed_seed_source`,
    and
    `molecule_residual_separated_slice_chart_source_with_refined_of_renormalizable_fixed_seed_source`
    showing that `slice_chart_refined` already realizes the missing
    separation property, but only by repackaging an already available
    PLAN_84 seed.
  - operator-action checkpoint:
    added
    `MoleculeResidualSeparatedOperatorActionSourceWith`,
    `MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith`,
    `molecule_residual_separated_operator_action_source_with_of_dynamical_banach_neighborhood_operator_seed_sources_with`,
    `no_molecule_residual_separated_operator_action_source_with_current_operator`,
    and
    `no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_current_operator`
    showing that a nonconstant chart is still not enough:
    with the current placeholder `slice_operator`, no chart choice can realize
    genuine operator-side dynamics on a separated chart direction.
  - current obstruction:
    a nonconstant chart is necessary but not sufficient: to obtain a
    genuinely new producer class, the operator scaffold must also become
    nontrivial enough to realize separated operator action rather than
    collapsing to the current constant-operator model.
- Existing exact seed-side target:
  `MoleculeResidualCriticalRenormalizableFixedSeedSource`
- Existing explicit but invalid producer family:
  `molecule_residual_critical_renormalizable_fixed_seed_source_of_standard_siegel_fixed_point`
  This theorem is ground-axiom-only, but it is not a valid upstream hit for
  last-axiom elimination because its assumptions include `h_norm`.
- This plan does not own:
  - critical-value transfer
  - renormalizable-point `V`-bound control (`RV`)
  Those stay with `PLAN_80`, `PLAN_78`, and `PLAN_53`.
- This plan is intentionally narrower than `PLAN_88`:
  it only audits and advances seed-side producer classes.
- Active follow-on:
  `PLAN_90_separated_operator_action_redesign.md`.
