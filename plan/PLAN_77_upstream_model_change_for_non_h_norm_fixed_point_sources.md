# PLAN 77 - Upstream Model Change For Non-h_norm Fixed-Point Sources

Status: ACTIVE
Progress: [#######---] 70%
Scope: Replace the model-level global-normalization and full-domain bridge
bottlenecks with upstream local-domain contracts that can feed non-
`molecule_h_norm` fixed-point existence/uniqueness source theorems.
Acceptance:
1. `#print axioms Molecule.molecule_residual_fixed_point_existence_source` does
   not include `Molecule.molecule_h_norm`.
2. `#print axioms Molecule.molecule_residual_fixed_point_uniqueness_direct_source`
   does not include `Molecule.molecule_h_norm`.
3. `#print axioms Molecule.molecule_residual_canonical_fast_fixed_point_data_source`
   does not include `Molecule.molecule_h_norm`.
4. `#print axioms Molecule.molecule_residual_anchor_witness_zero_arg_source` and
   `#print axioms Molecule.molecule_conjecture_refined` do not include
   `Molecule.molecule_h_norm`.
5. `make build` and `make check` pass.
Dependencies: `Molecule/Rfast.lean`, `Molecule/Conjecture.lean`,
`Molecule/FixedPointExistence.lean`, `Molecule/FeigenbaumFixedPoint.lean`,
`Molecule/RenormalizationFixedPointUniqueness.lean`,
`plan/PLAN_49_fixed_point_source_constructive_route.md`,
`plan/PLAN_53_fixed_point_model_bottleneck_refactor.md`,
`plan/PLAN_76_non_h_norm_anchor_witness_bottleneck_break.md`
Stuck Rule: STUCK if every upstream candidate still requires either
`Molecule.molecule_h_norm` or full-domain `FixedPointImpliesRenormalizable`.
Last Updated: 2026-03-06

## Work Plan

- [x] Consolidate current upstream obstruction facts and migration constraints:
  - `no_fixed_point_implies_renormalizable`;
  - `global_normalization_contract_inconsistent`;
  - `molecule_h_norm_inconsistent`;
  - current residual blockers:
    `molecule_residual_fixed_point_existence_source`,
    `molecule_residual_fixed_point_uniqueness_direct_source`,
    `molecule_residual_canonical_fast_fixed_point_data_source`.
- [x] Introduce a restricted bridge contract (on an invariant/local domain) that
  avoids full-domain `FixedPointImpliesRenormalizable`.
- [x] Introduce a renormalizable fixed-point witness source contract that does
  not route through `molecule_h_norm`.
- [x] Rebuild `molecule_residual_fixed_point_existence_source` from the new
  upstream witness/bridge route.
- [x] Add a model-sources-based direct-uniqueness seam and route PLAN_76
  cutover-ingredient consumers through it.
- [x] Route downstream uniqueness consumers (`hybrid_unique`,
  `fixed_point_uniqueness_source`) through the model-source direct-uniqueness
  seam where declaration order permits.
- [x] Route the active canonical fixed-point data source through the upstream
  existence seam.
- [x] Factor the current transfer/data carriers through explicit PLAN_77
  model-source seams so the remaining transfer-side `molecule_h_norm`
  dependency is isolated at current source values.
- [x] Split the transfer route into critical-value/`V`-bound component seams
  and route current canonical `V`-bound/orbit-debt aliases through that local
  transfer component layer.
- [x] Make the invariant-set local-domain transfer route explicit and rebase
  current transfer/data theorems through it.
- [ ] Replace the current local-domain transfer/data source values with
  non-`molecule_h_norm` witnesses.
- [ ] Rebuild `molecule_residual_fixed_point_uniqueness_direct_source` from
  non-circular hybrid collapse/lift uniqueness seams.
- [ ] Keep canonical-first partial bypass available while transfer-side work is
  active, but do not let it replace the primary transfer/data target.
- [ ] If both transfer-side and lifted-seam uniqueness replacement stall,
  pivot to an explicit model-restriction redesign of the active upstream
  contracts.
- [ ] Rebuild `molecule_residual_canonical_fast_fixed_point_data_source` from
  the non-`molecule_h_norm` fixed-point data source.
- [ ] Re-run PLAN_76 cutover using the new upstream sources and probe axiom
  signatures at zero-arg and top-level frontiers.
- [ ] Run `make build` and `make check`.

## Priority Order

1. Local-domain transfer/data replacement.
2. Lifted-seam model-collapse witness for uniqueness.
3. Canonical-first partial bypass where it reduces transfer-side debt.
4. Model-restriction redesign only if the first two tracks stall.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Upstream model-obstruction inventory | Core contradictions and dependency hotspots are explicit and linked to source theorems. | [###-------] 30% |
| Existence-source upstream replacement | Added restricted bridge-on source seam and existence constructor (`molecule_residual_fixed_point_existence_source_of_bridge_on`), then rerouted active `molecule_residual_fixed_point_existence_source` via bridge-on path; constructor seams are ground-axiom-only, active route is still `molecule_h_norm`-backed via current fixed-point data source. | [####------] 40% |
| Local-domain transfer/data replacement | Active transfer/data theorems now route through invariant-set local-domain transfer sources, with canonical `V`-bound/orbit debt consuming transfer-component seams. Constructor seams are ground-axiom-only, but the current local-domain source values still inherit `molecule_h_norm`. | [#####-----] 50% |
| Lifted-seam model-collapse witness | Model-sources-based direct-uniqueness seam is in place and PLAN_76/downstream uniqueness consumers are cut over to it; remaining blocker is the current model-collapse value feeding that seam. | [##--------] 20% |
| Canonical-first partial bypass | Canonical fast fixed-point data already routes through existence, and canonical `V`-bound/orbit debt now route through transfer-component seams; this lowers transfer-side debt visibility but does not yet remove the active upstream source values. | [###-------] 30% |
| Model-restriction fallback inventory | Full-domain bridge/global-normalization obstruction is explicit; no restricted-model redesign has been implemented yet. | [#---------] 10% |
| PLAN_76 downstream cutover readiness | PLAN_76 routing seams are mature; cutover-ingredients and downstream uniqueness consumers now consume model-sources-based direct uniqueness, and the active canonical source now consumes the upstream existence seam. Remaining blockers are the current uniqueness-side model-collapse value and transfer/data-side source values. | [########--] 80% |

## Notes

- Current model-level obstruction facts:
  - `Rfast` totalization maps non-renormalizable maps to `defaultBMol`
    (`Molecule/Rfast.lean`), creating non-renormalizable fixed-point behavior.
  - `no_fixed_point_implies_renormalizable` blocks full-domain bridge use.
  - `global_normalization_contract_inconsistent` and
    `molecule_h_norm_inconsistent` show the legacy global-normalization route is
    not a viable constructive upstream source.
- Immediate milestone: define one restricted upstream bridge/witness contract
  with at least one non-`molecule_h_norm` theorem-level source feeding
  `MoleculeResidualFixedPointExistenceSource`.
- New checkpoint (2026-03-06, step-1 attempt):
  - Added restricted bridge contract:
    `FixedPointImpliesRenormalizableOn`.
  - Added restricted existence constructor:
    `renormalizable_fixed_exists_of_fixed_point_exists_in_and_bridge_on`.
  - Added localized normalization-to-bridge constructor:
    `fixed_point_implies_renormalizable_on_of_normalization_on`.
  - Added upstream restricted bridge-on source seam:
    `MoleculeResidualFixedPointBridgeOnSource`.
  - Added source-level constructors:
    `molecule_residual_fixed_point_existence_source_of_bridge_on`,
    `molecule_residual_fixed_point_bridge_on_source_of_fixed_point_and_normalization_on`.
  - Targeted probes:
    all new constructors are ground-axiom-only; current
    `molecule_residual_fixed_point_existence_source`,
    `molecule_residual_fixed_point_uniqueness_direct_source`,
    `molecule_residual_canonical_fast_fixed_point_data_source`,
    and top-level routes remain `Molecule.molecule_h_norm`-backed.
- New checkpoint (2026-03-06, step-2 attempt):
  - Added bridge-on source constructor from fixed-point data source:
    `molecule_residual_fixed_point_bridge_on_source_of_fixed_point_data_source`.
  - Added current bridge-on source theorem:
    `molecule_residual_fixed_point_bridge_on_source`.
  - Added current existence theorem routed via bridge-on seam:
    `molecule_residual_fixed_point_existence_source_via_bridge_on`.
  - Rebased `molecule_residual_fixed_point_existence_source` onto
    `molecule_residual_fixed_point_existence_source_via_bridge_on`.
  - Targeted probes:
    data-parametric bridge-on constructor is ground-axiom-only; current
    bridge-on source and active existence theorem remain
    `Molecule.molecule_h_norm`-backed.
- New checkpoint (2026-03-06, step-3 attempt):
  - Added PLAN_77 direct-uniqueness model-sources seam:
    `MoleculeResidualFixedPointUniquenessDirectModelSources`.
  - Added source-level constructors:
    `molecule_residual_fixed_point_uniqueness_direct_model_sources_of_hybrid_class_uniqueness_model_sources`,
    `molecule_residual_fixed_point_uniqueness_direct_source_of_model_sources`.
  - Added current routed direct-uniqueness theorem:
    `molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources`.
  - Routed PLAN_76 cutover-ingredients theorem
    `molecule_residual_anchor_witness_cutover_ingredients` through
    `molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources`.
  - Targeted probes:
    source-level model-sources constructors are ground-axiom-only; current
    model-sources value, routed direct-uniqueness theorem, cutover-ingredients
    theorem, and top-level routes remain `Molecule.molecule_h_norm`-backed.
- New checkpoint (2026-03-06, step-4 attempt):
  - Rerouted later uniqueness consumers through model-source direct-uniqueness:
    `molecule_residual_hybrid_unique_fixed_point_source`,
    and therefore `molecule_residual_fixed_point_uniqueness_source`.
  - Targeted probes:
    source-level model-sources constructors remain ground-axiom-only; routed
    `hybrid_unique`, `fixed_point_uniqueness_source`, PLAN_76 cutover, and
    top-level routes still remain `Molecule.molecule_h_norm`-backed via the
    current model-source value.
- New checkpoint (2026-03-06, step-5 attempt):
  - Rebased active canonical source
    `molecule_residual_canonical_fast_fixed_point_data_source` onto
    `molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source`
    fed by `molecule_residual_fixed_point_existence_source`.
  - Targeted probes:
    the existence-to-canonical constructor remains ground-axiom-only; active
    canonical source, PLAN_76 cutover, zero-arg, and top-level routes remain
    `Molecule.molecule_h_norm`-backed.
- New checkpoint (2026-03-06, step-6 attempt):
  - Added PLAN_77 transfer/data model-source seams:
    `MoleculeResidualFixedPointTransferModelSources`,
    `MoleculeResidualFixedPointDataModelSources`.
  - Added source-level constructors:
    `molecule_residual_fixed_point_transfer_source_of_model_sources`,
    `molecule_residual_fixed_point_data_source_of_model_sources`.
  - Rebased current transfer/data theorems onto explicit model-source routes:
    `molecule_residual_fixed_point_transfer_source_via_model_sources`,
    `molecule_residual_fixed_point_data_source_via_model_sources`,
    then `molecule_residual_fixed_point_transfer_source`,
    `molecule_residual_fixed_point_data_source`.
  - Targeted probes:
    new transfer/data model-source constructors are ground-axiom-only; active
    transfer/data/canonical routes remain `Molecule.molecule_h_norm`-backed,
    and the current frontier is now explicit on both uniqueness-side
    model-collapse and transfer/data source values.
- New checkpoint (2026-03-06, step-7 attempt):
  - Added PLAN_77 transfer-component seam:
    `MoleculeResidualFixedPointTransferComponentSources`.
  - Added source-level constructors:
    `molecule_residual_fixed_point_transfer_source_of_component_sources`,
    `molecule_residual_canonical_vbound_source_of_transfer_component_sources`,
    `molecule_residual_canonical_orbit_at_debt_source_of_structure_and_transfer_component_sources`.
  - Added current transfer-component and canonical partial-bypass routes:
    `molecule_residual_fixed_point_transfer_component_sources`,
    `molecule_residual_canonical_vbound_source_via_fixed_point_transfer_component_sources`,
    `molecule_residual_canonical_orbit_at_debt_source_via_fixed_point_transfer_component_sources`.
  - Rebased the existing current canonical `V`-bound/orbit-debt aliases onto
    the transfer-component route.
  - Targeted probes:
    new transfer-component constructors are ground-axiom-only; current
    transfer-component and canonical aliases remain `Molecule.molecule_h_norm`-
    backed through the current transfer source value.
- New checkpoint (2026-03-06, step-8 attempt):
  - Added PLAN_77 invariant-set local-domain transfer seam:
    `MoleculeResidualFixedPointTransferOnSources`.
  - Added source-level constructors:
    `molecule_residual_fixed_point_transfer_source_of_on_sources`,
    `molecule_residual_fixed_point_data_source_of_existence_and_transfer_on_sources`.
  - Added current local-domain source pack and routed current transfer/data
    theorems through it:
    `molecule_residual_fixed_point_transfer_on_sources`,
    `molecule_residual_fixed_point_transfer_source_via_on_sources`,
    `molecule_residual_fixed_point_data_source_via_transfer_on_sources`.
  - Targeted probes:
    new local-domain transfer/data constructors are ground-axiom-only; current
    local-domain transfer/data routes remain `Molecule.molecule_h_norm`-backed
    through the current transfer model-source values.
