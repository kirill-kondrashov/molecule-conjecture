# PLAN 77 - Upstream Model Change For Non-h_norm Fixed-Point Sources

Status: ACTIVE
Progress: [######----] 60%
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
- [ ] Rebuild `molecule_residual_fixed_point_uniqueness_direct_source` from
  non-circular hybrid collapse/lift uniqueness seams.
- [ ] Rebuild `molecule_residual_canonical_fast_fixed_point_data_source` from
  the non-`molecule_h_norm` fixed-point data source.
- [ ] Re-run PLAN_76 cutover using the new upstream sources and probe axiom
  signatures at zero-arg and top-level frontiers.
- [ ] Run `make build` and `make check`.

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Upstream model-obstruction inventory | Core contradictions and dependency hotspots are explicit and linked to source theorems. | [###-------] 30% |
| Existence-source upstream replacement | Added restricted bridge-on source seam and existence constructor (`molecule_residual_fixed_point_existence_source_of_bridge_on`), then rerouted active `molecule_residual_fixed_point_existence_source` via bridge-on path; constructor seams are ground-axiom-only, active route is still `molecule_h_norm`-backed via current fixed-point data source. | [####------] 40% |
| Uniqueness-source upstream replacement | Added model-sources-based direct-uniqueness seam (`molecule_residual_fixed_point_uniqueness_direct_source_of_model_sources`) and routed PLAN_76 cutover-ingredients plus later uniqueness consumers through `molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources`; seam constructors are ground-axiom-only, current model-source value remains `molecule_h_norm`-backed. | [###-------] 30% |
| Canonical-source upstream replacement | Active `molecule_residual_canonical_fast_fixed_point_data_source` now routes through `molecule_residual_fixed_point_existence_source`; constructor seam is ground-axiom-only, active canonical source still inherits `molecule_h_norm` from the current existence theorem. | [##--------] 20% |
| PLAN_76 downstream cutover readiness | PLAN_76 routing seams are mature; cutover-ingredients and downstream uniqueness consumers now consume model-sources-based direct uniqueness, and the active canonical source now consumes the upstream existence seam. Remaining blocker is the current upstream source values. | [########--] 80% |

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
