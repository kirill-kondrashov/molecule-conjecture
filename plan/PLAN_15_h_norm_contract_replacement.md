# PLAN 15 - Replace Global `h_norm` Contract

Status: ACTIVE
Progress: [####------] 40%
Scope: Remove dependence on the contradictory global `h_norm` by replacing theorem interfaces with localized normalization contracts.
Acceptance: `molecule_conjecture_refined` no longer depends on `molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/HyperbolicityTheorems.lean`
Stuck Rule: STUCK if interface replacement forces project-wide rewrite without a compilable migration bridge.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Introduce replacement signatures using localized normalization package.
- [ ] Migrate top-level theorem path to replacement signatures.

## Current Outcome

- Added `FixedPointNormalizationData` and
  `problem_4_3_bounds_established_of_fixed_point_data` in `Molecule/Problem4_3.lean`.
- Legacy Problem 4.3 theorem now bridges through the localized signature.
- Top-level export now routes through `molecule_conjecture_refined_of_pack`
  (non-ex-falso path), but still carries `h_norm` via packed assumptions.
