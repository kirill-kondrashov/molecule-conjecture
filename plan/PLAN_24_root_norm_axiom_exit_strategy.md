# PLAN 24 - Root `h_norm` Axiom Exit Strategy

Status: ACTIVE
Progress: [########--] 80%
Scope: Remove the final dependency on `Molecule.molecule_h_norm` by replacing remaining global-normalization theorem inputs with local fixed-point/spectral contracts.
Acceptance: `check_axioms` for `molecule_conjecture_refined` no longer lists `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/HyperbolicityTheorems.lean`, `Molecule/Problem4_3.lean`
Stuck Rule: STUCK if every route still requires deriving data from the contradictory global statement `∀ K, ...`.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Isolate exact proof edges still forcing `h_norm` in the top theorem path.
- [x] Introduce local-contract theorem variants for those edges.
- [x] Switch top theorem chain to the local-contract variants.
- [x] Re-run axiom audit.
- [x] Remove unused legacy fields from packed top-theorem assumptions.
- [ ] Replace `molecule_h_fixed_data` / `molecule_h_spectral_data` global bridges with non-`h_norm` sources.
- [ ] Close PLAN_11.

## Current Outcome

- Added localized hyperbolicity route in `Molecule/Conjecture.lean`:
  - `Rfast_hyperbolicity_conjecture_localized`
- Switched the cutover theorem chain to localized fixed-point/spectral contracts:
  - `molecule_conjecture_refined_with_localized_slice_data` now consumes
    `FixedPointNormalizationData` and spectral data directly.
- Extended packed assumptions with localized witnesses:
  - `molecule_h_fixed_data`
  - `molecule_h_spectral_data`
- Minimized packed top-theorem assumptions to only active localized fields
  (removed unused legacy `h_norm`/`h_conj`/`h_gap`/`h_unique` fields from the pack).
- Audit after cutover still reports one project axiom dependency:
  - `Molecule.molecule_h_norm`
