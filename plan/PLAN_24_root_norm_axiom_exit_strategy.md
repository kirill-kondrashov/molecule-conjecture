# PLAN 24 - Root `h_norm` Axiom Exit Strategy

Status: DONE
Progress: [##########] 100%
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
- [x] Replace `molecule_h_fixed_data` / `molecule_h_spectral_data` global bridges with non-`h_norm` sources.
- [x] Remove remaining contradiction-based `molecule_h_*` witnesses from the zero-arg theorem path.
- [x] Close PLAN_11 unblocker condition.

## Current Outcome

- Added localized hyperbolicity route in `Molecule/Conjecture.lean`:
  - `Rfast_hyperbolicity_conjecture_localized`
- Switched the cutover theorem chain to localized fixed-point and gap-conjugacy contracts:
  - `molecule_conjecture_refined_with_localized_slice_data` now consumes
    `FixedPointNormalizationData`, `h_conj`, and `h_gap` (no packed spectral bridge).
- Extended packed assumptions with localized fixed-point witness:
  - `molecule_h_fixed_data`
- Minimized packed top-theorem assumptions to only active localized fields
  (removed unused legacy `h_norm`/`h_spectral_data` fields from the pack).
- Replaced global bridge for fixed-point data with localized extraction:
  - `fixed_point_normalization_data_of_invariant_slice_data`
  - `molecule_h_fixed_data` now uses localized `h_data`.
- Removed the packed spectral-data bridge and rerouted localized hyperbolicity through:
  - `h_conj` + `h_gap` + localized bounds (`bounds_imply_hyperbolicity_proof` path).
- `check_axioms` no longer reports `Molecule.molecule_h_norm`.
- Remaining project axiom moved to:
  - `Molecule.molecule_core_assumptions`
