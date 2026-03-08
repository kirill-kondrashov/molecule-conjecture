# Machine-Generated Formalization of Dudko's Molecule Conjecture

[![build](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml)

## 🚧 WORK IN PROGRESS 🚧

**Current Status:** This repository is in active development.

- `Molecule.molecule_conjecture_refined` is zero-argument and currently has
  one remaining project-specific axiom symbol in its proof path:
  `Molecule.molecule_h_norm`.
- The legacy `InvariantSliceDataWithNormalization` route is now certified as a
  dead end in the current scaffold.
- The active live blocker is
  `Molecule.molecule_residual_fixed_point_data_source`, which is still routed
  through `molecule_h_fixed_data_direct`.

Several core contracts are still placeholder/relaxed, so this is not yet a faithful
formalization of the full mathematical conjecture from the literature.

This repository contains a **machine-generated attempt of formal proof** of Dudko's Molecule Conjecture for quadratic polynomials in Lean 4. This theorem is a key component of the Mandelbrot Local Connectivity (MLC) Conjecture, establishing it for non-renormalizable parameters.

Essentially, this software facilitates progress toward an exact proof **in collaboration** with human verification, leveraging the rigor of formalization in Lean.

> [!NOTE]
> This is a work in progress. Updates will be posted when (or if ☺) the proof is fully verified. This repository is shared at an early stage to simplify collaboration.

The primary benefit of using Lean is that the logic is verified by the Lean kernel,
ensuring correctness relative to the definitions and axioms provided. Some essential
parts, such as definitions, useful lemmas, and theorem skeletons from the literature,
are included.

## Disclaimer

> [!NOTE]
> **This is an AI-assisted attempt to formalize modern mathematics.**
>
> The code and documentation in this repository were produced by a combination of AI assistance and manual refinement. While the definitions and logical structure are checked by the Lean 4 kernel, the choice of axioms and the mathematical fidelity of the formalization to the standard literature require expert verification.

## Formalization Status

The main formal statement is `Molecule.molecule_conjecture_refined` in
`Molecule/Conjecture.lean`. It is a zero-argument theorem that constructs a
renormalization operator `Rfast`, a compact operator on the horseshoe
`Rfast_HMol`, and a combinatorial model `R_target`, and then establishes:

- `IsHyperbolic Rfast`
- `IsPiecewiseAnalytic1DUnstable Rfast`
- `IsCompactOperator Rfast_HMol`
- `CombinatoriallyAssociated Rfast_HMol R_target`
- `∃ N, IsConjugateToShift R_target N`

The refined theorem path above is reduced to one remaining project-local axiom
symbol: `Molecule.molecule_h_norm`. Most structural routing around that axiom is
now explicit, and one legacy upstream branch has been closed as inconsistent in
the current model. What remains is an upstream witness-construction problem,
not another routing problem.

There is now an explicit canonical fixed-point contract:

- `CanonicalFastFixedPointData : Prop := ∃ g : BMol, IsFastRenormalizable g ∧ Molecule.Rfast g = g`
- `MoleculeHypothesisPack` includes `h_canonical_fixed : CanonicalFastFixedPointData`
- `canonical_rfast_has_fast_renormalizable_fixed_point_of_pack` reads this field directly
- `molecule_conjecture_refined_with_canonical_fixed_point_of_pack` exports
  `MoleculeConjectureRefined ∧ CanonicalFastFixedPointData`

So the canonical fixed-point route is contract-explicit at pack level (no hidden
derivation through `molecule_h_norm`/`molecule_local_fixed_seed`), while the
zero-argument canonical export still depends on the current residual contract axiom
`Molecule.molecule_residual_assumptions`.

Current axiom frontier:

- `check_axioms Molecule.molecule_conjecture_refined` currently reports
  `propext`, `Quot.sound`, `Classical.choice`, and `Molecule.molecule_h_norm`.
- The old normalized invariant-slice-data seam is formally closed by
  `no_molecule_residual_invariant_slice_data_with_normalization_source`.
- The remaining live transfer-side blocker is
  `molecule_residual_fixed_point_data_source`.
- Ground-axiom-only constructors already exist for:
  - `fixed_point_normalization_data_of_fixed_exists_and_transfer`
  - `fixed_point_normalization_data_of_ingredients`
  - `fixed_point_normalization_data_of_invariant_slice_data`
- What is missing is a non-`molecule_h_norm` producer for one of those
  constructor inputs, ideally a direct single-reference witness of
  `FixedPointNormalizationData`.
- Fallback live route: replace the pair
  `MoleculeResidualFixedPointExistenceSource` +
  `MoleculeResidualFixedPointTransferSource`, then rebuild fixed-point data from
  `fixed_point_normalization_data_of_fixed_exists_and_transfer`.
- The current split carriers are now explicit:
  `molecule_residual_fixed_point_existence_source_via_fixed_data_direct` and
  `molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct`.
- Preferred next attack: the existence half first, because it has fewer
  dependencies than the transfer half.
- The existence half is now reduced further:
  `MoleculeResidualFixedPointExistenceSource` is ground-axiom-only equivalent to
  `MoleculeResidualCanonicalFastFixedPointDataSource`.
- The current canonical theorem is now routed through the smaller triple:
  `MoleculeResidualFixedPointNormalizationIngredients`,
  `MoleculeResidualOrbitClauseAtSource`,
  and `MoleculeResidualFixedPointUniquenessDirectSource`.
- Concretely, the active theorem carriers on that branch are now:
  `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`,
  `molecule_residual_orbit_clause_at_source`,
  and `molecule_residual_fixed_point_uniqueness_direct_source`.
- Under the fixed-data branch itself, the current carrier now splits into:
  `molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct`,
  built from the ground theorem `fixed_point_exists` plus three direct
  non-ground carriers.
- Concretely, the remaining fixed-data debt is concentrated in
  `molecule_residual_fixed_point_renormalizable_via_global_norm_direct`,
  `molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct`,
  and
  `molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct`.
- The current transfer theorem now also routes through the same primitive
  ingredient carrier plus direct uniqueness, so the transfer branch no longer
  hides an extra `FixedPointNormalizationData` wrapper.

Implementation notes (important for interpretation):

- `SliceSpace` is currently instantiated as `ℂ`.
- `slice_chart` and `slice_operator` are currently placeholder constant maps
  (stubbed Banach-slice model).
- `PseudoSiegelAPrioriBounds` is now defined through the explicit
  `PseudoSiegelAPrioriBoundsStatement` contract in
  `Molecule/Conjecture.lean`.
- `IsHyperbolic1DUnstable` and `Has1DUnstableDirection` were realigned to weaker
  witness-style predicates compatible with the current scaffold.
- `IsHyperbolic` was similarly relaxed in the scaffold to match the current
  constructive route.
- Combinatorial and compactness obligations (`shift`, `assoc`, `compact`) are
  discharged constructively in the current model.
- Legacy internal axiom declarations still exist in parts of the codebase for
  compatibility/history.
  They are not used by `Molecule.molecule_conjecture_refined`; the canonical
  zero-argument strengthened export currently uses
  `Molecule.molecule_residual_assumptions` as its explicit contract source.

In practice: the refined theorem is kernel-checked and reduced to one residual
project-local axiom, while the canonical fixed-point strengthened export is
kernel-checked but explicitly assumption-bearing via residual contract data.
Current contracts are still too weak to claim equivalence with the full Dudko
Molecule-Conjecture statement.

> [!NOTE]
>
> Next step: replace the current `molecule_h_fixed_data_direct` carrier with a
> non-`molecule_h_norm` witness theorem for `FixedPointNormalizationData`, then
> reroute `molecule_residual_fixed_point_data_source` and downstream local-
> witness/transfer theorems through it.

## Verification

To verify the proof and check for any remaining gaps (the `sorry` keyword in Lean), run:

```bash
make check
```

This will analyze the codebase and output any axioms or unproven statements used.

**Current expected output (for `Molecule.molecule_conjecture_refined`):**
```
✅ The proof of 'Molecule.molecule_conjecture_refined' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
- Molecule.molecule_h_norm
```
