# Machine-Generated Formalization of Dudko's Molecule Conjecture

[![build](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml)

## 🚧 WORK IN PROGRESS 🚧

**Current Status:** This repository is in active development.

- `Molecule.molecule_conjecture_refined` is zero-argument and currently has
  one remaining project-specific axiom symbol in its proof path:
  `Molecule.molecule_h_norm`.
- The legacy `InvariantSliceDataWithNormalization` route is now certified as a
  dead end in the current scaffold.
- The active live frontier is now explicit after expansion of the current
  theorem bodies: a small set of direct fixed-point carriers plus one
  canonical orbit carrier.

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
- Ground-axiom-only constructors already exist for:
  - `fixed_point_normalization_data_of_fixed_exists_and_transfer`
  - `fixed_point_normalization_data_of_ingredients`
  - `fixed_point_normalization_data_of_invariant_slice_data`
- After expanding the current theorem bodies, the remaining missing statements
  are best expressed directly in mathematical notation.

Shared witness-side frontier:
```text
(R)  forall f : BMol,
       Rfast f = f -> IsFastRenormalizable f

(V)  forall f : BMol,
       Rfast f = f -> IsFastRenormalizable f ->
       f.V subset Metric.ball 0 0.1
```

- The literal full-domain `(R)` above is not a viable constructive target in
  the current scaffold:
  `no_fixed_point_implies_renormalizable` blocks that bridge.
- The active research program therefore targets a localized replacement:
```text
(R_K)  exists K : Set BMol,
         (exists f : BMol, f in K /\ Rfast f = f) /\
         (forall f : BMol, f in K -> Rfast f = f -> IsFastRenormalizable f)
```
- Operationally, this means proving `FixedPointImpliesRenormalizableOn K` for a
  live domain `K` and composing it with the existing fixed-point-in-`K`
  theorem.
- That localized route is now blocked in the current scaffold when seeded from
  `fixed_point_exists`, because the chosen witness ultimately traces back to
  `defaultBMol`.
- The next live direction is therefore a seed-replacement program:
```text
(S)  produce f_seed : BMol with
       IsFastRenormalizable f_seed /\ Rfast f_seed = f_seed
     from canonical or renormalizable fixed-point data,
     without using fixed_point_exists
```
- Once such an `f_seed` exists, the singleton-bridge / identification machinery
  can be rebuilt around `f_seed` rather than `selected_fixed_point`.
- This seed-replacement route is now explicit in the code:
```text
MoleculeResidualRenormalizableFixedSeedSource
  <-> MoleculeResidualCanonicalFastFixedPointDataSource
```
- The canonical seeded existence route
  `molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source_via_seed`
  is ground-axiom-only.
- The concrete current-route alias
  `molecule_residual_fixed_point_existence_source_via_canonical_fast_fixed_point_data_source`
  now exposes that seeded route directly from the current canonical source.
- Its fully expanded form
  `molecule_residual_fixed_point_existence_source_via_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed`
  shows the exact remaining inputs on this branch: fixed-data, local orbit-at,
  and direct uniqueness.
- The parameterized expanded theorem
  `molecule_residual_fixed_point_existence_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed`
  is ground-axiom-only, so the residual non-ground debt on the current route is
  exactly those three inputs.
- Targeted probes show that this alias has the same axiom footprint as both
  `molecule_residual_canonical_fast_fixed_point_data_source` and the current
  `molecule_residual_fixed_point_existence_source`.
- So the PLAN_84 structural debt is now discharged. The remaining question on
  this branch is upstream only: can canonical fast fixed-point data itself be
  produced without `Molecule.molecule_h_norm`?

Transfer-only additional frontier:
```text
(C)  forall f : BMol,
       Rfast f = f -> IsFastRenormalizable f ->
       criticalValue f = 0
```

Canonical-only additional frontier:
```text
(O)  forall (f_star : BMol) (D : Set Complex) (U : Set BMol)
            (a b : Nat -> Nat),
       Rfast f_star = f_star ->
       IsFastRenormalizable f_star ->
       IsOpen D -> IsOpen U ->
       f_star in U ->
       criticalValue f_star in D ->
       MoleculeOrbitClauseAt D U a b
```

- The ground theorem
  `fixed_point_exists : exists f : BMol, Rfast f = f /\ criticalValue f = 0`
  is already available without `Molecule.molecule_h_norm`.
- So, after expanding definitions, what is exactly missing is:
  - for the existence branch: prove `(R)`;
  - for the data/local-witness branch: prove `(R)` and `(V)`;
  - for the transfer / `...via_on_sources` branch: prove `(C)` and `(V)`;
  - for the canonical branch: prove `(R)`, `(V)`, and `(O)`.
- Equivalently, a full elimination of `Molecule.molecule_h_norm` now reduces to
  replacing those direct frontier contracts with non-axiomatic proofs.

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
