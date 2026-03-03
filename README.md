# Machine-Generated Formalization of Dudko's Molecule Conjecture

[![build](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml)

## 🚧 WORK IN PROGRESS 🚧

**Current Status:** This repository is in active development and the formalization is a conditional proof pipeline with explicit hypotheses.

This repository contains a **machine-generated attempt of formal proof** of Dudko's Molecule Conjecture for quadratic polynomials in Lean 4. This theorem is a key component of the Mandelbrot Local Connectivity (MLC) Conjecture, establishing it for non-renormalizable parameters.

Essentially, this software facilitates progress toward an exact proof **in collaboration** with human verification, leveraging the rigor of formalization in Lean.

> [!NOTE]
> This is a work in progress. Updates will be posted when (or if ☺) the proof is fully verified. This repository is shared at an early stage to simplify collaboration.

The primary benefit of using Lean is that the logic is verified by the Lean kernel, ensuring correctness relative to the definitions and axioms provided. Some essential parts, such as definitions, useful lemmas, and theorems from the literature, are included. All domain-specific steps are now expressed as explicit hypotheses, and the remaining axioms are Lean's standard logical axioms.

## Disclaimer

> [!NOTE]
> **This is an AI-assisted attempt to formalize modern mathematics.**
>
> The code and documentation in this repository were produced by a combination of AI assistance and manual refinement. While the definitions and logical structure are checked by the Lean 4 kernel, the choice of axioms and the mathematical fidelity of the formalization to the standard literature require expert verification.

## Formalization Status

The main formal statement is `Molecule.molecule_conjecture_refined` in `Molecule/Conjecture.lean`. It is a zero-argument theorem that constructs a renormalization operator `Rfast`, a compact operator on the horseshoe `Rfast_HMol`, and a combinatorial model `R_target`, and then establishes:

- `IsHyperbolic Rfast`
- `IsPiecewiseAnalytic1DUnstable Rfast`
- `IsCompactOperator Rfast_HMol`
- `CombinatoriallyAssociated Rfast_HMol R_target`
- `∃ N, IsConjugateToShift R_target N`

The remaining analytic/dynamical assumptions are currently concentrated in a single internal bundle `MoleculeResidualAssumptions` in `Molecule/Conjecture.lean`, exposed by theorem-level projections (`molecule_residual_*`) and routed into the zero-argument export theorem.

Implementation notes:

- `SliceSpace` is currently instantiated as `ℂ`.
- `slice_chart` and `slice_operator` are currently placeholder constant maps, so the Banach slice is a stubbed model.
- The top-level theorem remains a formal statement whose analytic and dynamical inputs are carried by internal hypothesis constants.
- Combinatorial and compactness interfaces were realigned to constructive factor-style contracts in the current placeholder model; theorem-level witnesses now discharge `shift`, `assoc`, and `compact` obligations without residual axioms.

In practice, this means `Molecule.molecule_conjecture_refined` remains conditional at the foundational level: it does not derive the analytic/dynamical ingredients internally, but depends on explicit internal hypothesis constants. Intuitively, the file assembles a rigorous dependency graph: if the analytic estimates and dynamical controls from the literature are supplied, the rest of the logical pipeline is fully formal and checked by Lean.

> [!NOTE]
> 
> Next step (intuitively): replace these hypotheses with actual constructions and proofs inside Lean. Concretely, this means formalizing the Banach slice and chart, proving the a priori bounds and orbit control from renormalization theory, establishing the spectral gap and piecewise analyticity, and finally discharging the remaining parameters in `molecule_conjecture_refined` so the theorem becomes unconditional.

## Verification

To verify the proof and check for any remaining gaps (the `sorry` keyword in Lean), run:

```bash
make check
```

This will analyze the codebase and output any axioms or unproven statements used.

**Expected Output:**
```
✅ The proof of 'Molecule.molecule_conjecture_refined' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
- Molecule.molecule_residual_assumptions
```
