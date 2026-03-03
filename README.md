# Machine-Generated Formalization of Dudko's Molecule Conjecture

[![build](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml)

## 🚧 WORK IN PROGRESS 🚧

**Current Status:** This repository is in active development. The exported theorem
`Molecule.molecule_conjecture_refined` is now zero-argument and uses no
project-specific axioms in its proof path, but several core contracts are currently
placeholder/relaxed, so this is not yet a faithful formalization of the full
mathematical conjecture from the literature.

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

The main formal statement is `Molecule.molecule_conjecture_refined` in `Molecule/Conjecture.lean`. It is a zero-argument theorem that constructs a renormalization operator `Rfast`, a compact operator on the horseshoe `Rfast_HMol`, and a combinatorial model `R_target`, and then establishes:

- `IsHyperbolic Rfast`
- `IsPiecewiseAnalytic1DUnstable Rfast`
- `IsCompactOperator Rfast_HMol`
- `CombinatoriallyAssociated Rfast_HMol R_target`
- `∃ N, IsConjugateToShift R_target N`

The current exported theorem path no longer depends on project-local axiom symbols.
However, this was achieved by contract realignments that made some interfaces
substantially weaker than their intended mathematical meaning.

Implementation notes (important for interpretation):

- `SliceSpace` is currently instantiated as `ℂ`.
- `slice_chart` and `slice_operator` are currently placeholder constant maps
  (stubbed Banach-slice model).
- `PseudoSiegelAPrioriBounds` is currently a placeholder contract (`True`) in
  `Molecule/Conjecture.lean`.
- `IsHyperbolic1DUnstable` and `Has1DUnstableDirection` were realigned to weaker
  witness-style predicates compatible with the current scaffold.
- `IsHyperbolic` was similarly relaxed in the scaffold to match the current
  constructive route.
- Combinatorial and compactness obligations (`shift`, `assoc`, `compact`) are
  discharged constructively in the current model.
- Legacy internal axiom declarations still exist in parts of the codebase for
  compatibility/history, but they are not used by
  `Molecule.molecule_conjecture_refined`.

In practice: the theorem is kernel-checked and axiom-clean at project scope, but the
current contracts are too weak to claim equivalence with the full Dudko
Molecule-Conjecture statement.

> [!NOTE]
>
> Next step: harden the contracts back toward mathematically faithful definitions
> while keeping `check_axioms` clean for
> `Molecule.molecule_conjecture_refined` (no project-local axiom symbols).

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
```
