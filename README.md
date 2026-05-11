# Machine-Generated Formalization of Dudko's Molecule Conjecture

[![build](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/molecule-conjecture/actions/workflows/lean_action_ci.yml)

## Current Status

This repository is an active Lean 4 formalization effort around Dudko's
Molecule Conjecture.

The main theorem is `Molecule.molecule_conjecture_refined` in
`Molecule/Conjecture.lean`. It is a zero-argument theorem that constructs:

- a renormalization operator `Rfast : BMol -> BMol`,
- a horseshoe operator `Rfast_HMol : HMol -> HMol`,
- a combinatorial model `R_target`,

and establishes:

- `IsHyperbolic Rfast`,
- `IsPiecewiseAnalytic1DUnstable Rfast`,
- `IsCompactOperator Rfast_HMol`,
- `CombinatoriallyAssociated Rfast_HMol R_target`,
- `∃ N, IsConjugateToShift R_target N`.

## Current Axiom Frontier

`check_axioms Molecule.molecule_conjecture_refined` currently reports one
remaining project-local axiom:

- `Molecule.molecule_h_norm`

Along with the Lean core axioms:

- `propext`
- `Quot.sound`
- `Classical.choice`

So the current repo frontier is:

\[
\texttt{Molecule.molecule\_h\_norm}
\]

## Current Interpretation of the Remaining Gap

The repository already contains the main routing and packaging around the final
theorem. The remaining work is an upstream witness/source construction problem
for the last residual contract, not a basic theorem-wiring problem.

At the current level of abstraction, the missing control is reflected in the
following frontier contracts:

```text
(R)  forall f : BMol,
       Rfast f = f -> IsFastRenormalizable f

(V)  forall f : BMol,
       Rfast f = f -> IsFastRenormalizable f ->
       f.V subset Metric.ball 0 0.1

(C)  forall f : BMol,
       Rfast f = f -> IsFastRenormalizable f ->
       criticalValue f = 0

(O)  forall (f_star : BMol) (D : Set Complex) (U : Set BMol)
            (a b : Nat -> Nat),
       Rfast f_star = f_star ->
       IsFastRenormalizable f_star ->
       IsOpen D -> IsOpen U ->
       f_star in U ->
       criticalValue f_star in D ->
       MoleculeOrbitClauseAt D U a b
```

In current repo terms, eliminating `Molecule.molecule_h_norm` means replacing
the relevant remaining frontier contracts with non-axiomatic proofs.

## Current Plan Split

The current planning split is:

- `PLAN_88` — governing route plan,
- `PLAN_90` / `PLAN_91` — active operational queue,
- `PLAN_93` — sidecar roadmap for literature-guided future directions.

## Verification

Run:

```bash
make build
make check
./scripts/verify_output.sh
```

`make check` reports the axioms used by
`Molecule.molecule_conjecture_refined`.

**Current expected output (for `Molecule.molecule_conjecture_refined`):**
<!-- EXPECTED_CHECK_OUTPUT_START -->
```
✅ The proof of 'Molecule.molecule_conjecture_refined' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
- Molecule.molecule_h_norm
```
<!-- EXPECTED_CHECK_OUTPUT_END -->

## Disclaimer

This is an AI-assisted formalization effort. Lean checks the logical structure
relative to the definitions and axioms present in the codebase, but the
mathematical fidelity of the model and the choice of remaining axioms still
require expert review.
