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
- Expanding one layer further gives the exact four residual inputs on this
  branch:
  renormalizability, `V`-bound transfer, local orbit-at, and direct
  uniqueness.
- The parameterized four-input theorem is ground-axiom-only, and the
  corresponding current-route alias inherits exactly the non-ground debt of
  those four inputs.
- The same branch can now also be written with the more primitive
  hybrid-class-collapse carrier in place of direct uniqueness.
- That rewrite does not further reduce the axiom frontier; it just exposes the
  same remaining debt one wrapper lower.
- Targeted probes show that this alias has the same axiom footprint as both
  `molecule_residual_canonical_fast_fixed_point_data_source` and the current
  `molecule_residual_fixed_point_existence_source`.
- So PLAN_84 is now complete as a seed-replacement / handoff plan.
- The remaining question on this branch is upstream only. After fully
  expanding the seeded route, the residual non-ground frontier is:
  - fixed-point renormalizability
  - `V`-bound transfer
  - local orbit-at
  - hybrid-class collapse
- `PLAN_85_upstream_four_carrier_burndown.md` is now complete as a
  burndown/handoff plan.
- `PLAN_86_localized_or_reseeded_R_replacement.md` is now complete as a
  structural handoff plan for that frontier.
- `PLAN_87_non_circular_critical_seed_source.md` isolated the exact seed-side
  theorem target, but was too narrow as a master research program.
- `PLAN_88_dual_track_seed_or_non_singleton_localized_bridge.md` is now the
  active research program.
- The PLAN_86 localized branch is now concrete on a seed-based refined
  singleton domain:
  `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_of_renormalizable_fixed_seed_source`,
  with bridge/existence cutovers
  `molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain`
  and
  `molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain`.
- Targeted probes show that localized seed-domain route is ground-axiom-only.
  Under the current refined witness, however, it is still only a singleton
  domain, so the live missing step is either:
  - a non-circular producer of the seed, or
  - a genuinely larger live domain `K`.
- The current localized refined-singleton route is now also explicitly reduced
  back to the seed source:
  `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_renormalizable_fixed_seed_source`.
  So at present it is a clean reformulation of the reseeded route, not an
  independent larger-domain replacement.
- That same localized refined-singleton route is now also explicitly equivalent
  to canonical fast fixed-point data:
  `molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_canonical_fast_fixed_point_data_source`.
  So under the current refined witness, the localized branch, reseeded branch,
  and canonical seed route all collapse to the same upstream debt.
- The exact remaining localized target is now explicit:
  `MoleculeResidualNonSingletonLocalizedBridgeSources`.
  The theorem
  `no_nontrivial_member_of_refined_invariant_fixed_seed_singleton_domain_sources`
  shows the current refined singleton route cannot supply that target, so any
  real localized breakthrough must come from a genuinely larger live domain `K`.
- The downstream `PLAN_80` / `PLAN_78` rebase requirement is now also exact:
  replacement existence alone is not enough. The clean parameterized cutovers
  show those branches need:
  - a replacement existence theorem,
  - fixed-point critical-value transfer, and
  - renormalizable-point `V`-bound control.
- The structural handoff is now complete on the localized side:
  a non-singleton localized bridge source would already propagate to
  existence, canonical fast fixed-point data, fixed-data, and local-witness
  through ground-axiom-only cutovers.
- Critical revision of the research program:
  seed search and larger-domain localized search should not be treated as a
  primary route plus a fallback.
  They are the two co-equal live upstream targets after the structural work.
- Second critical revision:
  an upstream theorem hit is not yet a full replacement theorem.
  The downstream interface still needs:
  - fixed-point critical-value transfer, and
  - renormalizable-point `V`-bound control (`RV`)
  before fixed-data/local-witness can be rebuilt.
- Third critical revision:
  a localized-side candidate does not count if its domain/bridge package only
  repackages a seed theorem or bakes `IsFastRenormalizable` into the domain.
- Fourth critical revision:
  the active master program should not claim ownership of those sidecar
  carriers. They remain owned by the existing downstream plans
  `PLAN_80`, `PLAN_78`, and `PLAN_53`.
- New coordination checkpoint:
  once fixed-point critical-value transfer is supplied, both active upstream
  tracks now meet at the same stronger seed contract:
  `MoleculeResidualCriticalRenormalizableFixedSeedSource`.
- On the seed-side branch, the exact external gate is now fully explicit:
  canonical fast fixed-point data + critical-value transfer + `RV`
  already yields fixed-data and local-witness through ground-axiom-only
  cutovers.
- So the current active theorem search is now split explicitly into:
  - seed-side target:
    `MoleculeResidualCriticalRenormalizableFixedSeedSource`
  - localized-side target:
    `MoleculeResidualNonSingletonLocalizedBridgeSources`
- Any candidate on either side only counts if it escapes the already-known
  singleton/canonical equivalence class.
- Full downstream progress still requires the separate sidecar carrier plans to
  land:
  - fixed-point critical-value transfer
  - renormalizable-point `V`-bound control (`RV`)
- The first PLAN_85 package theorem,
  `molecule_residual_fixed_point_existence_source_of_upstream_four_carrier_sources`,
  is ground-axiom-only; the current package and current-route alias inherit
  exactly the four packaged carriers.
- The shared witness-side pair is now also packaged explicitly:
  `MoleculeResidualWitnessPairSources`.
- Parameterized pair-level theorems for fixed-data and local witness are
  ground-axiom-only; the current pair package inherits exactly the current
  witness-side debt.
- The PLAN_85 witness-side pair has now been shrunk once more:
  on the seeded existence / fixed-data / local-witness branch it uses
  renormalizable-point `V`-bound control
  (`MoleculeResidualRenormVBoundSource`)
  instead of fixed-point `V`-bound transfer.
- The canonical branch is now also threaded through the same explicit
  upstream package, so its current wrapper debt is exactly the same
  four-carrier tuple `(R, RV, O, H)`.
- The active current fixed-data, local-witness, and canonical theorems have
  now been cut over one step further: their live current debt is just the
  witness-side pair `(R, RV)`.
- The current canonical theorem has then been cut one step further again:
  it now routes directly through the current existence theorem, so its active
  current debt is just `R`.
- So `O` and `H` are no longer on the active current canonical route; they
  remain only on alternate seeded/package routes.
- The remaining direct global witness-side carrier `R` is now explicitly
  certified false in the current scaffold
  (`no_molecule_residual_fixed_point_renormalizable_source`), so the active
  existence/canonical route cannot be completed by proving global `R`.
  Any further elimination on that side must replace `R` by a localized or
  reseeded theorem.
- The localized and reseeded replacement branches now share a clean singleton
  bridge seam built from an abstract renormalizable fixed seed:
  `molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source`.
  So the remaining question on that side is no longer bridge structure; it is
  how to produce a non-circular seed (or a larger live domain `K`).
- The seeded existence branch can now be stated as:
  shared witness-side pair + local orbit-at + hybrid-class collapse.

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
