# PLAN: Strengthen `molecule-conjecture` Export Contract (Canonical Fixed Point)

Status: DONE
Progress: [##########] 100%
Last Updated: 2026-03-03

## Goal

Eliminate reliance on hidden internal axioms (`molecule_local_fixed_seed`, `molecule_h_norm`)
from the exported canonical fixed-point path by making the required fixed-point witness an
explicit part of the theorem contract.

---

## Current Problem

In current `strengthen` branch state:

- `molecule_conjecture_refined` is zero-argument and core-axiom-only.
- `canonical_rfast_has_fast_renormalizable_fixed_point` exists, but still depends on
  internal non-core assumptions (`molecule_h_norm`).
- `molecule_local_fixed_seed` remains present and still appears in downstream axiom frontiers
  via alternative fixed-point accessors.

This creates contract ambiguity: the stronger theorem appears exported, but its axiom budget
is still hidden inside internals.

---

## Required Contract Strengthening

### 1. Introduce explicit canonical fixed-point contract

In `Molecule/Conjecture.lean`, add:

```lean
def CanonicalFastFixedPointData : Prop :=
  ∃ g : BMol, IsFastRenormalizable g ∧ Molecule.Rfast g = g
```

### 2. Extend `MoleculeHypothesisPack`

Add field:

```lean
h_canonical_fixed : CanonicalFastFixedPointData
```

This makes the fixed-point witness explicit and auditable.

### 3. Rewrite canonical theorem to use the pack field directly

Replace internal proof route with:

```lean
theorem canonical_rfast_has_fast_renormalizable_fixed_point_of_pack
    (hpack : MoleculeHypothesisPack) :
    CanonicalFastFixedPointData := by
  exact hpack.h_canonical_fixed
```

No derivation from `molecule_h_norm` or `molecule_local_fixed_seed`.

### 4. Strengthen exported zero-argument theorem

Keep existing theorem for compatibility, and add:

```lean
theorem molecule_conjecture_refined_with_canonical_fixed_point_of_pack
    (hpack : MoleculeHypothesisPack) :
    MoleculeConjectureRefined ∧ CanonicalFastFixedPointData := by
  exact ⟨molecule_conjecture_refined_of_pack hpack, hpack.h_canonical_fixed⟩

theorem molecule_conjecture_refined_with_canonical_fixed_point :
    MoleculeConjectureRefined ∧ CanonicalFastFixedPointData := by
  exact molecule_conjecture_refined_with_canonical_fixed_point_of_pack
    molecule_hypothesis_pack
```

where `MoleculeConjectureRefined` is the current existential operator package proposition.

### 5. Remove/deprecate misleading internal fixed-point export path

Deprecate or stop exporting canonical fixed-point theorem proofs that rely on:

- `molecule_h_norm`
- `molecule_local_fixed_seed`

The public canonical path should only reflect explicit contract fields.

---

## Constructor Updates

Any constructor/theorem building `MoleculeHypothesisPack` must now provide:

- existing analytic/combinatorial fields
- `h_canonical_fixed`

Do not synthesize `h_canonical_fixed` from internal hidden axioms.

---

## Verification (must pass)

Add/update an upstream check script with:

```lean
#print axioms Molecule.molecule_conjecture_refined
#print axioms Molecule.molecule_conjecture_refined_with_canonical_fixed_point
#print axioms Molecule.canonical_rfast_has_fast_renormalizable_fixed_point
```

Acceptance criteria:

1. `molecule_conjecture_refined` remains core-only.
2. `molecule_conjecture_refined_with_canonical_fixed_point` contains only:
   - core Lean axioms, plus
   - explicit contract assumptions represented in `MoleculeHypothesisPack`.
3. No hidden dependence on `molecule_local_fixed_seed` or `molecule_h_norm` unless they are
   intentionally part of the explicit exported contract.

---

## Execution Log

- [x] Added explicit contract:
  - `CanonicalFastFixedPointData : Prop`
- [x] Extended `MoleculeHypothesisPack` with:
  - `h_canonical_fixed : CanonicalFastFixedPointData`
- [x] Rewired canonical theorem path:
  - `canonical_rfast_has_fast_renormalizable_fixed_point_of_pack` now returns
    `hpack.h_canonical_fixed` directly.
- [x] Added proposition alias:
  - `MoleculeConjectureRefined : Prop`
- [x] Added strengthened theorem pair:
  - `molecule_conjecture_refined_with_canonical_fixed_point_of_pack`
  - `molecule_conjecture_refined_with_canonical_fixed_point`
- [x] Ran axiom-audit checks directly with `lake env lean` + `#print axioms`.
- [x] Verified frontier:
  - `molecule_conjecture_refined`: core-only (`propext`, `Classical.choice`, `Quot.sound`)
  - canonical pair theorems: explicit contract dependency only via
    `Molecule.molecule_residual_assumptions` (no direct `molecule_h_norm` / `molecule_local_fixed_seed`).

---

## Downstream Impact (MLC repo)

After this lands upstream, downstream can route:

- from `Molecule.molecule_conjecture_refined_with_canonical_fixed_point`
- to `∃ g, IsFastRenormalizable g ∧ Rfast g = g`
- then to tower existence

and remove `Molecule.molecule_local_fixed_seed` from its axiom frontier, provided no other path
reintroduces it.
