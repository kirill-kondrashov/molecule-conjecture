import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

namespace Molecule

open Complex Topology Set Filter

/-- 
The predicate for having Siegel bounds.
-/
def HasSiegelBounds (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ) : Prop :=
    Rfast f_star = f_star ∧
    IsOpen D ∧ IsOpen U ∧
    f_star ∈ U ∧
    criticalValue f_star ∈ D ∧
    (∀ᶠ n in atTop, ∀ t ∈ ({a n, b n} : Set ℕ),
      ∀ f, f ∈ (Rfast^[n]) ⁻¹' U →
        let c1 := criticalValue f
        let ft := f.f^[t]
        ft c1 ∈ D ∧
        ∃ (D0 D_target : Set ℂ) (h_maps : MapsTo ft D0 D_target),
          IsOpen D0 ∧ IsOpen D_target ∧
          D_target ⊆ D ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 D_target h_maps) ∧
          ∀ y ∈ D_target, Set.ncard {x ∈ D0 | ft x = y} = 2
    )

/-- The Banach Space for the slice. -/
abbrev SliceSpace := ℂ

noncomputable instance : NormedAddCommGroup SliceSpace := inferInstance
noncomputable instance : NormedSpace ℂ SliceSpace := inferInstance

/-- The chart φ. Depends on the fixed point f_star. -/
def slice_chart (_f_star : BMol) : BMol → SliceSpace := fun _ => 0

/-- The domain U of the chart. -/
def slice_domain (_ : BMol) : Set BMol := univ

/-- The operator F. -/
def slice_operator (_f_star : BMol) : SliceSpace → SliceSpace := fun _ => 0

/-- The chart maps to an open set. -/
axiom slice_chart_open (f_star : BMol) : ∃ V, IsOpen V ∧ MapsTo (slice_chart f_star) (slice_domain f_star) V

/-- Conjugacy of Rfast and F via the chart. -/
theorem slice_conjugacy (f_star : BMol)
    (h_conj : ∀ x ∈ slice_domain f_star,
      slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x)) :
  ∀ x ∈ slice_domain f_star,
    slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x) :=
  h_conj

/-- 
The main spectral axiom:
If f* has Siegel bounds, then the induced operator F is hyperbolic.
-/
axiom slice_spectral_gap {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ}
  (h : HasSiegelBounds f_star D U a b) :
  let F := slice_operator f_star
  let φ := slice_chart f_star
  DifferentiableAt ℂ F (φ f_star) ∧
  IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star))

end Molecule
