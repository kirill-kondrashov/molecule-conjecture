import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

namespace MLC

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
        ∃ (D0 : Set ℂ) (h_maps : MapsTo ft D0 D),
          IsOpen D0 ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 D h_maps) ∧
          ∀ y ∈ D, Set.ncard {x ∈ D0 | ft x = y} = 2
    )

/-- The Banach Space for the slice. -/
axiom SliceSpace : Type
axiom SliceSpace_normedGroup : NormedAddCommGroup SliceSpace
noncomputable instance : NormedAddCommGroup SliceSpace := SliceSpace_normedGroup
axiom SliceSpace_normedSpace : NormedSpace ℂ SliceSpace
noncomputable instance : NormedSpace ℂ SliceSpace := SliceSpace_normedSpace

/-- The chart φ. Depends on the fixed point f_star. -/
axiom slice_chart (f_star : BMol) : BMol → SliceSpace

/-- The domain U of the chart. -/
def slice_domain (f_star : BMol) : Set BMol := univ

/-- The operator F. -/
axiom slice_operator (f_star : BMol) : SliceSpace → SliceSpace

/-- The chart maps to an open set. -/
axiom slice_chart_open (f_star : BMol) : ∃ V, IsOpen V ∧ MapsTo (slice_chart f_star) (slice_domain f_star) V

/-- Conjugacy of Rfast and F via the chart. -/
axiom slice_conjugacy (f_star : BMol) : 
  ∀ x ∈ slice_domain f_star, slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x)

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

end MLC
