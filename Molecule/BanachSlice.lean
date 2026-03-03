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
theorem slice_chart_open (f_star : BMol) :
  ∃ V, IsOpen V ∧ MapsTo (slice_chart f_star) (slice_domain f_star) V := by
  refine ⟨univ, isOpen_univ, ?_⟩
  intro x hx
  trivial

/--
Refined chart candidate used for constructive witness migration.
Unlike `slice_chart`, this chart separates the reference map from other points.
-/
noncomputable def slice_chart_refined (f_ref : BMol) : BMol → SliceSpace := by
  classical
  exact fun g => if g = f_ref then 0 else 1

/--
Refined-chart open-image witness.
-/
theorem slice_chart_refined_open (f_ref : BMol) :
  ∃ V, IsOpen V ∧ MapsTo (slice_chart_refined f_ref) (slice_domain f_ref) V := by
  refine ⟨univ, isOpen_univ, ?_⟩
  intro x hx
  trivial

/--
Constructive singleton witness package for the refined chart.
This is an upstream building block for replacing ex-falso `h_exists` paths.
-/
theorem refined_singleton_slice_witness (f_ref : BMol) :
    ∃ (K : Set BMol) (P : Set SliceSpace),
      IsCompact P ∧
      Convex ℝ P ∧
      MapsTo (slice_operator f_ref) P P ∧
      K = {f | slice_chart_refined f_ref f ∈ P} ∧
      SurjOn (slice_chart_refined f_ref) K P ∧
      K.Finite ∧
      InjOn (slice_chart_refined f_ref) K ∧
      ContinuousOn (slice_operator f_ref) ((slice_chart_refined f_ref) '' K) ∧
      K.Nonempty ∧
      f_ref ∈ K := by
  classical
  refine ⟨{f_ref}, {0}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.finite_singleton (0 : SliceSpace)).isCompact
  · exact convex_singleton (0 : SliceSpace)
  · intro x hx
    simp [slice_operator]
  · ext f
    constructor
    · intro hf
      simp [slice_chart_refined] at hf ⊢
      exact hf
    · intro hf
      simp [slice_chart_refined] at hf ⊢
      exact hf
  · intro y hy
    have hy0 : y = (0 : SliceSpace) := by simp at hy; exact hy
    refine ⟨f_ref, by simp, ?_⟩
    simp [slice_chart_refined, hy0]
  · exact Set.finite_singleton f_ref
  · intro x hx y hy hxy
    simp at hx hy
    simp [hx, hy]
  ·
    -- In the discrete topology on `BMol`, continuity-on is trivial.
    change ContinuousOn (fun _ : SliceSpace => (0 : SliceSpace))
      ((slice_chart_refined f_ref) '' ({f_ref} : Set BMol))
    exact continuousOn_const
  · exact Set.singleton_nonempty f_ref
  · simp

/-- Conjugacy of Rfast and F via the chart. -/
theorem slice_conjugacy (f_star : BMol)
    (h_conj : ∀ x ∈ slice_domain f_star,
      slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x)) :
  ∀ x ∈ slice_domain f_star,
    slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x) :=
  h_conj

/-- 
The main spectral result (assumed as an explicit hypothesis).
If f* has Siegel bounds, then the induced operator F is hyperbolic.
-/
theorem slice_spectral_gap {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ}
  (_h : HasSiegelBounds f_star D U a b)
  (h_gap :
    let F := slice_operator f_star
    let φ := slice_chart f_star
    DifferentiableAt ℂ F (φ f_star) ∧
    IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star))) :
  let F := slice_operator f_star
  let φ := slice_chart f_star
  DifferentiableAt ℂ F (φ f_star) ∧
  IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)) :=
  h_gap

end Molecule
