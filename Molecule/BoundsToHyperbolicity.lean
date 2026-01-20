import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Molecule.BanachSlice
import Mathlib.Analysis.Complex.CauchyIntegral

namespace MLC

open Complex Topology Set

/--
Lemma: Pseudo-Siegel Bounds imply the existence of a Banach Slice.
If the bounds hold, there exists a Banach space of analytic functions E and a chart φ
such that Rfast corresponds to an operator F on E.

Reference: Dudko, Lyubich, Selinger, arXiv:1703.01206, Section 7.1 "Banach slices".
-/
theorem bounds_imply_banach_slice :
  PseudoSiegelAPrioriBoundsStatement →
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol) (f_star : BMol),
    Rfast f_star = f_star ∧
    IsFastRenormalizable f_star ∧
    f_star ∈ U ∧
    (∃ V, IsOpen V ∧ MapsTo φ U V) ∧
    ∃ (F : E → E),
      (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
      DifferentiableAt ℂ F (φ f_star) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)) := by
  intro h
  obtain ⟨f_star, U, h_fixed, h_renorm, h_U_open, h_f_in_U, h_c1_in_D, h_bounds_body⟩ := h
  let D : Set ℂ := Metric.ball 0 0.1
  let h_D_open : IsOpen D := Metric.isOpen_ball

  -- Use the components from the BanachSlice module
  let E := SliceSpace
  let φ := slice_chart f_star
  let U_slice := slice_domain f_star
  let F := slice_operator f_star

  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1

  have h_siegel : HasSiegelBounds f_star D U a b := by
    refine ⟨h_fixed, h_D_open, h_U_open, h_f_in_U, h_c1_in_D, ?_⟩
    dsimp [a, b]
    exact h_bounds_body

  use E, (inferInstance : NormedAddCommGroup E), (inferInstance : NormedSpace ℂ E)
  use φ, U_slice, f_star

  -- 1. Rfast f_star = f_star
  have h_fixed := h_siegel.1
  constructor
  · exact h_fixed
  
  -- 2. IsFastRenormalizable f_star
  constructor
  · exact h_renorm

  -- 3. f_star ∈ U_slice
  constructor
  · change f_star ∈ univ
    exact mem_univ f_star

  -- 3. Chart maps to open set
  constructor
  · apply slice_chart_open

  -- 4. Existence of F with properties
  use F
  constructor
  · -- Conjugacy: ∀ x ∈ U, F (φ x) = φ (Rfast x)
    intro x hx
    apply slice_conjugacy
    exact hx

  -- 5. Differentiability and Hyperbolicity (from Spectral Gap Axiom)
  have h_spectral := slice_spectral_gap h_siegel
  constructor
  · exact h_spectral.1
  · exact h_spectral.2

/--
Theorem: Bounds Imply Hyperbolicity.
The main implication from Section 7 of the paper.
-/
theorem bounds_imply_hyperbolicity_proof (h : PseudoSiegelAPrioriBoundsStatement) : IsHyperbolic Rfast := by
  -- 1. Use the Banach Slice lemma (which encapsulates the spectral theory)
  obtain ⟨E, inst1, inst2, φ, U, f_star, h_fixed, h_renorm, h_f_in_U, h_chart, F, h_conj, h_diff, h_hyp⟩ :=
    bounds_imply_banach_slice h

  -- 2. Prove f_star is analytic (from BMol definition)
  have h_analytic : AnalyticOn ℂ f_star.f f_star.U := by
    rw [analyticOn_iff_differentiableOn f_star.isOpen_U]
    exact f_star.differentiable_on

  -- 3. Construct the IsHyperbolic witness
  use f_star
  use E, inst1, inst2
  use φ, U
  refine ⟨h_f_in_U, h_fixed, h_renorm, h_analytic, h_chart, F, h_conj, h_diff, h_hyp⟩

end MLC
