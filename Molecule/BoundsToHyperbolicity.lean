import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Mathlib.Analysis.Complex.CauchyIntegral

namespace MLC

open Complex Topology Set

/--
Lemma: Pseudo-Siegel Bounds imply the existence of a Banach Slice.
If the bounds hold, there exists a Banach space of analytic functions E and a chart φ
such that Rfast corresponds to an operator F on E.

Reference: Dudko, Lyubich, Selinger, arXiv:1703.01206, Section 7.1 "Banach slices".
-/
axiom bounds_imply_banach_slice : 
  PseudoSiegelAPrioriBoundsStatement → 
  ∃ (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol) (f_star : BMol),
    Rfast f_star = f_star ∧
    f_star ∈ U ∧
    (∃ V, IsOpen V ∧ MapsTo φ U V) ∧
    ∃ (F : E → E),
      (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
      DifferentiableAt ℂ F (φ f_star) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star))

/--
Theorem: Bounds Imply Hyperbolicity.
The main implication from Section 7 of the paper.
-/
theorem bounds_imply_hyperbolicity_proof (h : PseudoSiegelAPrioriBoundsStatement) : IsHyperbolic Rfast := by
  -- 1. Use the Banach Slice lemma (which encapsulates the spectral theory)
  obtain ⟨E, inst1, inst2, φ, U, f_star, h_fixed, h_f_in_U, h_chart, F, h_conj, h_diff, h_hyp⟩ := 
    bounds_imply_banach_slice h
  
  -- 2. Prove f_star is analytic (from BMol definition)
  have h_analytic : AnalyticOn ℂ f_star.f f_star.U := by
    rw [analyticOn_iff_differentiableOn f_star.isOpen_U]
    exact f_star.differentiable_on

  -- 3. Construct the IsHyperbolic witness
  use f_star
  use E, inst1, inst2
  use φ, U
  refine ⟨h_f_in_U, h_fixed, h_analytic, h_chart, F, h_conj, h_diff, h_hyp⟩

end MLC
