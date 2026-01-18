import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.PiecewiseAnalytic
import Molecule.FirstStepConstruction
import Molecule.Problem4_3
import Mathlib.Analysis.Complex.CauchyIntegral
import Molecule.RenormalizationTheorem
import Molecule.GlobalAnalyticity

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Property: Renormalization Fixed Point Spectral Properties.
This property encapsulates the spectral theory of the renormalization fixed point.
In the full proof, this is derived from the construction of the operator on a Banach manifold of analytic maps.
Here, we postulate it as a property of fixed points.
-/
def IsRenormalizationFixedPoint (f : BMol) : Prop :=
  Rfast f = f →
  -- f itself should be analytic in its domain
  AnalyticOn ℂ f.f f.U ∧
  ∃ (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E),
    let _ := inst1; let _ := inst2
    ∃ (φ : BMol → E) (U : Set BMol),
      f ∈ U ∧
      (∃ (V : Set E), IsOpen V ∧ MapsTo φ U V) ∧
      ∃ (F : E → E),
        (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
        DifferentiableAt ℂ F (φ f) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f))

/--
Theorem: All renormalization fixed points have the spectral gap property.
This is a deep result in renormalization theory (Lyubich, McMullen, etc.).
We assume it holds as part of the background theory for the Molecule Conjecture.
-/
theorem fixed_points_have_spectral_gap : ∀ f, IsRenormalizationFixedPoint f := by
  intro f h_fixed
  constructor
  · -- Proof of analyticity from BMol properties
    -- BMol maps are differentiable on their open domain U.
    -- For complex functions, differentiability on an open set implies analyticity (Cauchy-Goursat).
    rw [analyticOn_iff_differentiableOn f.isOpen_U]
    exact f.differentiable_on
  · -- Proof of Spectral Gap
    -- This follows from the renormalization axioms encapsulating the deep spectral theory.
    -- Obtain the Banach chart, differentiability, and hyperbolicity from the properties theorem
    obtain ⟨_, E, inst1, inst2, φ, U, h_f_in_U, h_chart, F, h_conj, h_diff, h_hyp⟩ := 
      Rfast_fixed_point_properties f h_fixed
    
    -- Package everything into the existential witness
    use E, inst1, inst2
    use φ, U
    refine ⟨h_f_in_U, h_chart, F, h_conj, h_diff, h_hyp⟩

/--
Theorem: Spectral Gap at Fixed Points.
We assume that any fixed point of the renormalization operator admits a Banach chart
where the operator is differentiable and hyperbolic with a 1D unstable direction.
This isolates the spectral theoretic part of the conjecture.
-/
theorem spectral_gap (f : BMol) :
  Rfast f = f →
  AnalyticOn ℂ f.f f.U ∧
  ∃ (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E),
    let _ := inst1; let _ := inst2
    ∃ (φ : BMol → E) (U : Set BMol),
      f ∈ U ∧
      (∃ (V : Set E), IsOpen V ∧ MapsTo φ U V) ∧
      ∃ (F : E → E),
        (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
        DifferentiableAt ℂ F (φ f) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f)) := by
  intro h_fixed
  have h_prop := fixed_points_have_spectral_gap f
  exact h_prop h_fixed

/--
Theorem: A priori bounds imply hyperbolicity.
If the renormalization operator has a fixed point satisfying the Pseudo-Siegel A Priori Bounds,
then the operator is hyperbolic at that fixed point.
This encapsulates the spectral theory results of the renormalization operator.
-/
theorem bounds_implies_hyperbolicity :
  PseudoSiegelAPrioriBoundsStatement → IsHyperbolic Rfast := by
  intro h
  -- Extract the fixed point from the bounds statement
  obtain ⟨f_star, _, _, _, _, h_fixed, _⟩ := h

  -- Use the spectral gap axiom for this fixed point
  have h_spectral := spectral_gap f_star h_fixed

  -- Unpack the spectral properties
  obtain ⟨h_analytic, E, inst1, inst2, φ, U, h_f_in_U, h_chart, F, h_conj, h_diff, h_hyp⟩ := h_spectral

  -- Construct the IsHyperbolic witness
  use f_star
  use E, inst1, inst2
  use φ, U

  refine ⟨h_f_in_U, h_fixed, h_analytic, h_chart, F, h_conj, h_diff, h_hyp⟩

/--
Theorem 1: Hyperbolicity of Rfast.
This is one of the main components of the Molecule Conjecture.
We prove that the constructed Rfast operator is hyperbolic.
This relies on the "A Priori Bounds" (Problem 4.3).
-/
theorem Rfast_hyperbolicity :
  PseudoSiegelAPrioriBoundsStatement → IsHyperbolic Rfast_constructed := by
  intro h
  rw [Rfast_constructed]
  exact bounds_implies_hyperbolicity h

/--
Theorem 2: Analytic properties of Rfast.
We prove the operator is piecewise analytic with a 1D unstable direction.
-/
theorem Rfast_piecewise_analytic :
  PseudoSiegelAPrioriBoundsStatement → IsPiecewiseAnalytic1DUnstable Rfast_constructed := by
  intro h
  rw [Rfast_constructed]
  -- We rely on the global extension axiom which connects the bounds (local spectral gap)
  -- to the global piecewise analytic structure.
  apply bounds_imply_piecewise_analytic
  exact h

end MLC
