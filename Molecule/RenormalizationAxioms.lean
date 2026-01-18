import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Molecule.BoundsToHyperbolicity

namespace MLC

open Complex Topology Set

/--
Axiom: Uniqueness of the Renormalization Fixed Point.
There is only one fixed point for the Pacman Renormalization operator with a given combinatorics.

Reference: Dudko, Lyubich, Selinger, arXiv:1703.01206, Theorem 1.1.
-/
axiom fixed_point_uniqueness_axiom :
  ∃! f, Rfast f = f

/--
Theorem: Pacman Renormalization Theorem (Hyperbolicity and Uniqueness).
There exists a unique fixed point of the renormalization operator, and the operator is hyperbolic at this fixed point.

Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization...", arXiv:1703.01206, Theorem 1.1.
-/
theorem Rfast_theorem_1_1 : 
  (IsHyperbolic Rfast) ∧ (∃! f, Rfast f = f) := by
  -- We prove this by combining the A Priori Bounds result with the Uniqueness result.
  -- 1. Establishing Hyperbolicity from Bounds
  have h_hyp : IsHyperbolic Rfast := by
    apply bounds_imply_hyperbolicity_proof
    -- We rely on Problem 4.3 which establishes the bounds
    exact problem_4_3_bounds_established

  -- 2. Establishing Uniqueness
  have h_unique : ∃! f, Rfast f = f := fixed_point_uniqueness_axiom

  exact ⟨h_hyp, h_unique⟩

/-- 
Theorem: Properties of the Renormalization Fixed Point.
Every fixed point of Rfast is analytic and admits a Banach chart where the operator is differentiable and hyperbolic.
This derives directly from the Pacman Renormalization Theorem (Theorem 1.1).

Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization...", arXiv:1703.01206, Theorem 1.1.
-/
theorem Rfast_fixed_point_properties : 
  ∀ f, Rfast f = f → 
  AnalyticOn ℂ f.f f.U ∧
  ∃ (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol),
    f ∈ U ∧ 
    (∃ V, IsOpen V ∧ MapsTo φ U V) ∧
    ∃ (F : E → E), 
      (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
      DifferentiableAt ℂ F (φ f) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f)) := by
  intro f h_fixed
  obtain ⟨h_hyp, h_unique⟩ := Rfast_theorem_1_1
  
  -- Unpack IsHyperbolic Witness
  obtain ⟨g, E, inst1, inst2, φ, U, h_g_in_U, h_g_fixed, h_g_analytic, h_chart, F, h_conj, h_diff, h_hyp_lin⟩ := h_hyp
  
  -- Use uniqueness to identify f with g
  have h_eq : f = g := by
    apply h_unique.unique h_fixed h_g_fixed
  
  subst h_eq
  
  -- Return the properties of g (which is f)
  refine ⟨h_g_analytic, E, inst1, inst2, φ, U, h_g_in_U, h_chart, F, h_conj, h_diff, h_hyp_lin⟩


end MLC
