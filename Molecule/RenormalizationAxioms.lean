import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast

namespace MLC

open Complex Topology Set

/-- 
Axiom: The Renormalization Operator is Differentiable at Fixed Points.
The operator Rfast, when restricted to appropriate Banach charts around a fixed point, is differentiable.
This encapsulates the analytic dependence of the renormalization on the map.
-/
axiom Rfast_fixed_point_is_differentiable : 
  ∀ f, Rfast f = f → 
  ∃ (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol),
    f ∈ U ∧ 
    (∃ V, IsOpen V ∧ MapsTo φ U V) ∧
    ∃ (F : E → E), 
      (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
      DifferentiableAt ℂ F (φ f)

/--
Axiom: The Derivative of Renormalization is Hyperbolic at Fixed Points.
The linearization of Rfast at a fixed point is a hyperbolic operator with a 1D unstable direction.
This encapsulates the spectral gap theorem for the renormalization fixed point.
-/
axiom Rfast_fixed_point_derivative_is_hyperbolic :
  ∀ f, Rfast f = f →
  ∀ (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol) (F : E → E),
    f ∈ U →
    (∀ x ∈ U, F (φ x) = φ (Rfast x)) →
    DifferentiableAt ℂ F (φ f) →
    IsHyperbolic1DUnstable (fderiv ℂ F (φ f))

end MLC
