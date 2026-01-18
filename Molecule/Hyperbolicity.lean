import Molecule.BMol
import Molecule.Rfast
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic

import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace MLC

open Complex Topology Filter Set

/--
A continuous linear operator L : E → E is hyperbolic with a 1D unstable direction if
the space E splits into a 1D unstable subspace Eu and a stable subspace Es,
such that L expands on Eu and contracts on Es.

Reference: Dudko, Lyubich, Selinger, "Pacman renormalization...", arXiv:1703.01206, Section 1 and 7.
-/
def IsHyperbolic1DUnstable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (L : E →L[ℂ] E) : Prop :=
  ∃ (Eu Es : Submodule ℂ E),
    -- The space splits into stable and unstable subspaces
    IsCompl Eu Es ∧
    -- The unstable subspace is 1-dimensional
    Module.finrank ℂ Eu = 1 ∧
    -- The subspaces are invariant under L
    Submodule.map (L : E →ₗ[ℂ] E) Eu = Eu ∧
    Submodule.map (L : E →ₗ[ℂ] E) Es ≤ Es ∧
    -- Expansion on Eu: Eigenvalue with modulus > 1
    (∃ v ∈ Eu, v ≠ 0 ∧ ∃ eig : ℂ, ‖eig‖ > 1 ∧ L v = eig • v) ∧
    -- Contraction on Es: The operator norm restricted to Es is < 1
    (∃ (r : ℝ), r < 1 ∧ ∀ v ∈ Es, ‖L v‖ ≤ r * ‖v‖)

/--
A map f : BMol → BMol is hyperbolic if at its fixed point (or periodic point),
the dynamics can be linearized in a suitable Banach chart, and the linear part is hyperbolic.

Since BMol is not defined as a Banach manifold in this codebase, we formalize the property by
positing the existence of a local chart to a Banach space.
-/
def IsHyperbolic (f : BMol → BMol) : Prop :=
  ∃ (g : BMol) (E : Type) (inst1 : NormedAddCommGroup E) (inst2 : NormedSpace ℂ E),
    let _ := inst1; let _ := inst2
    ∃ (φ : BMol → E) (U : Set BMol),
      g ∈ U ∧
      f g = g ∧ -- Fixed point
      IsFastRenormalizable g ∧ -- The fixed point must be renormalizable
      AnalyticOn ℂ g.f g.U ∧ -- f itself should be analytic in its domain
      -- φ is a "chart" around g
      (∃ (V : Set E), IsOpen V ∧ MapsTo φ U V) ∧
      -- The conjugate map F = φ ∘ f ∘ φ⁻¹ is differentiable at φ(g)
      ∃ (F : E → E),
        (∀ x ∈ U, F (φ x) = φ (f x)) ∧
        DifferentiableAt ℂ F (φ g) ∧
        -- The derivative is hyperbolic with 1D unstable manifold
        IsHyperbolic1DUnstable (fderiv ℂ F (φ g))

end MLC
