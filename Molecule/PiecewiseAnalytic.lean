import Molecule.BMol
import Molecule.Hyperbolicity
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Countable

namespace MLC

open Complex Topology Filter Set

/--
A map `f` is analytic on a set `U` in `BMol` if there exists a chart to a Banach space
conjugating `f` to an analytic map.
-/
structure AnalyticChart (f : BMol → BMol) (U : Set BMol) : Type 1 where
  E : Type
  inst1 : NormedAddCommGroup E
  inst2 : NormedSpace ℂ E
  φ : BMol → E
  V : Set E
  hV_open : IsOpen V
  h_chart : MapsTo φ U V
  F : E → E
  h_conj : ∀ x ∈ U, F (φ x) = φ (f x)
  h_analytic : AnalyticOn ℂ F V

instance : TopologicalSpace BMol := ⊥ -- Trivial topology for now, as we don't have a natural one yet.

/--
Piecewise Analyticity: The domain can be covered by a countable collection of open sets
on which the map is analytic.
-/
def IsPiecewiseAnalytic (f : BMol → BMol) : Prop :=
  ∃ (Us : Set (Set BMol)),
    Us.Countable ∧
    (∀ U ∈ Us, IsOpen U) ∧
    (⋃₀ Us = univ) ∧
    ∀ U ∈ Us, Nonempty (AnalyticChart f U)

/--
1D Unstable Direction: At every point in the domain (where analytic),
the derivative has a 1D unstable splitting.
This generalizes the fixed-point hyperbolicity to the entire domain.
-/
def Has1DUnstableDirection (f : BMol → BMol) : Prop :=
  ∀ (U : Set BMol) (h : AnalyticChart f U) (x : BMol),
    x ∈ U →
    let _ := h.inst1; let _ := h.inst2
    -- The derivative of the conjugate map F at φ(x)
    let L := fderiv ℂ h.F (h.φ x)
    -- Must have a 1D unstable splitting
    IsHyperbolic1DUnstable L

/--
Combined predicate for Piecewise Analyticity with 1D Unstable Direction.
Reference: Dudko, Lyubich, Selinger, "Pacman renormalization...", arXiv:1703.01206.
-/
def IsPiecewiseAnalytic1DUnstable (f : BMol → BMol) : Prop :=
  IsPiecewiseAnalytic f ∧ Has1DUnstableDirection f

end MLC
