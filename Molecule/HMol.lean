import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace MLC

open Complex Topology Filter Set

/--
A Horseshoe map (f, U, V) structure.
- U, V: Open subsets of ℂ. V is connected and simply connected (usually a large disk).
- U is relatively compact in V.
- f : U → V is a proper holomorphic map.
- U is typically not connected (e.g., two disjoint disks).
- f is locally injective on U (no critical points in U).
- Dynamics exhibits a horseshoe: intersection of U with f⁻¹(U) contains disjoint components.
-/
structure HorseshoeMap where
  U : Set ℂ
  V : Set ℂ
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_V : IsConnected V
  simplyConnected_V : SimplyConnectedSpace V
  subset : U ⊆ V
  closure_subset : closure U ⊆ V
  differentiable_on : DifferentiableOn ℂ f U
  maps_to : MapsTo f U V
  -- Properness using IsProperMap on the restricted map
  proper : IsProperMap (maps_to.restrict f U V)
  
  /-- Ensures it is a degree-d horseshoe (usually degree 2 for the molecule conjecture) -/
  degree : ∃ d : ℕ, d ≥ 2 ∧ ∀ y ∈ V, {x ∈ U | f x = y}.Finite ∧ Set.ncard {x ∈ U | f x = y} = d

  /-- A Horseshoe must have multiple "legs" or intersections with the original domain. 
      We require at least two disjoint regions that map back into U. -/
  intersections : ∃ (H₁ H₂ : Set ℂ), Disjoint H₁ H₂ ∧ H₁ ⊆ U ∩ f ⁻¹' U ∧ H₂ ⊆ U ∩ f ⁻¹' U
  
  /-- Horseshoe maps are locally injective on U (no critical points in U). -/
  locally_injective : ∀ x ∈ U, deriv f x ≠ 0

/-- HMol is the space of Horseshoe maps. -/
def HMol := HorseshoeMap

/-- The standard horseshoe map example: f(z) = z^2 - 20 on V = D(0, 10). -/
noncomputable def defaultHMol : HMol :=
  let V := Metric.ball 0 10
  let f := fun z => z^2 - 20
  let U := f ⁻¹' V
  { U := U
    V := V
    f := f
    isOpen_U := Metric.isOpen_ball.preimage (continuous_id.pow 2 |>.sub continuous_const)
    isOpen_V := Metric.isOpen_ball
    isConnected_V := (convex_ball (0:ℂ) 10).isConnected <| Metric.nonempty_ball.2 (by norm_num)
    simplyConnected_V := have : ContractibleSpace V := (convex_ball (0:ℂ) 10).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num); inferInstance
    subset := by
      intro z hz
      simp only [U, V, f, Metric.mem_ball, mem_preimage] at *
      have h1 : ‖z^2‖ - 20 ≤ ‖z^2 - 20‖ := by
        have := norm_sub_norm_le (z^2) (20:ℂ)
        rw [sub_le_iff_le_add]
        rw [norm_pow]
        simp at this
        exact this
      have h2 : ‖z^2‖ < 30 := by
        simp [dist_zero_right] at hz
        linarith
      rw [norm_pow] at h2
      have h_abs : ‖z‖ < Real.sqrt 30 := by
        rw [← Real.sqrt_sq (norm_nonneg z)]
        apply Real.sqrt_lt_sqrt (sq_nonneg _)
        exact h2
      simp only [dist_zero_right]
      apply lt_of_lt_of_le h_abs
      rw [Real.sqrt_le_iff] <;> norm_num
    closure_subset := by
      -- closure U ⊆ {z | |z^2 - 20| ≤ 10} ⊆ V
      sorry
    differentiable_on := (differentiable_id.pow 2 |>.sub (differentiable_const _)).differentiableOn
    maps_to := mapsTo_preimage f V
    proper := by
       -- Restriction of proper map (polynomial) to preimage of bounded set is proper?
       -- Yes, f is proper on C. Preimage of compact is compact.
       sorry
    degree := by
       use 2
       constructor
       · norm_num
       · intro y hy
         -- y ∈ V means |y| < 10.
         -- {x ∈ U | f x = y} is {x | x^2 - 20 = y and |x^2-20| < 10}
         -- If x^2 - 20 = y, then |x^2-20| = |y| < 10 is automatically true.
         -- So we just need solutions to x^2 = y + 20.
         -- y + 20 is in B(20, 10), so it is non-zero.
         -- Non-zero number has exactly 2 square roots.
         have h_eq : {x ∈ U | f x = y} = {x | x^2 = y + 20} := by
            ext x
            simp [U, V, f]
            constructor
            · rintro ⟨h_u, h_eq⟩
              rw [← h_eq]
              ring
            · intro h_sq
              constructor
              · rw [← sub_eq_iff_eq_add] at h_sq
                rw [h_sq]
                dsimp [V] at hy
                rw [Metric.mem_ball, dist_zero_right] at hy
                exact hy
              · rw [sub_eq_iff_eq_add]
                exact h_sq
         rw [h_eq]
         have h_nonzero : y + 20 ≠ 0 := by
            intro h
            rw [add_eq_zero_iff_eq_neg] at h
            -- y ∈ B(0, 10), so |y| < 10. |-20| = 20. Contradiction.
            rw [h] at hy
            simp [V, Metric.mem_ball, dist_zero_right] at hy
            linarith
         let p : Polynomial ℂ := Polynomial.X^2 - Polynomial.C (y + 20)
         have hp : p ≠ 0 := Polynomial.monic_X_pow_sub_C (y + 20) (two_ne_zero) |>.ne_zero
         have h_roots : {x | x^2 = y + 20} = (p.roots.toFinset : Set ℂ) := by
            ext x
            rw [Finset.mem_coe, Multiset.mem_toFinset]
            rw [Polynomial.mem_roots hp]
            simp [p]
            rw [sub_eq_zero]
         rw [h_roots]
         constructor
         · exact p.roots.toFinset.finite_toSet
         · rw [Set.ncard_eq_toFinset_card _ p.roots.toFinset.finite_toSet]
           have h_sep : p.Separable := by
              apply Polynomial.separable_X_pow_sub_C (y+20) (by norm_num) h_nonzero
           simp
           rw [Multiset.toFinset_card_of_nodup (sorry : p.roots.Nodup)]
           have h_card : p.roots.card = 2 := sorry
           rw [h_card]




    intersections := by
      -- U has 2 components. Preimage of U has 4.
      -- We can pick 2 disjoint ones.
      sorry
    locally_injective := by
      intro z hz
      simp only [U, V, f, Metric.mem_ball, mem_preimage] at hz
      -- f'(z) = 2z. Zero at 0.
      -- 0 is not in U? |0^2 - 20| = 20 > 10. So 0 ∉ U.
      dsimp [f]
      rw [deriv_sub_const]
      simp
      intro h
      rw [h] at hz
      simp [dist_zero_right] at hz
      norm_num at hz


  }

noncomputable instance : Inhabited HMol := ⟨defaultHMol⟩

instance : TopologicalSpace HMol := ⊥

end MLC
