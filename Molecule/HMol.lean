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
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Normed.Group.Bounded

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
  let hU_open := Metric.isOpen_ball.preimage (continuous_id.pow 2 |>.sub continuous_const)
  { U := U
    V := V
    f := f
    isOpen_U := hU_open
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
      rw [Real.sqrt_le_iff]; norm_num
    closure_subset := by
      have h_cont : Continuous f := (continuous_id.pow 2).sub continuous_const
      have h_subset : closure U ⊆ f ⁻¹' (closure V) := h_cont.closure_preimage_subset V
      apply h_subset.trans
      intro z hz
      rw [mem_preimage] at hz
      have h_closure_ball : closure V ⊆ Metric.closedBall 0 10 := Metric.closure_ball_subset_closedBall
      have : f z ∈ Metric.closedBall 0 10 := h_closure_ball hz
      rw [Metric.mem_closedBall, dist_zero_right] at this
      have h_triangle : ‖z^2‖ - 20 ≤ ‖z^2 - 20‖ := by
          have := norm_sub_norm_le (z^2) (20:ℂ)
          rw [sub_le_iff_le_add]
          rw [norm_pow]
          simp at this
          exact this
      have h_bound : ‖z‖^2 ≤ 30 := by
          rw [norm_pow] at h_triangle
          linarith
      rw [Metric.mem_ball, dist_zero_right]
      have h_bound_sqrt : Real.sqrt (‖z‖^2) ≤ Real.sqrt 30 := Real.sqrt_le_sqrt h_bound
      rw [Real.sqrt_sq (norm_nonneg z)] at h_bound_sqrt
      apply lt_of_le_of_lt h_bound_sqrt
      rw [Real.sqrt_lt]
      norm_num
      norm_num
      norm_num
    differentiable_on := (differentiable_id.pow 2 |>.sub (differentiable_const _)).differentiableOn
    maps_to := mapsTo_preimage f V
    proper := by
       have h_proper_C : IsProperMap f := by
          rw [isProperMap_iff_tendsto_cocompact]
          constructor
          · exact (continuous_id.pow 2).sub continuous_const
          · apply Filter.tendsto_cocompact_cocompact_of_norm
            intro R
            let p : Polynomial ℂ := Polynomial.X^2 - Polynomial.C 20
            have h_eq : ∀ z, f z = p.eval z := by simp [f, p]
            have h_tendsto : Tendsto (fun z => ‖p.eval z‖) (cocompact ℂ) atTop := by
                apply Polynomial.tendsto_norm_atTop p
                · rw [Polynomial.degree_X_pow_sub_C]
                  norm_num
                  norm_num
                · exact tendsto_norm_cocompact_atTop
            simp_rw [← h_eq] at h_tendsto
            rw [Filter.tendsto_atTop] at h_tendsto
            specialize h_tendsto (R + 1)
            rw [Filter.eventually_iff] at h_tendsto
            rw [Filter.hasBasis_cocompact.mem_iff] at h_tendsto
            rcases h_tendsto with ⟨K, hK_compact, hK_sub⟩
            rcases hK_compact.isBounded.subset_ball 0 with ⟨r, hr_sub⟩
            use r
            intro x hx
            have h_not_in_K : x ∉ K := fun h => (not_le.2 (by simpa using Metric.mem_ball.1 (hr_sub h))) hx.le
            have := hK_sub h_not_in_K
            have h_ineq : R + 1 ≤ ‖f x‖ := this
            linarith
       rw [isProperMap_iff_isCompact_preimage]
       constructor
       · exact h_proper_C.continuous.restrict _
       intro K hK
       have hK_compact_C : IsCompact (K : Set ℂ) := hK.image continuous_subtype_val
       have h_pre : IsCompact (f ⁻¹' K) := h_proper_C.isCompact_preimage hK_compact_C
       have h_eq : (Subtype.val '' (MapsTo.restrict f U V (mapsTo_preimage f V) ⁻¹' K)) = f ⁻¹' (Subtype.val '' K) := by
          ext x
          simp only [mem_image, mem_preimage]
          constructor
          · rintro ⟨y, hy, rfl⟩
            simp [MapsTo.restrict] at hy
            exact ⟨MapsTo.restrict f U V (mapsTo_preimage f V) y, hy, rfl⟩
          · intro h
            have h_sub : Subtype.val '' K ⊆ V := fun z hz => Exists.elim hz (fun k hk => hk.2 ▸ k.property)
            have h_in_V : f x ∈ V := h_sub h
            refine Exists.intro (Subtype.mk x h_in_V) ⟨?_, rfl⟩
            simp [MapsTo.restrict]
            rcases h with ⟨k, hk, hk_eq⟩
            convert hk
            apply Subtype.ext
            exact hk_eq.symm
       rw [IsEmbedding.subtypeVal.isCompact_iff]
       rw [h_eq]
       exact h_pre
    degree := by
       use 2
       constructor
       · norm_num
       · intro y hy
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
           rw [Multiset.toFinset_card_of_nodup]
           · rw [IsAlgClosed.card_roots_eq_natDegree]
             simp only [p]
             rw [Polynomial.natDegree_X_pow_sub_C]
           · exact Polynomial.nodup_roots h_sep

    intersections := by
       let z1 : ℂ := 5
       let z2 : ℂ := -4
       have h1 : f z1 = z1 := by dsimp [f, z1]; norm_num
       have h2 : f z2 = z2 := by dsimp [f, z2]; norm_num
       have hz1 : z1 ∈ V := by simp [V, Metric.mem_ball, z1]; norm_num
       have hz2 : z2 ∈ V := by simp [V, Metric.mem_ball, z2]; norm_num
       have hz1_U : z1 ∈ U := by simp [U, mem_preimage]; rw [h1]; exact hz1
       have hz2_U : z2 ∈ U := by simp [U, mem_preimage]; rw [h2]; exact hz2

       let S := U ∩ f ⁻¹' U
       have hS_open' : IsOpen S := IsOpen.inter hU_open (hU_open.preimage (continuous_id.pow 2 |>.sub continuous_const))

       have hz1_S : z1 ∈ S := ⟨hz1_U, by simp [mem_preimage]; rw [h1]; exact hz1_U⟩
       have hz2_S : z2 ∈ S := ⟨hz2_U, by simp [mem_preimage]; rw [h2]; exact hz2_U⟩

       obtain ⟨r1, hr1_pos, hr1_sub⟩ := Metric.isOpen_iff.1 hS_open' z1 hz1_S
       obtain ⟨r2, hr2_pos, hr2_sub⟩ := Metric.isOpen_iff.1 hS_open' z2 hz2_S

       let ε := min (1:ℝ) (min r1 r2)
       have he_pos : 0 < ε := lt_min (by norm_num) (lt_min hr1_pos hr2_pos)

       use Metric.ball z1 ε, Metric.ball z2 ε
       constructor
       · rw [Set.disjoint_left]
         intro z hz1 hz2
         rw [Metric.mem_ball] at hz1 hz2
         have h : dist z1 z2 ≤ dist z1 z + dist z z2 := dist_triangle _ _ _
         rw [dist_comm z z2] at h
         rw [dist_comm z z1] at hz1
         rw [dist_comm z z2] at hz2
         have h_lt : dist z1 z2 < ε + ε := lt_of_le_of_lt h (add_lt_add hz1 hz2)
         have h_dist : dist z1 z2 = 9 := by dsimp [z1, z2]; rw [dist_eq_norm]; norm_num
         rw [h_dist] at h_lt
         have h_eps : ε + ε ≤ 2 := by
           have : ε ≤ 1 := min_le_left _ _
           linarith
         linarith
       · constructor
         · apply Subset.trans _ hr1_sub
           apply Metric.ball_subset_ball
           apply le_trans (min_le_right _ _) (min_le_left _ _)
         · apply Subset.trans _ hr2_sub
           apply Metric.ball_subset_ball
           apply le_trans (min_le_right _ _) (min_le_right _ _)
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
