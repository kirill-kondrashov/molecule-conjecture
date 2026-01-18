import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
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

namespace MLC

open Complex Topology Filter Set

/--
A Quadratic-like map (f, U, V) consists of:
- U, V: Open, connected, simply connected subsets of ℂ
- U is relatively compact in V (closure U ⊆ V)
- f : U → V is a proper holomorphic map of degree 2

Here we formalize the structure BMol as the space of such maps.
-/
structure QuadraticLikeMap where
  U : Set ℂ
  V : Set ℂ
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_U : IsConnected U
  isConnected_V : IsConnected V
  simplyConnected_U : SimplyConnectedSpace U
  simplyConnected_V : SimplyConnectedSpace V
  subset : U ⊆ V
  closure_subset : closure U ⊆ V
  differentiable_on : DifferentiableOn ℂ f U
  maps_to : MapsTo f U V
  -- Properness using IsProperMap on the restricted map
  proper : IsProperMap (maps_to.restrict f U V)
  -- Degree 2 condition: unique critical point in U
  unique_critical_point : ∃! c ∈ U, deriv f c = 0

/-- The unique critical point of a Quadratic-like map. -/
noncomputable def criticalPoint (g : QuadraticLikeMap) : ℂ :=
  Classical.choose g.unique_critical_point

/-- The critical value c1 = f(c0). -/
noncomputable def criticalValue (g : QuadraticLikeMap) : ℂ :=
  g.f (criticalPoint g)

/-- 
A fixed point of the map.
For a quadratic-like map, there are typically two. This definition selects one arbitrarily
(in practice, the α-fixed point is intended).
-/
noncomputable def QuadraticLikeMap.fixed_point (g : QuadraticLikeMap) : ℂ :=
  Classical.epsilon (fun z => z ∈ g.U ∧ g.f z = z)

/-- BMol is the space of Quadratic-like maps. -/
def BMol := QuadraticLikeMap

/-- 
We define a trivial topology on BMol (discrete) for now to satisfy type class requirements
in abstract statements. In a full formalization, this would be the compact-open topology 
on the space of holomorphic maps.
-/
instance : TopologicalSpace BMol :=
  { IsOpen := fun _ => True,
    isOpen_univ := True.intro,
    isOpen_inter := fun _ _ _ _ => True.intro,
    isOpen_sUnion := fun _ _ => True.intro }

/-- The standard quadratic map f(z) = z^2 on disks D(0,2) -> D(0,4). -/
noncomputable def defaultBMol : BMol :=
  let U := Metric.ball 0 2
  let V := Metric.ball 0 4
  let f := fun z => z^2
  { U := U
    V := V
    f := f
    isOpen_U := Metric.isOpen_ball
    isOpen_V := Metric.isOpen_ball
    isConnected_U := (convex_ball (0:ℂ) 2).isConnected <| Metric.nonempty_ball.2 (by norm_num)
    isConnected_V := (convex_ball (0:ℂ) 4).isConnected <| Metric.nonempty_ball.2 (by norm_num)
    simplyConnected_U := have : ContractibleSpace U := (convex_ball (0:ℂ) 2).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num); inferInstance
    simplyConnected_V := have : ContractibleSpace V := (convex_ball (0:ℂ) 4).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num); inferInstance
    subset := Metric.ball_subset_ball (by norm_num)
    closure_subset := by
      rw [closure_ball (0:ℂ) (by norm_num : (2:ℝ) ≠ 0)]
      apply Metric.closedBall_subset_ball
      norm_num
    differentiable_on := differentiableOn_id.pow 2
    maps_to := by
      dsimp [U, V, f]
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at *
      norm_cast
      rw [norm_pow]
      rw [show (4:ℝ) = 2^2 by norm_num]
      rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)]
      exact hz
    proper := by
      rw [isProperMap_iff_isCompact_preimage]
      constructor
      · exact (continuous_pow 2).continuousOn.mapsToRestrict _
      · intro K hK
        let K' : Set ℂ := Subtype.val '' K
        have hK'_compact : IsCompact K' := hK.image continuous_subtype_val
        have hK'_sub_V : K' ⊆ V := Subtype.coe_image_subset V K
        
        let S := f ⁻¹' K'
        have hS_compact : IsCompact S := by
           have : IsProperMap f := by
              rw [isProperMap_iff_isCompact_preimage]
              constructor
              · exact continuous_pow 2
              · intro L hL
                exact Metric.isCompact_of_isClosed_isBounded (hL.isClosed.preimage (continuous_pow 2)) (by
                  obtain ⟨R, hR⟩ := hL.isBounded.subset_ball (0:ℂ)
                  rw [isBounded_iff_forall_norm_le]
                  use Real.sqrt R
                  intro z hz
                  have : ‖z^2‖ < R := by
                    apply mem_ball_zero_iff.mp
                    apply hR
                    exact hz
                  rw [norm_pow] at this
                  apply le_of_lt
                  -- z^2 < R implies |z| < sqrt R
                  have hRpos : 0 ≤ R := by
                    apply le_trans (sq_nonneg ‖z‖) this.le
                  rw [← Real.sqrt_sq (norm_nonneg z)]
                  rw [Real.sqrt_lt_sqrt_iff (sq_nonneg _)]
                  exact this)

           exact this.isCompact_preimage hK'_compact

        have hS_sub_U : S ⊆ U := by
          intro z hz
          have : f z ∈ K' := hz
          have : f z ∈ V := hK'_sub_V this
          simp [V, Metric.mem_ball, dist_zero_right] at this
          rw [norm_pow] at this
          rw [show (4:ℝ) = 2^2 by norm_num] at this
          rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)] at this
          simp [U, Metric.mem_ball, dist_zero_right, this]

        have : (MapsTo.restrict f U V (by
          dsimp [U, V, f]
          intro z hz
          simp only [Metric.mem_ball, dist_zero_right] at *
          norm_cast
          rw [norm_pow]
          rw [show (4:ℝ) = 2^2 by norm_num]
          rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)]
          exact hz
        )) ⁻¹' K = {x : U | f x ∈ K'} := by
            ext x
            simp only [mem_preimage, mem_setOf_eq]
            dsimp [K']
            constructor
            · intro h
              exact ⟨_, h, rfl⟩
            · rintro ⟨y, hy, eq⟩
              convert hy
              ext
              exact eq.symm
        rw [this]
        -- IsCompact {x:U | f x ∈ K'} iff IsCompact S
        -- S = Subtype.val '' {x:U | f x ∈ K'}
        -- Use Subtype.isCompact_iff
        rw [Subtype.isCompact_iff]
        have : Subtype.val '' {x : U | f x ∈ K'} = S := by
          ext z
          simp only [S, mem_preimage]
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx
          · intro hz
            exact ⟨⟨z, hS_sub_U hz⟩, hz, rfl⟩
        rw [this]
        exact hS_compact

    unique_critical_point := by
      use 0
      dsimp [U, V, f]
      constructor
      · simp [Metric.mem_ball]
      · intro y hy
        simp [Metric.mem_ball] at hy
        exact hy.2
  }

noncomputable instance : Inhabited BMol := ⟨defaultBMol⟩

end MLC
