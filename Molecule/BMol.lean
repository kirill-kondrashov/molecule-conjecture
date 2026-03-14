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

namespace Molecule

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
  -- Simple critical point (non-degenerate)
  simple_critical_point : ∀ c ∈ U, deriv f c = 0 → deriv (deriv f) c ≠ 0

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

instance : DiscreteTopology BMol := ⟨rfl⟩

/--
A first non-placeholder observation on `BMol`: evaluate the underlying map at
`0`. This is intentionally coarse, but it already supports a non-discrete
topology candidate.
-/
def bmol_zero_observation (g : BMol) : ℂ := g.f 0

/--
Finite source-domain tag used by the first topology migration step: record
whether the fixed probe point `5 / 2` lies in the source domain.
-/
noncomputable def bmol_large_source_tag_observation (g : BMol) : ℂ := by
  classical
  exact if ((5 : ℂ) / 2) ∈ g.U then 1 else 0

/--
Two-coordinate finite observation for the first topology-compatible scaffold
search: one analytic value and one coarse domain tag.
-/
noncomputable def bmol_finite_observation (g : BMol) : ℂ × ℂ :=
  (bmol_zero_observation g, bmol_large_source_tag_observation g)

/--
A first non-discrete topology candidate on `BMol`, induced by the zero-value
observation of the underlying map. The default instance remains discrete for
compatibility, while this named topology provides a concrete upgrade target.
-/
def bmol_zero_topology : TopologicalSpace BMol :=
  TopologicalSpace.induced bmol_zero_observation inferInstance

/--
The zero-value observation is continuous by construction in the induced
topology.
-/
theorem continuous_bmol_zero_observation :
    @Continuous BMol ℂ bmol_zero_topology inferInstance bmol_zero_observation :=
  continuous_induced_dom

/--
Finite-observation topology candidate for the first topology-compatible chart
migration.
-/
def bmol_finite_topology : TopologicalSpace BMol :=
  TopologicalSpace.induced bmol_finite_observation inferInstance

/--
The finite observation is continuous by construction in its induced topology.
-/
theorem continuous_bmol_finite_observation :
    @Continuous BMol (ℂ × ℂ) bmol_finite_topology inferInstance
      bmol_finite_observation :=
  continuous_induced_dom

/--
Under the finite-observation topology, the zero-value observation is continuous
as the first coordinate projection.
-/
theorem continuous_bmol_zero_observation_of_bmol_finite_topology :
    @Continuous BMol ℂ bmol_finite_topology inferInstance bmol_zero_observation := by
  let _ : TopologicalSpace BMol := bmol_finite_topology
  simpa [bmol_finite_observation] using
    (continuous_fst.comp continuous_bmol_finite_observation)

/--
Under the finite-observation topology, the source-domain tag is continuous as
the second coordinate projection.
-/
theorem continuous_bmol_large_source_tag_observation_of_bmol_finite_topology :
    @Continuous BMol ℂ bmol_finite_topology inferInstance
      bmol_large_source_tag_observation := by
  let _ : TopologicalSpace BMol := bmol_finite_topology
  simpa [bmol_finite_observation] using
    (continuous_snd.comp continuous_bmol_finite_observation)

/-- Global properness of the quadratic map on `ℂ`. -/
lemma isProperMap_quad : IsProperMap (fun z : ℂ => z ^ 2) := by
  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · exact continuous_pow 2
  · intro L hL
    exact
      Metric.isCompact_of_isClosed_isBounded
        (hL.isClosed.preimage (continuous_pow 2))
        (by
          obtain ⟨R, hR⟩ := hL.isBounded.subset_ball (0 : ℂ)
          rw [isBounded_iff_forall_norm_le]
          use Real.sqrt R
          intro z hz
          have hzR : ‖z ^ 2‖ < R := by
            apply mem_ball_zero_iff.mp
            exact hR hz
          rw [norm_pow] at hzR
          apply le_of_lt
          rw [← Real.sqrt_sq (norm_nonneg z)]
          rw [Real.sqrt_lt_sqrt_iff (sq_nonneg ‖z‖)]
          exact hzR)

/--
Translating the quadratic map by a constant preserves properness on `ℂ`.
-/
lemma isProperMap_quad_add_const (c : ℂ) :
    IsProperMap (fun z : ℂ => z ^ 2 + c) := by
  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · exact (continuous_pow 2).add continuous_const
  · intro L hL
    let L' : Set ℂ := (fun w : ℂ => w - c) '' L
    have hL'_compact : IsCompact L' :=
      hL.image (continuous_id.sub continuous_const)
    have h_preimage :
        (fun z : ℂ => z ^ 2 + c) ⁻¹' L = (fun z : ℂ => z ^ 2) ⁻¹' L' := by
      ext z
      constructor
      · intro hz
        exact ⟨z ^ 2 + c, hz, by simp⟩
      · rintro ⟨w, hw, h_eq⟩
        have h_eq' : w - c = z ^ 2 := by
          simpa using h_eq
        have hw_eq : w = z ^ 2 + c := by
          calc
            w = (w - c) + c := by symm; exact sub_add_cancel w c
            _ = z ^ 2 + c := by rw [h_eq']
        show z ^ 2 + c ∈ L
        rw [← hw_eq]
        exact hw
    rw [h_preimage]
    exact isProperMap_quad.isCompact_preimage hL'_compact

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
    simple_critical_point := by
      intro c hc h_deriv
      dsimp [f] at *
      have h1 : deriv (fun z ↦ z ^ 2) c = 2 * c := by
        rw [deriv_pow_field 2]; simp
      rw [h1] at h_deriv
      
      have h_deriv_fun : deriv (fun (z:ℂ) ↦ z^2) = (fun z ↦ 2*z) := by
        ext z
        rw [deriv_pow_field 2]; simp
      
      rw [h_deriv_fun]
      rw [deriv_const_mul]
      · rw [deriv_id'']
        norm_num
      · exact differentiableAt_id
  }

/--
A first explicit non-`z^2` quadratic-like map for the redesigned search.
This keeps the same source disk as `defaultBMol`, but shifts the polynomial to
`z ↦ z^2 + 1` and recenters the target disk at `1`.
-/
noncomputable def shiftedBMol : BMol :=
  let U := Metric.ball 0 2
  let V := Metric.ball 1 4
  let f := fun z => z^2 + 1
  { U := U
    V := V
    f := f
    isOpen_U := Metric.isOpen_ball
    isOpen_V := Metric.isOpen_ball
    isConnected_U := (convex_ball (0 : ℂ) 2).isConnected <|
      Metric.nonempty_ball.2 (by norm_num)
    isConnected_V := (convex_ball (1 : ℂ) 4).isConnected <|
      Metric.nonempty_ball.2 (by norm_num)
    simplyConnected_U := by
      have : ContractibleSpace U :=
        (convex_ball (0 : ℂ) 2).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num)
      infer_instance
    simplyConnected_V := by
      have : ContractibleSpace V :=
        (convex_ball (1 : ℂ) 4).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num)
      infer_instance
    subset := by
      intro z hz
      simp only [U, Metric.mem_ball, dist_zero_right] at hz
      simp only [V, Metric.mem_ball, dist_eq_norm]
      calc
        ‖z - 1‖ ≤ ‖z‖ + ‖(-1 : ℂ)‖ := by
          simpa [sub_eq_add_neg] using (norm_add_le z (-1 : ℂ))
        _ < 2 + 1 := by
          have := add_lt_add_right hz ‖(-1 : ℂ)‖
          simpa using this
        _ < 4 := by norm_num
    closure_subset := by
      rw [closure_ball (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0)]
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hz
      simp only [V, Metric.mem_ball, dist_eq_norm]
      calc
        ‖z - 1‖ ≤ ‖z‖ + ‖(-1 : ℂ)‖ := by
          simpa [sub_eq_add_neg] using (norm_add_le z (-1 : ℂ))
        _ ≤ 2 + 1 := by
          have := add_le_add_right hz ‖(-1 : ℂ)‖
          simpa using this
        _ < 4 := by norm_num
    differentiable_on := (differentiableOn_id.pow 2).add (differentiableOn_const (1 : ℂ))
    maps_to := by
      dsimp [U, V, f]
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at hz
      simp only [Metric.mem_ball, dist_eq_norm]
      have hz_sq : ‖z ^ 2‖ < 4 := by
        rw [norm_pow]
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)]
        exact hz
      simpa using hz_sq
    proper := by
      rw [isProperMap_iff_isCompact_preimage]
      constructor
      · exact ((continuous_pow 2).add continuous_const).continuousOn.mapsToRestrict _
      · intro K hK
        let K' : Set ℂ := Subtype.val '' K
        have hK'_compact : IsCompact K' := hK.image continuous_subtype_val
        have hK'_sub_V : K' ⊆ V := Subtype.coe_image_subset V K

        let S := f ⁻¹' K'
        have hS_compact : IsCompact S := by
          exact (isProperMap_quad_add_const 1).isCompact_preimage hK'_compact

        have hS_sub_U : S ⊆ U := by
          intro z hzS
          have hzV : f z ∈ V := hK'_sub_V hzS
          have hz_sq : ‖z ^ 2‖ < 4 := by
            simpa [V, f, Metric.mem_ball, dist_eq_norm] using hzV
          rw [norm_pow] at hz_sq
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num] at hz_sq
          rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)] at hz_sq
          simpa [U, Metric.mem_ball, dist_zero_right] using hz_sq

        have :
            (MapsTo.restrict f U V (by
              dsimp [U, V, f]
              intro z hz
              simp only [Metric.mem_ball, dist_zero_right] at hz
              simp only [Metric.mem_ball, dist_eq_norm]
              have hz_sq : ‖z ^ 2‖ < 4 := by
                rw [norm_pow]
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
                rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)]
                exact hz
              simpa using hz_sq
            )) ⁻¹' K = {x : U | f x ∈ K'} := by
          ext x
          simp only [mem_preimage, mem_setOf_eq]
          dsimp [K']
          constructor
          · intro h
            exact ⟨_, h, rfl⟩
          · rintro ⟨y, hy, h_eq⟩
            convert hy
            ext
            exact h_eq.symm
        rw [this]
        rw [Subtype.isCompact_iff]
        have : Subtype.val '' {x : U | f x ∈ K'} = S := by
          ext z
          simp only [S, mem_preimage]
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx
          · intro hzS
            exact ⟨⟨z, hS_sub_U hzS⟩, hzS, rfl⟩
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
    simple_critical_point := by
      intro c hc h_deriv
      dsimp [f] at *
      have h_deriv_fun : deriv (fun z : ℂ ↦ z ^ 2 + 1) = (fun z : ℂ ↦ 2 * z) := by
        ext z
        rw [deriv_add_const']
        rw [deriv_pow_field 2]
        simp

      rw [h_deriv_fun]
      rw [deriv_const_mul]
      · rw [deriv_id'']
        norm_num
      · exact differentiableAt_id
  }

/--
A second explicit quadratic-like map in the current scaffold.
This keeps the same quadratic polynomial but on a larger disk pair, providing a
concrete `BMol` point distinct from `defaultBMol`.
-/
noncomputable def largeBMol : BMol :=
  let U := Metric.ball 0 3
  let V := Metric.ball 0 9
  let f := fun z => z^2
  { U := U
    V := V
    f := f
    isOpen_U := Metric.isOpen_ball
    isOpen_V := Metric.isOpen_ball
    isConnected_U := (convex_ball (0:ℂ) 3).isConnected <| Metric.nonempty_ball.2 (by norm_num)
    isConnected_V := (convex_ball (0:ℂ) 9).isConnected <| Metric.nonempty_ball.2 (by norm_num)
    simplyConnected_U := have : ContractibleSpace U := (convex_ball (0:ℂ) 3).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num); inferInstance
    simplyConnected_V := have : ContractibleSpace V := (convex_ball (0:ℂ) 9).contractibleSpace (Metric.nonempty_ball.2 <| by norm_num); inferInstance
    subset := Metric.ball_subset_ball (by norm_num)
    closure_subset := by
      rw [closure_ball (0:ℂ) (by norm_num : (3:ℝ) ≠ 0)]
      apply Metric.closedBall_subset_ball
      norm_num
    differentiable_on := differentiableOn_id.pow 2
    maps_to := by
      dsimp [U, V, f]
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at *
      norm_cast
      rw [norm_pow]
      rw [show (9:ℝ) = 3^2 by norm_num]
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
          rw [show (9:ℝ) = 3^2 by norm_num] at this
          rw [sq_lt_sq, abs_norm, abs_of_nonneg (by norm_num)] at this
          simp [U, Metric.mem_ball, dist_zero_right, this]

        have : (MapsTo.restrict f U V (by
          dsimp [U, V, f]
          intro z hz
          simp only [Metric.mem_ball, dist_zero_right] at *
          norm_cast
          rw [norm_pow]
          rw [show (9:ℝ) = 3^2 by norm_num]
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
    simple_critical_point := by
      intro c hc h_deriv
      dsimp [f] at *
      have h1 : deriv (fun z ↦ z ^ 2) c = 2 * c := by
        rw [deriv_pow_field 2]
        simp
      rw [h1] at h_deriv

      have h_deriv_fun : deriv (fun (z : ℂ) ↦ z^2) = (fun z ↦ 2 * z) := by
        ext z
        rw [deriv_pow_field 2]
        simp

      rw [h_deriv_fun]
      rw [deriv_const_mul]
      · rw [deriv_id'']
        norm_num
      · exact differentiableAt_id
  }

/--
`largeBMol` is genuinely different from the default quadratic model: it contains
`5 / 2` in its source disk while `defaultBMol` does not.
-/
lemma largeBMol_ne_defaultBMol : largeBMol ≠ defaultBMol := by
  intro h_eq
  have h_mem_large : ((5 : ℂ) / 2) ∈ largeBMol.U := by
    simp [largeBMol, Metric.mem_ball, dist_zero_right]
    norm_num
  have h_not_mem_default : ((5 : ℂ) / 2) ∉ defaultBMol.U := by
    simp [defaultBMol, Metric.mem_ball, dist_zero_right]
    norm_num
  exact h_not_mem_default (by simpa [h_eq] using h_mem_large)

/--
`shiftedBMol` is genuinely different from the default quadratic model because
their underlying maps disagree at `0`.
-/
lemma shiftedBMol_ne_defaultBMol : shiftedBMol ≠ defaultBMol := by
  intro h_eq
  have h_at_zero : shiftedBMol.f 0 = defaultBMol.f 0 :=
    congrArg (fun g : BMol => g.f 0) h_eq
  simp [shiftedBMol, defaultBMol] at h_at_zero

/--
The shifted model is not another literal `z ↦ z^2` point.
-/
lemma shiftedBMol_f_ne_sq : shiftedBMol.f ≠ fun z => z ^ 2 := by
  intro h_eq
  have h_at_zero := congrFun h_eq 0
  simp [shiftedBMol] at h_at_zero

/--
The shifted model is still an explicit polynomial point: its underlying map is
evaluation of `X^2 + 1`.
-/
lemma shiftedBMol_f_eq_eval_polynomial_sq_add_one :
    shiftedBMol.f = fun z => Polynomial.eval z (Polynomial.X ^ 2 + Polynomial.C 1) := by
  ext z
  simp [shiftedBMol]

/--
The shifted and large models are genuinely different because their underlying
maps disagree at `0`.
-/
lemma shiftedBMol_ne_largeBMol : shiftedBMol ≠ largeBMol := by
  intro h_eq
  have h_at_zero : shiftedBMol.f 0 = largeBMol.f 0 :=
    congrArg (fun g : BMol => g.f 0) h_eq
  simp [shiftedBMol, largeBMol] at h_at_zero

/-- The default model has zero-value observation `0`. -/
@[simp] theorem bmol_zero_observation_default :
    bmol_zero_observation defaultBMol = 0 := by
  simp [bmol_zero_observation, defaultBMol]

/-- The shifted model has zero-value observation `1`. -/
@[simp] theorem bmol_zero_observation_shifted :
    bmol_zero_observation shiftedBMol = 1 := by
  simp [bmol_zero_observation, shiftedBMol]

/-- The large model shares the same zero-value observation as the default one. -/
@[simp] theorem bmol_zero_observation_large :
    bmol_zero_observation largeBMol = 0 := by
  simp [bmol_zero_observation, largeBMol]

/-- The default model does not contain `5 / 2` in its source domain. -/
@[simp] theorem bmol_large_source_tag_observation_default :
    bmol_large_source_tag_observation defaultBMol = 0 := by
  simp [bmol_large_source_tag_observation, defaultBMol, Metric.mem_ball, dist_zero_right]
  norm_num

/-- The shifted model has the same source disk as `defaultBMol`. -/
@[simp] theorem bmol_large_source_tag_observation_shifted :
    bmol_large_source_tag_observation shiftedBMol = 0 := by
  simp [bmol_large_source_tag_observation, shiftedBMol, Metric.mem_ball, dist_zero_right]
  norm_num

/-- The large model contains the probe point `5 / 2` in its source domain. -/
@[simp] theorem bmol_large_source_tag_observation_large :
    bmol_large_source_tag_observation largeBMol = 1 := by
  simp [bmol_large_source_tag_observation, largeBMol, Metric.mem_ball, dist_zero_right]
  norm_num

/-- The finite observation of `defaultBMol`. -/
@[simp] theorem bmol_finite_observation_default :
    bmol_finite_observation defaultBMol = (0, 0) := by
  simp [bmol_finite_observation]

/-- The finite observation of `shiftedBMol`. -/
@[simp] theorem bmol_finite_observation_shifted :
    bmol_finite_observation shiftedBMol = (1, 0) := by
  simp [bmol_finite_observation]

/-- The finite observation of `largeBMol`. -/
@[simp] theorem bmol_finite_observation_large :
    bmol_finite_observation largeBMol = (0, 1) := by
  simp [bmol_finite_observation]

/--
The induced zero-observation topology already separates the shifted model from
the default one by an open set.
-/
theorem exists_open_separating_default_and_shifted_of_bmol_zero_topology :
    ∃ s : Set BMol,
      IsOpen[bmol_zero_topology] s ∧
        defaultBMol ∈ s ∧
        shiftedBMol ∉ s := by
  refine
    ⟨bmol_zero_observation ⁻¹' Metric.ball 0 (1 / 2 : ℝ), ?_, ?_, ?_⟩
  · exact isOpen_induced_iff.mpr ⟨Metric.ball 0 (1 / 2 : ℝ), Metric.isOpen_ball, rfl⟩
  · simp [Metric.mem_ball]
  · simp [Metric.mem_ball]
    norm_num

/--
The zero-observation topology is not discrete: `defaultBMol` and `largeBMol`
have the same observed value at `0`, so the singleton `{defaultBMol}` is not
open.
-/
theorem not_isOpen_singleton_default_of_bmol_zero_topology :
    ¬ IsOpen[bmol_zero_topology] ({defaultBMol} : Set BMol) := by
  intro h_open
  rcases isOpen_induced_iff.mp h_open with ⟨t, _ht, h_pre⟩
  have h_default_mem : defaultBMol ∈ bmol_zero_observation ⁻¹' t := by
    rw [h_pre]
    simp
  have h_zero_mem : (0 : ℂ) ∈ t := by
    simpa using h_default_mem
  have h_large_mem : largeBMol ∈ bmol_zero_observation ⁻¹' t := by
    simpa using h_zero_mem
  have h_large_singleton : largeBMol ∈ ({defaultBMol} : Set BMol) := by
    rw [← h_pre]
    exact h_large_mem
  exact largeBMol_ne_defaultBMol (by simpa using h_large_singleton)

/-- The named zero-observation topology is a genuine non-discrete candidate. -/
theorem not_discrete_bmol_zero_topology :
    ¬ @DiscreteTopology BMol bmol_zero_topology := by
  intro h_discrete
  have h_open : IsOpen[bmol_zero_topology] ({defaultBMol} : Set BMol) :=
    (@discreteTopology_iff_isOpen_singleton BMol bmol_zero_topology).mp
      h_discrete defaultBMol
  exact not_isOpen_singleton_default_of_bmol_zero_topology h_open

noncomputable instance : Inhabited BMol := ⟨defaultBMol⟩

end Molecule
