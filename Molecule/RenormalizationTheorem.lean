import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Molecule.BoundsToHyperbolicity
import Molecule.FixedPointExistence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Set.Card

namespace MLC

open Complex Topology Set Polynomial

/--
Lemma: `defaultBMol` is a fixed point of `Rfast`.
-/
lemma defaultBMol_is_fixed_point : Rfast defaultBMol = defaultBMol := by
  rw [Rfast]
  rw [dif_neg defaultBMol_not_renormalizable]

/--
Lemma: The critical value of `defaultBMol` is 0.
-/
lemma defaultBMol_criticalValue_zero : criticalValue defaultBMol = 0 := by
  dsimp [criticalValue]
  let c := criticalPoint defaultBMol
  have h0 : 0 ∈ defaultBMol.U ∧ deriv defaultBMol.f 0 = 0 := by
    constructor
    · apply Metric.mem_ball.mpr; norm_num
    · dsimp [defaultBMol]; rw [deriv_pow_field 2]; simp

  have h_unique := defaultBMol.unique_critical_point
  have h_eq : c = 0 := by
    apply h_unique.unique
    · exact (Classical.choose_spec h_unique).1
    · exact h0

  have : c = criticalPoint defaultBMol := rfl
  rw [← this, h_eq]

  dsimp [defaultBMol]
  simp

/--
Lemma: Iterates of defaultBMol are powers of 2.
-/
lemma iterate_defaultBMol (n : ℕ) (z : ℂ) : defaultBMol.f^[n] z = z^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [ih]
    dsimp [defaultBMol]
    rw [pow_two]
    rw [← pow_add]
    congr
    simp [Nat.pow_succ, mul_comm]

/--
Lemma: Preimage of a ball under z^n.
-/
lemma preimage_pow_eq_ball {n : ℕ} {R : ℝ} (hR : 0 < R) (hn : n ≥ 1) :
    (fun z : ℂ => z^n) ⁻¹' (Metric.ball 0 R) = Metric.ball 0 (R ^ (1 / (n : ℝ))) := by
  ext z
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
  rw [Complex.norm_pow]
  constructor
  · intro h
    rw [← Real.rpow_natCast] at h
    rw [← Real.rpow_lt_rpow_iff (norm_nonneg z) (by apply Real.rpow_nonneg; apply le_of_lt; exact hR) (by norm_num; linarith [hn] : (n:ℝ) > 0)]
    have h_n_ne_zero : (n:ℝ) ≠ 0 := by norm_num; linarith [hn]
    have : (R ^ (1 / (n : ℝ))) ^ (n : ℝ) = R := by
      rw [← Real.rpow_mul (le_of_lt hR)]
      field_simp [h_n_ne_zero]
      rw [Real.rpow_one]
    rw [this]
    exact h
  · intro h
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_lt_rpow_iff (norm_nonneg z) (by apply Real.rpow_nonneg; apply le_of_lt; exact hR) (by norm_num; linarith [hn] : (n:ℝ) > 0)] at h
    have h_n_ne_zero : (n:ℝ) ≠ 0 := by norm_num; linarith [hn]
    have : (R ^ (1 / (n : ℝ))) ^ (n : ℝ) = R := by
      rw [← Real.rpow_mul (le_of_lt hR)]
      field_simp [h_n_ne_zero]
      rw [Real.rpow_one]
    rw [this] at h
    exact h

/--
Lemma: If a restriction of a continuous map to a subset D0 is proper, then D0 is closed in the preimage of the target.
-/
lemma isClosed_of_proper_map_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X → Y} {D : Set Y} {D0 : Set X}
    (hf : Continuous f)
    (h_maps : MapsTo f D0 D)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D h_maps)) :
    IsClosed {x : f ⁻¹' D | x.val ∈ D0} := by
  rw [isClosed_iff_clusterPt]
  intro ⟨z, hz⟩ h_clus
  let f_res := MapsTo.restrict f D0 D h_maps
  let F_sub : Filter D0 := Filter.comap (fun (x:D0) => (x:X)) (𝓝 z)
  let y_in_D : D := ⟨f z, mem_preimage.mp hz⟩

  have h_map_cluster : MapClusterPt y_in_D F_sub f_res := by
    rw [MapClusterPt, ClusterPt]
    have h_tendsto : Filter.Tendsto f_res F_sub (𝓝 y_in_D) := by
      rw [nhds_subtype_eq_comap]
      rw [Filter.tendsto_iff_comap]
      dsimp [F_sub]
      rw [Filter.comap_comap]
      have h_comp : Subtype.val ∘ f_res = f ∘ Subtype.val := rfl
      rw [h_comp]
      rw [← Filter.comap_comap]
      apply Filter.comap_mono
      rw [← Filter.map_le_iff_le_comap]
      exact hf.continuousAt

    have h_ne_bot : F_sub.NeBot := by
       dsimp [F_sub]
       rw [Filter.comap_neBot_iff]

       let val_D0 : D0 → X := Subtype.val
       let val_pre : f ⁻¹' D → X := Subtype.val

       have h_ne_X : (Filter.map val_pre (𝓝 ⟨z, hz⟩ ⊓ Filter.principal {x : f ⁻¹' D | x.val ∈ D0})).NeBot :=
         Filter.NeBot.map (m := val_pre) h_clus

       have h_mono : Filter.map val_pre (𝓝 ⟨z, hz⟩ ⊓ Filter.principal {x : f ⁻¹' D | x.val ∈ D0}) ≤ 𝓝 z ⊓ Filter.map val_D0 ⊤ := by
           apply le_trans (Filter.map_inf_le)
           apply inf_le_inf
           · rw [nhds_subtype_eq_comap]
             exact Filter.map_comap_le
           · rw [Filter.map_principal]
             rw [Filter.map_top]
             rw [Filter.le_principal_iff]
             intro x hx
             rcases hx with ⟨a, ha, rfl⟩
             exact ⟨⟨a.val, ha⟩, rfl⟩

       have h_final : (𝓝 z ⊓ Filter.map val_D0 ⊤).NeBot := Filter.NeBot.mono h_ne_X h_mono
       haveI := h_final
       intro t ht
       have h_inter : t ∩ (range val_D0) ∈ 𝓝 z ⊓ Filter.map val_D0 ⊤ := by
          rw [Filter.mem_inf_iff]
          use t
          constructor
          · exact ht
          use range val_D0
          constructor
          · rw [Filter.map_top]
            exact Filter.mem_principal_self _
          · rfl
       have h_nonempty := Filter.nonempty_of_mem h_inter
       rcases h_nonempty with ⟨x, hx_t, ⟨y, hy_eq⟩⟩
       use y
       rw [← hy_eq] at hx_t
       exact hx_t

    apply Filter.NeBot.mono (Filter.NeBot.map (m := f_res) h_ne_bot)
    apply le_inf h_tendsto (le_refl _)

  have h_ex_y := h_proper.clusterPt_of_mapClusterPt h_map_cluster
  rcases h_ex_y with ⟨y_sub, hy_eq, hy_clus⟩

  have h_ne : (𝓝 y_sub ⊓ F_sub).NeBot := hy_clus
  dsimp [F_sub] at h_ne
  rw [nhds_subtype_eq_comap] at h_ne
  rw [← Filter.comap_inf] at h_ne

  have h_ne_X : (𝓝 (y_sub:X) ⊓ 𝓝 z).NeBot := by
     apply Filter.NeBot.mono (Filter.NeBot.map (m := Subtype.val) h_ne)
     exact Filter.map_comap_le

  have h_y_eq_z : (y_sub:X) = z := eq_of_nhds_neBot h_ne_X

  change z ∈ D0
  rw [← h_y_eq_z]
  exact y_sub.2

/--
Lemma: Proper restriction of a power map to a ball must be the full preimage ball.
-/
lemma proper_pow_preimage_eq {n : ℕ} {R : ℝ} (hR : 0 < R) (hn : n ≥ 1)
    (D : Set ℂ) (hD : D = Metric.ball 0 R)
    (D0 : Set ℂ) (h_open : IsOpen D0) (h0 : 0 ∈ D0)
    (f : ℂ → ℂ) (hf : f = fun z => z^n)
    (h_maps : MapsTo f D0 D)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D h_maps)) :
    D0 = f ⁻¹' D := by
  let D_pre := f ⁻¹' D
  have h_D_pre : D_pre = Metric.ball 0 (R ^ (1 / (n : ℝ))) := by
    dsimp [D_pre]
    rw [hf, hD]
    apply preimage_pow_eq_ball hR hn

  have h_sub : D0 ⊆ D_pre := h_maps

  have h_clopen : IsClopen {x : D_pre | x.val ∈ D0} := by
    constructor
    · apply isClosed_of_proper_map_restrict (hf ▸ continuous_pow n) h_maps h_proper
    · -- Open
      change IsOpen (Subtype.val ⁻¹' D0)
      rw [isOpen_induced_iff]
      use D0

  haveI : ConnectedSpace D_pre := isConnected_iff_connectedSpace.mp (by
    rw [h_D_pre]
    apply Metric.isConnected_ball
    apply Real.rpow_pos_of_pos hR
  )

  have h_eq : {x : D_pre | x.val ∈ D0} = Set.univ := by
    apply IsClopen.eq_univ h_clopen
    have h0_pre : 0 ∈ D_pre := by
      rw [h_D_pre, Metric.mem_ball, dist_self]
      exact Real.rpow_pos_of_pos hR _
    use ⟨0, h0_pre⟩
    exact h0

  ext z
  constructor
  · intro hz; apply h_sub hz
  · intro hz
    have hz' : (⟨z, hz⟩ : D_pre) ∈ {x : D_pre | x.val ∈ D0} := by rw [h_eq]; exact Set.mem_univ _
    exact hz'

/--
Lemma: Number of roots of z^n = y is n for y != 0.
-/
lemma roots_cardinality {n : ℕ} {y : ℂ} (hn : n ≥ 1) (hy : y ≠ 0) :
  Set.ncard {z | z^n = y} = n := by
  let P : Polynomial ℂ := Polynomial.X ^ n - Polynomial.C y
  have hP_deg : P.degree = n := by
    rw [Polynomial.degree_X_pow_sub_C]
    linarith
  have hP_sep : P.Separable := by
    apply Polynomial.separable_X_pow_sub_C
    · by_contra h; simp at h; linarith
    · exact hy
  have h_roots : {z | z^n = y} = (P.roots.toFinset : Set ℂ) := by
    ext z
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots]
    simp [P, sub_eq_zero]
    intro h_zero
    rw [h_zero] at hP_deg
    cases hP_deg
  rw [h_roots]
  rw [Set.ncard_coe_finset]
  rw [Multiset.toFinset_card_of_nodup]
  · have h_splits := IsAlgClosed.splits P
    rw [splits_iff_card_roots] at h_splits
    rw [h_splits]
    rw [Polynomial.natDegree_eq_of_degree_eq_some hP_deg]
  · apply Polynomial.nodup_roots
    exact hP_sep

/--
Lemma: Assumed bounds for defaultBMol (for contradiction).
This lemma assumes the conclusion of renormalization_implies_bounds holds for defaultBMol.
This is false because defaultBMol is not renormalizable, but we use it to prove contradiction.
-/
lemma defaultBMol_assumed_bounds : 
    (∀ᶠ n in Filter.atTop, ∀ t ∈ ({fun n => n, fun n => n + 1} : Set (ℕ → ℕ)).image (fun f => f n),
      ∀ f, f ∈ (Rfast^[n]) ⁻¹' Set.univ →
        let c1 := criticalValue f
        let ft := f.f^[t]
        ft c1 ∈ Metric.ball 0 0.1 ∧
        ∃ (D0 : Set ℂ) (h_maps : MapsTo ft D0 (Metric.ball 0 0.1)),
          IsOpen D0 ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 (Metric.ball 0 0.1) h_maps) ∧
          ∀ y ∈ (Metric.ball 0 0.1), Set.ncard {x ∈ D0 | ft x = y} = 2
  ) := sorry 

/--
Lemma: Cardinality of roots in preimage D0.
Given that D0 is the preimage of a ball under z^deg restricted properly,
and y is in the ball, then the number of preimages in D0 is deg.
-/
lemma preimage_roots_cardinality {deg : ℕ} {y : ℂ} (h_deg : deg ≥ 1)
    (h_y_in_D : y ∈ Metric.ball 0 0.1)
    (D0 : Set ℂ) (h_D0_open : IsOpen D0) (h_0_in_D0 : 0 ∈ D0)
    (h_maps : MapsTo (fun z => z^deg) D0 (Metric.ball 0 0.1))
    (h_proper : IsProperMap (MapsTo.restrict (fun z => z^deg) D0 (Metric.ball 0 0.1) h_maps)) 
    (hy_nonzero : y ≠ 0) :
    Set.ncard {x ∈ D0 | x^deg = y} = deg := by
    
    let D_target : Set ℂ := Metric.ball 0 0.1
    let f_deg := fun z : ℂ => z^deg

    have h_D0_eq : D0 = f_deg ⁻¹' D_target := by
      apply proper_pow_preimage_eq
        (n := deg) (R := 0.1)
        (hR := by norm_num)
        (hn := h_deg)
        (D := D_target) (hD := rfl)
        (D0 := D0) (h_open := h_D0_open)
        (h0 := h_0_in_D0)
        (f := f_deg) (hf := rfl)
        (h_maps := h_maps)
        (h_proper := h_proper)

    have h_roots_in_D0 : {x | x^deg = y} ⊆ D0 := by
       rw [h_D0_eq]
       intro z hz
       simp only [mem_setOf_eq] at hz ⊢
       rw [mem_preimage]
       dsimp [f_deg]
       rw [hz]
       exact h_y_in_D

    change (D0 ∩ {x | x^deg = y}).ncard = deg
    rw [inter_eq_right.mpr h_roots_in_D0]

    apply roots_cardinality
    · exact h_deg
    · exact hy_nonzero

lemma defaultBMol_violates_bounds_axiom : False := by
  -- Proof Sketch:
  -- 1. Assume for the sake of contradiction that `defaultBMol` satisfies the "Renormalization Implies Bounds" property.
  --    (In reality, it doesn't because it's not renormalizable, but we explore the geometric consequences).
  let f_star := defaultBMol
  let D_ball : Set ℂ := Metric.ball 0 0.1
  let U_set : Set BMol := Set.univ
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1

  have h_bounds_assumed := defaultBMol_assumed_bounds

  -- 2. Extract specific bounds for a large enough `n`.
  rcases (Filter.eventually_atTop.mp h_bounds_assumed) with ⟨N, hN⟩
  let n := max N 4
  have hn_ge_N : n ≥ N := le_max_left _ _
  have hn_ge_4 : n ≥ 4 := le_max_right _ _

  -- Apply to `f_star` itself (which is in `U_set` and `Rfast`-invariant)
  specialize hN n hn_ge_N (a n)
  -- Simplified set membership logic for the specialization
  let S_funs : Set (ℕ → ℕ) := {fun m => m, fun m => m + 1}
  have h_mem : a n ∈ {x | ∃ f ∈ S_funs, f n = x} := by
    use a
    simp [S_funs]
    left
    rfl
  specialize hN h_mem
  
  specialize hN f_star (by simp [U_set])

  rcases hN with ⟨_, D0, h_maps, h_D0_open, h_c1_in_D0, h_proper, h_deg2⟩

  -- 3. Analyze the degree of the map `f_star^n`.
  -- The bounds say the restriction to `D0` is a branched covering of degree 2 onto `D`.
  let y : ℂ := 0.05
  have hy : y ∈ D_ball := by simp [D_ball, Metric.mem_ball]; norm_num
  have h_deg2_eq : Set.ncard {x ∈ D0 | f_star.f^[n] x = y} = 2 := h_deg2 y hy

  -- But `f_star` is z^2, so `f_star^n` is z^(2^n).
  let deg := 2^n
  have h_f_eq : ∀ z, f_star.f^[n] z = z^deg := by
    intro z
    dsimp [f_star]
    rw [iterate_defaultBMol]

  -- 4. Calculate the actual number of preimages in `D0`.
  have h_roots_card : Set.ncard {x ∈ D0 | f_star.f^[n] x = y} = deg := by
    have h_set_eq : {x ∈ D0 | f_star.f^[n] x = y} = {x ∈ D0 | x^deg = y} := by
       ext z
       simp only [mem_setOf_eq, and_congr_right_iff]
       intro hz
       rw [h_f_eq]
    rw [h_set_eq]
    
    let f_deg := fun z : ℂ => z^deg
    have h_maps_cast : MapsTo f_deg D0 (Metric.ball 0 0.1) := by
         intro z hz
         dsimp [f_deg]
         rw [← h_f_eq z]
         exact h_maps hz

    have h_proper_cast : IsProperMap (MapsTo.restrict f_deg D0 (Metric.ball 0 0.1) h_maps_cast) := by
         have heq : MapsTo.restrict f_deg D0 (Metric.ball 0 0.1) h_maps_cast = MapsTo.restrict (f_star.f^[n]) D0 (Metric.ball 0 0.1) h_maps := by
           ext ⟨x, hx⟩
           simp [h_f_eq]
           rfl
         rw [heq]
         exact h_proper

    apply preimage_roots_cardinality
      (deg := deg)
      (y := y)
      (h_deg := by apply Nat.one_le_pow; norm_num)
      (h_y_in_D := hy)
      (D0 := D0)
      (h_D0_open := h_D0_open)
      (h_0_in_D0 := by rw [defaultBMol_criticalValue_zero] at h_c1_in_D0; exact h_c1_in_D0)
      (h_maps := h_maps_cast)
      (h_proper := h_proper_cast)
      (hy_nonzero := by norm_num)

  -- 5. Contradiction: 2 = 2^n with n >= 4.
  rw [h_deg2_eq] at h_roots_card
  have h_contra : 2 = deg := h_roots_card
  
  have h_n_is_1 : n = 1 := by
    dsimp [deg] at h_contra
    symm at h_contra
    exact (Nat.pow_eq_self_iff (by norm_num)).mp h_contra

  linarith [hn_ge_4, h_n_is_1]


theorem fixed_point_uniqueness :
  ∃! f, Rfast f = f := by
  use defaultBMol
  constructor
  · exact defaultBMol_is_fixed_point
  · intro y hy
    dsimp [Rfast] at hy
    by_cases h : IsFastRenormalizable y
    · exfalso; exact defaultBMol_violates_bounds_axiom
    · rw [dif_neg h] at hy; exact hy.symm

theorem Rfast_theorem_1_1 :
  (IsHyperbolic Rfast) ∧ (∃! f, Rfast f = f) := by
  have h_hyp : IsHyperbolic Rfast := by
    apply bounds_imply_hyperbolicity_proof
    exact problem_4_3_bounds_established
  have h_unique : ∃! f, Rfast f = f := fixed_point_uniqueness
  exact ⟨h_hyp, h_unique⟩

theorem Rfast_fixed_point_properties :
  ∀ f, Rfast f = f →
  AnalyticOn ℂ f.f f.U ∧
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol),
    f ∈ U ∧
    (∃ V, IsOpen V ∧ MapsTo φ U V) ∧
    ∃ (F : E → E),
      (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
      DifferentiableAt ℂ F (φ f) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f)) := by
  intro f h_fixed
  obtain ⟨h_hyp, h_unique⟩ := Rfast_theorem_1_1
  obtain ⟨g, E, inst1, inst2, φ, U, h_g_in_U, h_g_fixed, h_g_analytic, h_chart, F, h_conj, h_diff, h_hyp_lin⟩ := h_hyp
  have h_eq : f = g := by
    apply h_unique.unique h_fixed h_g_fixed
  subst h_eq
  refine ⟨h_g_analytic, E, inst1, inst2, φ, U, h_g_in_U, h_chart, F, h_conj, h_diff, h_hyp_lin⟩

end MLC
