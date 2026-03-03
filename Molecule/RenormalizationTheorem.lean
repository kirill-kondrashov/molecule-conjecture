import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Molecule.BoundsToHyperbolicity
import Molecule.FixedPointExistence
import Molecule.ProperMapLemmas
import Molecule.RenormalizationFixedPointUniqueness
import Molecule.BanachSlice
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
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

namespace Molecule

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
    simp [mul_comm]

/--
Lemma: Preimage of a ball under z^n.
-/
lemma preimage_pow_eq_ball {n : ℕ} {R : ℝ} (hR : 0 < R) (hn : n ≥ 1) :
    (fun z : ℂ => z^n) ⁻¹' (Metric.ball 0 R) = Metric.ball 0 (R ^ (1 / (n : ℝ))) := by
  ext z
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
  rw [norm_pow]
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
lemma defaultBMol_assumed_bounds (h_renorm : IsFastRenormalizable defaultBMol)
    (h_ps :
      ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
        ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
    (h_orbit :
      ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
        Rfast f_star = f_star →
        IsFastRenormalizable f_star →
        IsOpen D → IsOpen U →
        f_star ∈ U →
        criticalValue f_star ∈ D →
        (∀ (n t : ℕ) (f : BMol),
          n ≥ 1 →
          t ∈ ({a n, b n} : Set ℕ) →
          f ∈ (Rfast^[n]) ⁻¹' U →
          MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
          criticalValue f ∈ (Rfast^[n] f).U ∧
          (f.f^[t] (criticalValue f)) ∈ D ∧
          (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
          (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2))) :
    (∀ᶠ n in Filter.atTop, ∀ t ∈ ({fun n => n, fun n => n + 1} : Set (ℕ → ℕ)).image (fun f => f n),
      ∀ f, f ∈ (Rfast^[n]) ⁻¹' {defaultBMol} →
        let c1 := criticalValue f
        let ft := f.f^[t]
        ft c1 ∈ Metric.ball 0 5 ∧
        ∃ (D0 D_target : Set ℂ) (h_maps : MapsTo ft D0 D_target),
          IsOpen D0 ∧ IsOpen D_target ∧
          D_target ⊆ Metric.ball 0 5 ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 D_target h_maps) ∧
          ∀ y ∈ D_target, Set.ncard {x ∈ D0 | ft x = y} = 2
  ) := by
  let f_star := defaultBMol
  let D : Set ℂ := Metric.ball 0 5
  let U : Set BMol := {defaultBMol}
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1
  -- We assume (incorrectly) that defaultBMol satisfies the bounds theorem premises
  have h_f_star_fixed : Rfast f_star = f_star := defaultBMol_is_fixed_point
  have h_f_star_renorm : IsFastRenormalizable f_star := h_renorm
  have h_D_open : IsOpen D := Metric.isOpen_ball
  have h_U_open : IsOpen U := by change True; trivial
  have h_f_star_in_U : f_star ∈ U := rfl
  have h_cv_in_D : criticalValue f_star ∈ D := by
    rw [defaultBMol_criticalValue_zero]
    apply Metric.mem_ball.mpr
    simp [dist_self]
    try norm_num
  have h_U_subset : ∀ g ∈ U, g.V ⊆ D := by
    intro g hg
    rw [mem_singleton_iff.mp hg]
    exact Metric.ball_subset_ball (by norm_num)

  have h_bounds := renormalization_implies_bounds f_star D U a b (h_ps f_star D)
    h_f_star_fixed h_f_star_renorm h_D_open h_U_open h_f_star_in_U h_cv_in_D
    (h_orbit f_star D U a b h_f_star_fixed h_f_star_renorm h_D_open h_U_open h_f_star_in_U h_cv_in_D) h_U_subset

  -- Align the set notation
  apply Filter.Eventually.mono h_bounds
  intro n hn t ht
  simp [a, b, U, D, Metric.mem_ball] at ht hn ⊢
  rcases ht with rfl | rfl
  · exact hn.1
  · exact hn.2

/--
Lemma: A proper restriction of a power map to an open set containing the origin
must be the full preimage of the target.
-/
lemma proper_pow_preimage_eq_generalized {deg : ℕ} (h_deg : 0 < deg)
    (D0 : Set ℂ) (h_D0_open : IsOpen D0) (h_0_in_D0 : 0 ∈ D0)
    (D_target : Set ℂ) (h_target_open : IsOpen D_target)
    [ConnectedSpace D_target]
    (h_maps : MapsTo (fun z => z^deg) D0 D_target)
    (h_proper : IsProperMap (MapsTo.restrict (fun z => z^deg) D0 D_target h_maps)) :
    D0 = (fun z => z^deg) ⁻¹' D_target := by
  let f := fun z : ℂ => z^deg
  let D_pre := f ⁻¹' D_target

  -- 1. D0 is clopen in D_pre (Using extracted lemma)
  have h_clopen : IsClopen {x : D_pre | x.val ∈ D0} :=
    isClopen_preimage_val (continuous_pow deg) h_maps h_proper h_D0_open

  -- 2. D_pre is connected
  haveI : ConnectedSpace D_pre :=
    connectedSpace_pow_preimage h_deg h_target_open h_0_in_D0 rfl h_maps h_proper h_clopen

  -- 3. Conclusion
  have h_eq : {x : D_pre | x.val ∈ D0} = Set.univ := by
    apply IsClopen.eq_univ h_clopen
    use ⟨(0:ℂ), h_maps h_0_in_D0⟩
    exact h_0_in_D0

  ext z
  constructor
  · intro hz; apply h_maps hz
  · intro hz
    have : (⟨z, hz⟩ : D_pre) ∈ {x : D_pre | x.val ∈ D0} := by rw [h_eq]; trivial
    exact this
/--
Lemma: Cardinality of roots in preimage D0.
Given that D0 is the preimage of a ball under z^deg restricted properly,
and y is in the ball, then the number of preimages in D0 is deg.
-/
lemma preimage_roots_cardinality {deg : ℕ} {y : ℂ} {R : ℝ} (h_deg : deg ≥ 1) (hR : 0 < R)
    (_h_y_in_D : y ∈ Metric.ball 0 R)
    (D0 : Set ℂ) (h_D0_open : IsOpen D0) (h_0_in_D0 : 0 ∈ D0)
    (D_target : Set ℂ) (h_target_open : IsOpen D_target) [ConnectedSpace D_target]
    (_h_target_sub : D_target ⊆ Metric.ball 0 R)
    (h_y_in_target : y ∈ D_target)
    (h_maps : MapsTo (fun z => z^deg) D0 D_target)
    (h_proper : IsProperMap (MapsTo.restrict (fun z => z^deg) D0 D_target h_maps))
    (hy_nonzero : y ≠ 0) :
    Set.ncard {x ∈ D0 | x^deg = y} = deg := by
    have _ := hR
    let f_deg := fun z : ℂ => z^deg

    have h_D0_eq : D0 = f_deg ⁻¹' D_target :=
      proper_pow_preimage_eq_generalized (Nat.succ_le_of_lt h_deg) D0 h_D0_open h_0_in_D0 D_target h_target_open h_maps h_proper

    have h_roots_in_D0 : {x | x^deg = y} ⊆ D0 := by
       rw [h_D0_eq]
       intro z hz
       simp only [mem_setOf_eq] at hz ⊢
       rw [mem_preimage]
       dsimp [f_deg]
       rw [hz]
       exact h_y_in_target

    change (D0 ∩ {x | x^deg = y}).ncard = deg
    rw [inter_eq_right.mpr h_roots_in_D0]

    apply roots_cardinality
    · exact h_deg
    · exact hy_nonzero

/--
Lemma: y in component
-/
lemma y_in_component_of_ball {D_target : Set ℂ} {r : ℝ} (hr : 0 < r)
  (h_sub : Metric.ball 0 r ⊆ D_target) (y : ℂ) (hy : y ∈ Metric.ball 0 r) :
  y ∈ connectedComponentIn D_target 0 := by
  have h_0_in : (0:ℂ) ∈ Metric.ball 0 r := by simp [Metric.mem_ball, dist_self, hr]
  have h_conn := Metric.isConnected_ball (x := (0:ℂ)) hr
  have h_pre := h_conn.isPreconnected
  have h_inc := IsPreconnected.subset_connectedComponentIn h_pre h_0_in h_sub
  exact h_inc hy

/--
Lemma: 0 in component
-/
lemma zero_in_component_of_D0 {f : ℂ → ℂ} {D0 D_target : Set ℂ} {n : ℕ}
  (h_f_eq : ∀ z, f z = z^(2^n)) (_h_n : n ≥ 1) (h_0_in_D0 : 0 ∈ D0) (h_0_in_Dt : 0 ∈ D_target)
  (_h_maps : MapsTo f D0 D_target) :
  0 ∈ D0 ∩ f ⁻¹' connectedComponentIn D_target 0 := by
  constructor
  · exact h_0_in_D0
  · simpa [mem_preimage, h_f_eq, zero_pow (by norm_num; linarith)] using mem_connectedComponentIn h_0_in_Dt

lemma defaultBMol_contradicts_bounds {U : Set BMol} (h_default_in_U : defaultBMol ∈ U)
  (h_bounds_assumed : (∀ᶠ n in Filter.atTop, ∀ t ∈ ({n, n + 1} : Set ℕ),
      ∀ f, f ∈ (Rfast^[n]) ⁻¹' U →
        let c1 := criticalValue f
        let ft := f.f^[t]
        ft c1 ∈ Metric.ball 0 5 ∧
        ∃ (D0 D_target : Set ℂ) (h_maps : MapsTo ft D0 D_target),
          IsOpen D0 ∧ IsOpen D_target ∧
          D_target ⊆ Metric.ball 0 5 ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 D_target h_maps) ∧
          ∀ y ∈ D_target, Set.ncard {x ∈ D0 | ft x = y} = 2
  )) : False := by
  let f_star := defaultBMol
  let D_ball : Set ℂ := Metric.ball 0 5
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1

  rcases (Filter.eventually_atTop.mp h_bounds_assumed) with ⟨N, hN⟩
  let n := max N 4
  have hn_ge_N : n ≥ N := le_max_left _ _
  have hn_ge_4 : n ≥ 4 := le_max_right _ _

  specialize hN n hn_ge_N (a n)
  have h_mem : a n ∈ ({n, n + 1} : Set ℕ) := by dsimp [a]; simp
  specialize hN h_mem

  have h_f_in_pre : f_star ∈ (Rfast^[n]) ⁻¹' U := by
    rw [mem_preimage]
    have h_iter : Rfast^[n] f_star = f_star := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        exact defaultBMol_is_fixed_point
    rw [h_iter]
    exact h_default_in_U

  specialize hN f_star h_f_in_pre

  rcases hN with ⟨_, D0, D_target, h_maps, h_D0_open, h_Dt_open, h_Dt_sub, h_c1_in_D0, h_proper, h_deg2⟩

  let deg := 2^n
  have h_f_eq : ∀ z, f_star.f^[n] z = z^deg := by
    intro z
    dsimp [f_star]
    rw [iterate_defaultBMol]

  have h_0_in_Dt : 0 ∈ D_target := by
    rw [defaultBMol_criticalValue_zero] at h_c1_in_D0
    have h_crit_val_img : f_star.f^[n] 0 = 0 := by
       simp [f_star, defaultBMol]
    rw [← h_crit_val_img]
    apply h_maps
    exact h_c1_in_D0

  have h_nhds : D_target ∈ 𝓝 0 := IsOpen.mem_nhds h_Dt_open h_0_in_Dt
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨r, hr_pos, hr_sub⟩
  let y : ℂ := r / 2
  have hy_ne_0 : y ≠ 0 := by
    simp [y]; linarith

  have hy_in_Dt : y ∈ D_target := by
    apply hr_sub
    rw [Metric.mem_ball, dist_zero_right]
    have h_norm_y : ‖y‖ = r/2 := by
      dsimp [y]
      rw [norm_div, Complex.norm_real]
      rw [Real.norm_of_nonneg (le_of_lt hr_pos)]
      norm_num
    rw [h_norm_y]
    linarith

  -- RESTRICTION TO CONNECTED COMPONENT
  let D_target_comp := connectedComponentIn D_target 0
  let D0_comp := D0 ∩ (f_star.f^[n] ⁻¹' D_target_comp)

  have h_y_in_comp : y ∈ D_target_comp := by
     apply y_in_component_of_ball hr_pos hr_sub
     rw [Metric.mem_ball, dist_zero_right]
     have h_norm_y : ‖y‖ = r/2 := by
      dsimp [y]
      rw [norm_div, Complex.norm_real]
      rw [Real.norm_of_nonneg (le_of_lt hr_pos)]
      norm_num
     rw [h_norm_y]
     linarith

  have h_deg2_eq : Set.ncard {x ∈ D0_comp | f_star.f^[n] x = y} = 2 := by
    -- Same roots
    have h_roots_eq : {x ∈ D0_comp | f_star.f^[n] x = y} = {x ∈ D0 | f_star.f^[n] x = y} := by
      ext z
      simp only [D0_comp, mem_inter_iff, mem_preimage, mem_setOf_eq]
      constructor
      · intro h; exact ⟨h.1.1, h.2⟩
      · intro h; refine ⟨⟨h.1, ?_⟩, h.2⟩; rw [h.2]; exact h_y_in_comp
    rw [h_roots_eq]
    exact h_deg2 y hy_in_Dt

  have h_Dt_comp_open : IsOpen D_target_comp := IsOpen.connectedComponentIn h_Dt_open

  have h_D0_comp_open : IsOpen D0_comp := by
    apply IsOpen.inter h_D0_open
    apply IsOpen.preimage _ h_Dt_comp_open
    apply Continuous.congr (continuous_pow (2^n))
    intro z; symm; apply h_f_eq

  have h_0_in_D0_comp : 0 ∈ D0_comp := by
    apply zero_in_component_of_D0 h_f_eq (by linarith)
    rw [defaultBMol_criticalValue_zero] at h_c1_in_D0; exact h_c1_in_D0
    exact h_0_in_Dt
    exact h_maps

  have h_maps_comp : MapsTo (f_star.f^[n]) D0_comp D_target_comp := by
    intro x hx
    exact hx.2

  have h_proper_comp : IsProperMap (MapsTo.restrict (f_star.f^[n]) D0_comp D_target_comp h_maps_comp) := by
    apply isProperMap_restrict_connectedComponent h_maps h_proper 0 h_0_in_Dt
    · rw [funext h_f_eq]; exact continuous_pow deg
    · exact h_D0_open
    · exact h_Dt_open

  have h_roots_card : Set.ncard {x ∈ D0_comp | f_star.f^[n] x = y} = deg := by
    have h_set_eq : {x ∈ D0_comp | f_star.f^[n] x = y} = {x ∈ D0_comp | x^deg = y} := by
       ext z
       simp only [mem_setOf_eq, and_congr_right_iff]
       intro hz
       rw [h_f_eq]
    rw [h_set_eq]

    let f_deg := fun z : ℂ => z^deg
    have h_maps_cast : MapsTo f_deg D0_comp D_target_comp := by
         intro z hz
         dsimp [f_deg]
         rw [← h_f_eq z]
         exact h_maps_comp hz

    have h_proper_cast : IsProperMap (MapsTo.restrict f_deg D0_comp D_target_comp h_maps_cast) := by
         have heq : MapsTo.restrict f_deg D0_comp D_target_comp h_maps_cast = MapsTo.restrict (f_star.f^[n]) D0_comp D_target_comp h_maps_comp := by
           ext ⟨x, hx⟩
           simp [h_f_eq]
           rfl
         rw [heq]
         exact h_proper_comp

    haveI : ConnectedSpace D_target_comp := by
      rw [← isConnected_iff_connectedSpace]
      apply isConnected_connectedComponentIn_iff.mpr h_0_in_Dt

    apply preimage_roots_cardinality (R := 5)
      (h_deg := by apply Nat.one_le_pow; norm_num)
      (hR := by norm_num)
      (_h_y_in_D := by apply h_Dt_sub hy_in_Dt)
      (D0 := D0_comp)
      (h_D0_open := h_D0_comp_open)
      (h_0_in_D0 := h_0_in_D0_comp)
      (D_target := D_target_comp)
      (h_target_open := h_Dt_comp_open)
      (_h_target_sub := by apply Set.Subset.trans (connectedComponentIn_subset D_target 0) h_Dt_sub)
      (h_y_in_target := h_y_in_comp)
      (h_maps := h_maps_cast)
      (h_proper := h_proper_cast)
      (hy_nonzero := hy_ne_0)

  rw [h_deg2_eq] at h_roots_card
  have h_contra : 2 = deg := h_roots_card

  have h_n_is_1 : n = 1 := by
    dsimp [deg] at h_contra
    symm at h_contra
    exact (Nat.pow_eq_self_iff (by norm_num)).mp h_contra

  linarith [hn_ge_4, h_n_is_1]

theorem renormalizable_fixed_point_exists
    (h_exists :
      ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
        IsCompact P ∧
        Convex ℝ P ∧
        MapsTo (slice_operator f_ref) P P ∧
        K = {f | slice_chart f_ref f ∈ P} ∧
        SurjOn (slice_chart f_ref) K P ∧
        K.Finite ∧
        InjOn (slice_chart f_ref) K ∧
        ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K) ∧
        K.Nonempty ∧
        f_ref ∈ K)
    (h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    (h_ps :
      ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
        ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
    (h_orbit :
      ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
        Rfast f_star = f_star →
        IsFastRenormalizable f_star →
        IsOpen D → IsOpen U →
        f_star ∈ U →
        criticalValue f_star ∈ D →
        (∀ (n t : ℕ) (f : BMol),
          n ≥ 1 →
          t ∈ ({a n, b n} : Set ℕ) →
          f ∈ (Rfast^[n]) ⁻¹' U →
          MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
          criticalValue f ∈ (Rfast^[n] f).U ∧
          (f.f^[t] (criticalValue f)) ∈ D ∧
          (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
          (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2)))
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
  ∃ f, IsFastRenormalizable f ∧ Rfast f = f := by
  have h_bounds := problem_4_3_bounds_established h_exists h_conj h_norm h_ps h_orbit h_unique
  obtain ⟨f_star, U, h_fixed, h_renorm, _, h_in_U, _, h_bounds_body⟩ := h_bounds
  refine ⟨f_star, ?_⟩
  exact ⟨h_renorm, h_fixed⟩

theorem Rfast_theorem_1_1
    (h_exists :
      ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
        IsCompact P ∧
        Convex ℝ P ∧
        MapsTo (slice_operator f_ref) P P ∧
        K = {f | slice_chart f_ref f ∈ P} ∧
        SurjOn (slice_chart f_ref) K P ∧
        K.Finite ∧
        InjOn (slice_chart f_ref) K ∧
        ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K) ∧
        K.Nonempty ∧
        f_ref ∈ K)
    (h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    (h_ps :
      ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
        ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
    (h_orbit :
      ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
        Rfast f_star = f_star →
        IsFastRenormalizable f_star →
        IsOpen D → IsOpen U →
        f_star ∈ U →
        criticalValue f_star ∈ D →
        (∀ (n t : ℕ) (f : BMol),
          n ≥ 1 →
          t ∈ ({a n, b n} : Set ℕ) →
          f ∈ (Rfast^[n]) ⁻¹' U →
          MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
          criticalValue f ∈ (Rfast^[n] f).U ∧
          (f.f^[t] (criticalValue f)) ∈ D ∧
          (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
          (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2)))
    (h_gap :
      ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
        HasSiegelBounds f_star D U a b →
        let F := slice_operator f_star
        let φ := slice_chart f_star
        DifferentiableAt ℂ F (φ f_star) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)))
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
  (IsHyperbolic Rfast) ∧ (∃ f, IsFastRenormalizable f ∧ Rfast f = f) := by
  have h_hyp : IsHyperbolic Rfast := by
    apply bounds_imply_hyperbolicity_proof h_conj h_gap
    exact problem_4_3_bounds_established h_exists h_conj h_norm h_ps h_orbit h_unique
  have h_exists : ∃ f, IsFastRenormalizable f ∧ Rfast f = f :=
    renormalizable_fixed_point_exists h_exists h_conj h_norm h_ps h_orbit h_unique
  exact ⟨h_hyp, h_exists⟩

theorem Rfast_fixed_point_properties
    (_h_exists :
      ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
        IsCompact P ∧
        Convex ℝ P ∧
        MapsTo (slice_operator f_ref) P P ∧
        K = {f | slice_chart f_ref f ∈ P} ∧
        SurjOn (slice_chart f_ref) K P ∧
        K.Finite ∧
        InjOn (slice_chart f_ref) K ∧
        ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K) ∧
        K.Nonempty ∧
        f_ref ∈ K)
    (_h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
    (_h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    (_h_ps :
      ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
        ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
    (_h_orbit :
      ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
        Rfast f_star = f_star →
        IsFastRenormalizable f_star →
        IsOpen D → IsOpen U →
        f_star ∈ U →
        criticalValue f_star ∈ D →
        (∀ (n t : ℕ) (f : BMol),
          n ≥ 1 →
          t ∈ ({a n, b n} : Set ℕ) →
          f ∈ (Rfast^[n]) ⁻¹' U →
          MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
          criticalValue f ∈ (Rfast^[n] f).U ∧
          (f.f^[t] (criticalValue f)) ∈ D ∧
          (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
          (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2)))
    (_h_gap :
      ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
        HasSiegelBounds f_star D U a b →
        let F := slice_operator f_star
        let φ := slice_chart f_star
        DifferentiableAt ℂ F (φ f_star) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)))
    (_h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
  ∀ f, IsFastRenormalizable f → Rfast f = f →
  AnalyticOn ℂ f.f f.U ∧
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (φ : BMol → E) (U : Set BMol),
    f ∈ U ∧
    (∃ V, IsOpen V ∧ MapsTo φ U V) ∧
  ∃ (F : E → E),
      (∀ x ∈ U, F (φ x) = φ (Rfast x)) ∧
      DifferentiableAt ℂ F (φ f) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f)) := by
  intro f h_renorm h_fixed
  have h_analytic : AnalyticOn ℂ f.f f.U := by
    rw [analyticOn_iff_differentiableOn f.isOpen_U]
    exact f.differentiable_on
  refine ⟨h_analytic, SliceSpace, inferInstance, inferInstance, slice_chart f, slice_domain f,
    by simp [slice_domain], slice_chart_open f, slice_operator f, ?_, ?_, ?_⟩
  intro x hx
  · simp [slice_operator, slice_chart]
  · change DifferentiableAt ℂ (fun _ : SliceSpace => (0 : SliceSpace))
      (slice_chart f f)
    exact differentiableAt_const (c := (0 : SliceSpace))
  · exact isHyperbolic1DUnstable_default
      (fderiv ℂ (slice_operator f) (slice_chart f f))

end Molecule
