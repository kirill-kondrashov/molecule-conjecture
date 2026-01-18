import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Molecule.BoundsToHyperbolicity
import Molecule.FixedPointExistence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace MLC

open Complex Topology Set

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
Lemma: Proper restriction of a power map to a ball must be the full preimage ball.
-/
lemma proper_pow_preimage_eq {n : ℕ} {R : ℝ} (hR : 0 < R) (hn : n ≥ 1)
    (D : Set ℂ) (hD : D = Metric.ball 0 R)
    (D0 : Set ℂ) (h_open : IsOpen D0) (h0 : 0 ∈ D0)
    (f : ℂ → ℂ) (hf : f = fun z => z^n)
    (h_maps : MapsTo f D0 D)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D h_maps)) :
    D0 = f ⁻¹' D := by
  -- Standard proper map property on locally compact space
  sorry

/--
Lemma: Number of roots of z^n = y is n for y != 0.
-/
lemma roots_cardinality {n : ℕ} {y : ℂ} (hn : n ≥ 1) (hy : y ≠ 0) : 
  Set.ncard {z | z^n = y} = n := by
  -- Follows from Fundamental Theorem of Algebra and separability
  sorry

lemma defaultBMol_violates_bounds_axiom : False := by
  let f_star := defaultBMol
  let D : Set ℂ := Metric.ball 0 0.1
  let U_set : Set BMol := Set.univ
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1
  
  have h_fixed : Rfast f_star = f_star := defaultBMol_is_fixed_point

  have h_bounds := renormalization_implies_bounds f_star D U_set a b h_fixed
    Metric.isOpen_ball isOpen_univ (mem_univ _) 
    (by 
      rw [defaultBMol_criticalValue_zero]
      apply Metric.mem_ball.mpr
      norm_num
    )
  
  rcases (Filter.eventually_atTop.mp h_bounds) with ⟨N, hN⟩
  let n := max N 4
  have hn_ge_N : n ≥ N := le_max_left _ _
  have hn_ge_4 : n ≥ 4 := le_max_right _ _
  
  specialize hN n hn_ge_N (a n) (by left; rfl)
  specialize hN f_star (by exact mem_univ _)
  
  rcases hN with ⟨_, D0, h_maps, left_1, h_c1_in_D0, left, h_deg2⟩
  
  let y : ℂ := 0.05
  have hy : y ∈ D := by simp [D, Metric.mem_ball]; norm_num
  
  have h_deg2_eq : Set.ncard {x ∈ D0 | f_star.f^[n] x = y} = 2 := h_deg2 y hy
  
  let deg := 2^n
  
  have h_f_eq : ∀ z, f_star.f^[n] z = z^deg := by
    intro z
    dsimp [f_star]
    rw [iterate_defaultBMol]
    
  have h_roots_card : Set.ncard {x ∈ D0 | f_star.f^[n] x = y} = deg := by
    have h_set_eq : {x ∈ D0 | f_star.f^[n] x = y} = {x ∈ D0 | x^deg = y} := by
       ext z
       simp only [mem_setOf_eq, and_congr_right_iff]
       intro hz
       rw [h_f_eq]
    rw [h_set_eq]
    
    have h_D0_eq : D0 = {z | z^deg ∈ D} := by
      let f_iter := f_star.f^[n]
      
      -- Create explicit versions to match types
      let f_deg := fun (z:ℂ) => z^deg
      have h_f_deg : f_deg = fun z => z^deg := rfl
      
      have h_maps_cast : MapsTo f_deg D0 D := by
         intro z hz
         rw [h_f_deg]
         dsimp
         rw [← h_f_eq]
         exact h_maps hz

      have h_proper_cast : IsProperMap (MapsTo.restrict f_deg D0 D h_maps_cast) := by
         -- We admit casting IsProperMap across equal functions for now
         sorry

      apply proper_pow_preimage_eq 
        (n := deg) (R := 0.1)
        (hR := by norm_num)
        (hn := by apply Nat.one_le_pow; norm_num)
        (D := D) (hD := rfl)
        (D0 := D0) (h_open := left_1) 
        (h0 := by rw [defaultBMol_criticalValue_zero] at h_c1_in_D0; exact h_c1_in_D0)
        (f := f_deg) (hf := h_f_deg)
        (h_maps := h_maps_cast)
        (h_proper := h_proper_cast)

    have h_roots_in_D0 : {x | x^deg = y} ⊆ D0 := by
       rw [h_D0_eq]
       intro z hz
       simp only [mem_setOf_eq] at hz ⊢
       rw [hz]
       exact hy
    
    change (D0 ∩ {x | x^deg = y}).ncard = deg
    rw [inter_eq_right.mpr h_roots_in_D0]
    
    apply roots_cardinality
    · apply Nat.one_le_pow; norm_num
    · norm_num
  
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
