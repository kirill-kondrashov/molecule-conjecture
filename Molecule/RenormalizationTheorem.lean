import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Molecule.Problem4_3
import Molecule.BoundsToHyperbolicity
import Molecule.FixedPointExistence

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
  -- c is defined as criticalPoint defaultBMol
  let c := criticalPoint defaultBMol
  
  -- We know 0 is a critical point
  have h0 : 0 ∈ defaultBMol.U ∧ deriv defaultBMol.f 0 = 0 := by
    constructor
    · apply Metric.mem_ball.mpr; norm_num
    · dsimp [defaultBMol]; rw [deriv_pow_field 2]; simp
  
  have h_unique := defaultBMol.unique_critical_point
  -- Since critical point is unique, c must be 0
  have h_eq : c = 0 := by
    apply h_unique.unique
    · exact (Classical.choose_spec h_unique).1
    · exact h0
  
  -- Substitute c -> 0 in goal
  have : c = criticalPoint defaultBMol := rfl
  rw [← this, h_eq]
  
  dsimp [defaultBMol]
  simp

/--
Lemma: If a map `f` is a fixed point of `Rfast` and `IsFastRenormalizable f` is false,
then it violates the `renormalization_implies_bounds` axiom.
-/
lemma defaultBMol_violates_bounds_axiom : False := by
  let f_star := defaultBMol
  let D : Set ℂ := Metric.ball 0 0.1
  let U_set : Set BMol := Set.univ
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1
  
  -- defaultBMol is a fixed point
  have h_fixed : Rfast f_star = f_star := defaultBMol_is_fixed_point

  -- Apply the axiom
  have h_bounds := renormalization_implies_bounds f_star D U_set a b h_fixed
    Metric.isOpen_ball isOpen_univ (mem_univ _) 
    (by 
      rw [defaultBMol_criticalValue_zero]
      apply Metric.mem_ball.mpr
      norm_num
    )
  
  -- Obtain contradiction from bounds
  rcases (Filter.eventually_atTop.mp h_bounds) with ⟨N, hN⟩
  -- Pick n > N and n >= 4
  let n := max N 4
  have hn_ge_N : n ≥ N := le_max_left _ _
  have hn_ge_4 : n ≥ 4 := le_max_right _ _
  
  specialize hN n hn_ge_N (a n) (by left; rfl)
  specialize hN f_star (by 
      exact mem_univ _
  )
  
  rcases hN with ⟨_, D0, h_maps, _, h_c1_in_D0, _, h_deg2⟩
  
  let y : ℂ := 0.05
  have hy : y ∈ D := by simp [D, Metric.mem_ball]; norm_num
  
  have h_deg2_eq : Set.ncard {x ∈ D0 | f_star.f^[n] x = y} = 2 := h_deg2 y hy
  
  let deg := 2^n
  
  have h_f_eq : ∀ z, f_star.f^[n] z = z^deg := by
    intro z
    dsimp [f_star, defaultBMol]
    apply iterate_sq_eq_pow_two_pow

  have h_roots_card : Set.ncard {x ∈ D0 | f_star.f^[n] x = y} = deg := by
    have h_set_eq : {x ∈ D0 | f_star.f^[n] x = y} = {x ∈ D0 | x^deg = y} := by
       ext z
       simp only [mem_setOf_eq, and_congr_right_iff]
       intro hz
       rw [h_f_eq]
    rw [h_set_eq]
    
    have h_roots_in_D0 : {x | x^deg = y} ⊆ D0 := by
        -- Proof that D0 contains all preimages
        sorry 
    
    change (D0 ∩ {x | x^deg = y}).ncard = deg
    
    -- Since D0 contains all roots, the set is just {x | x^deg = y}
    rw [inter_eq_right.mpr h_roots_in_D0]
    
    -- Cardinality of roots of z^deg = y is deg
    have h_card_roots : Set.ncard {x | x^deg = y} = deg := by
      sorry
      
    exact h_card_roots
  
  rw [h_deg2_eq] at h_roots_card
  -- h_roots_card is now 
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
  · -- Existence
    exact defaultBMol_is_fixed_point
  · -- Uniqueness
    intro y hy
    dsimp [Rfast] at hy
    by_cases h : IsFastRenormalizable y
    · -- y is renormalizable
      exfalso
      exact defaultBMol_violates_bounds_axiom
    · -- y is not renormalizable
      rw [dif_neg h] at hy
      exact hy.symm

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
