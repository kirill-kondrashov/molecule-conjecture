import Molecule.BMol
import Molecule.Rfast
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Basic

namespace MLC

open Complex Topology Set Filter

lemma iterate_sq_eq_pow_two_pow (n : ℕ) (z : ℂ) : (fun w => w^2)^[n] z = z^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [ih]
    rw [pow_two]
    rw [← pow_add]
    congr 1
    rw [pow_succ, mul_comm, two_mul]

-- Helper lemmas for derivatives

lemma h_LHS_deriv_aux (f : ℂ → ℂ) (ψ : ℂ → ℂ) (c : ℂ)
    (h_diff_f : DifferentiableAt ℂ f c)
    (h_diff_ψ : DifferentiableAt ℂ ψ (f c))
    (hc_crit : deriv f c = 0) :
    deriv (ψ ∘ f) c = 0 := by
  rw [deriv_comp c h_diff_ψ h_diff_f]
  rw [hc_crit]
  simp

lemma h_RHS_deriv_aux (N : ℕ) (ψ : ℂ → ℂ) (c : ℂ) (a : ℂ)
    (h_diff_ψ : DifferentiableAt ℂ ψ c)
    (h_deriv_ψ : deriv ψ c = a) :
    deriv (fun z => (ψ z)^N) c = N * (ψ c)^(N-1) * a := by
  change deriv (ψ^N) c = _
  rw [deriv_pow h_diff_ψ N]
  rw [h_deriv_ψ]

lemma h_LHS_deriv2_aux (f : ℂ → ℂ) (ψ : ℂ → ℂ) (c : ℂ) (a : ℂ) (U : Set ℂ)
    (hc : c ∈ U)
    (h_open : IsOpen U)
    (h_diff_f : DifferentiableOn ℂ f U)
    (h_diff_ψ : Differentiable ℂ ψ) 
    (h_diff_deriv_f : DifferentiableAt ℂ (deriv f) c)
    (h_deriv_ψ_const : ∀ z, deriv ψ z = a) :
    deriv (deriv (fun z => ψ (f z))) c = a * deriv (deriv f) c := by
  have h_local : ∀ᶠ z in 𝓝 c, deriv (fun w => ψ (f w)) z = a * deriv f z := by
    filter_upwards [h_open.mem_nhds hc] with z hz
    change deriv (ψ ∘ f) z = _
    rw [deriv_comp z (h_diff_ψ.differentiableAt (x := f z)) (h_diff_f.differentiableAt (h_open.mem_nhds hz))]
    rw [h_deriv_ψ_const (f z)]
  rw [Filter.EventuallyEq.deriv_eq h_local]
  rw [deriv_const_mul a h_diff_deriv_f]
  rfl

lemma h_RHS_deriv2_aux (N : ℕ) (ψ : ℂ → ℂ) (c : ℂ) (a : ℂ) (hN : N ≥ 4)
    (h_diff_ψ : Differentiable ℂ ψ)
    (h_deriv_ψ_const : ∀ z, deriv ψ z = a)
    (h_psi_c : ψ c = 0) :
    deriv (deriv (fun z => (ψ z)^N)) c = 0 := by
  have h_local : ∀ᶠ z in 𝓝 c, deriv (fun w => (ψ w)^N) z = (N:ℂ) * a * (ψ z)^(N-1) := by
    filter_upwards with z
    change deriv (ψ^N) z = _
    rw [deriv_pow (h_diff_ψ z) N]
    rw [h_deriv_ψ_const z]
    ring
  
  rw [Filter.EventuallyEq.deriv_eq h_local]
  change deriv (fun x => ((N:ℂ)*a) * (ψ^(N-1)) x) c = _
  rw [deriv_const_mul ((N:ℂ)*a) (DifferentiableAt.pow (h_diff_ψ c) (N-1))]
  rw [deriv_pow (h_diff_ψ c) (N-1)]
  rw [h_psi_c]
  -- (0)^(N-2)
  have h_exp : N - 1 - 1 ≠ 0 := by
    omega
  rw [zero_pow h_exp]
  simp

lemma deriv_affine (a b : ℂ) (c : ℂ) : deriv (fun z => a * z + b) c = a := by
  change deriv ((fun z => a * z) + (fun z => b)) c = a
  rw [deriv_add]
  · change deriv (fun z => a * id z) c + deriv (fun z => b) c = a
    rw [deriv_const_mul a differentiableAt_id]
    rw [deriv_id]
    simp
  · apply DifferentiableAt.const_mul
    exact differentiableAt_id
  · exact differentiableAt_const b

/--
Lemma: The default quadratic map z^2 is not Fast Renormalizable.
This is because Fast Renormalization requires period p >= 2,
which implies the degree of the renormalized map would be 2^p >= 4,
contradicting the degree 2 requirement of BMol.
-/
lemma defaultBMol_not_renormalizable : ¬ IsFastRenormalizable defaultBMol := by
  intro h
  obtain ⟨g', ⟨rel⟩⟩ := h
  let p := rel.p
  have hp : p ≥ 2 := rel.p_pos
  let ψ := rel.ψ
  obtain ⟨a, b, ha, hψ⟩ := rel.rescaling_affine
  
  let c := criticalPoint g'
  have hc : c ∈ g'.U := (Classical.choose_spec g'.unique_critical_point).1.1
  have hc_crit : deriv g'.f c = 0 := (Classical.choose_spec g'.unique_critical_point).1.2
  have h_simple : deriv (deriv g'.f) c ≠ 0 := g'.simple_critical_point c hc hc_crit

  let N := 2^p
  -- 2^p >= 2^2 = 4
  have hN : N ≥ 4 := by
    calc
      N = 2^p := rfl
      _ ≥ 2^2 := Nat.pow_le_pow_right (by norm_num) hp
      _ = 4 := by norm_num

  have h_iter : ∀ z, defaultBMol.f^[p] z = z^N := by
    intro z
    dsimp [defaultBMol]
    apply iterate_sq_eq_pow_two_pow

  let LHS := fun z => ψ (g'.f z)
  let RHS := fun z => (ψ z)^N

  have h_eq : ∀ z ∈ g'.U, LHS z = RHS z := by
    intro z hz
    dsimp [LHS, RHS]
    change rel.ψ (g'.f z) = _
    rw [rel.eq_f z hz]
    rw [h_iter (ψ z)]

  -- Useful differentiability facts
  have h_diff_f : DifferentiableOn ℂ g'.f g'.U := g'.differentiable_on
  have h_diff_f_at_c : DifferentiableAt ℂ g'.f c := h_diff_f.differentiableAt (g'.isOpen_U.mem_nhds hc)
  have h_diff_ψ : Differentiable ℂ ψ := by
    have : ψ = fun z => a * z + b := funext hψ
    rw [this]
    exact (differentiable_id.const_mul a).add_const b
  have h_diff_ψ_at : ∀ z, DifferentiableAt ℂ ψ z := fun z => h_diff_ψ z
  
  -- LHS' c
  have h_LHS_deriv : deriv LHS c = 0 := 
    h_LHS_deriv_aux g'.f ψ c h_diff_f_at_c (h_diff_ψ_at (g'.f c)) hc_crit

  -- RHS' c
  have h_deriv_ψ : deriv ψ c = a := by
    have : ψ = fun z => a * z + b := funext hψ
    rw [this]
    exact deriv_affine a b c

  have h_RHS_deriv : deriv RHS c = N * (ψ c)^(N-1) * a :=
    h_RHS_deriv_aux N ψ c a (h_diff_ψ_at c) h_deriv_ψ

  have h_ψ_c : ψ c = 0 := by
    have h_local_eq : LHS =ᶠ[𝓝 c] RHS := by
      apply Filter.eventually_iff_exists_mem.mpr
      use g'.U
      exact ⟨g'.isOpen_U.mem_nhds hc, h_eq⟩
    have h_deriv_eq : deriv LHS c = deriv RHS c := Filter.EventuallyEq.deriv_eq h_local_eq
    rw [h_LHS_deriv, h_RHS_deriv] at h_deriv_eq
    rw [eq_comm] at h_deriv_eq
    -- N * (ψ c) ^ (N - 1) * a = 0
    have h_prod_zero : (N : ℂ) * (ψ c) ^ (N - 1) * a = 0 := h_deriv_eq
    rw [mul_eq_zero, mul_eq_zero] at h_prod_zero
    rcases h_prod_zero with (hN_zero | hpow_zero) | ha_zero
    · -- N != 0
      have : (N : ℂ) ≠ 0 := by
        norm_cast
        linarith
      contradiction
    · -- (ψ c) ^ (N - 1) = 0 implies ψ c = 0
      apply eq_zero_of_pow_eq_zero hpow_zero
    · -- a != 0
      contradiction

  have h_deriv_ψ_all : ∀ z, deriv ψ z = a := by
    intro z
    have : ψ = fun w => a * w + b := funext hψ
    rw [this]
    exact deriv_affine a b z

  -- Second derivative of LHS at c
  have h_diff_deriv_f : DifferentiableAt ℂ (deriv g'.f) c := by
      by_contra h
      have h_zero : deriv (deriv g'.f) c = 0 := deriv_zero_of_not_differentiableAt h
      contradiction

  have h_LHS_deriv2 : deriv (deriv LHS) c = a * deriv (deriv g'.f) c :=
    h_LHS_deriv2_aux g'.f ψ c a g'.U hc g'.isOpen_U g'.differentiable_on h_diff_ψ h_diff_deriv_f h_deriv_ψ_all

  -- Second derivative of RHS at c
  have h_RHS_deriv2 : deriv (deriv RHS) c = 0 :=
    h_RHS_deriv2_aux N ψ c a hN h_diff_ψ h_deriv_ψ_all h_ψ_c

  have h_contra : a * deriv (deriv g'.f) c = 0 := by
    have h_deriv2_eq : deriv (deriv LHS) c = deriv (deriv RHS) c := by
       -- deriv LHS = deriv RHS locally
       have h_d1_eq : ∀ᶠ z in 𝓝 c, deriv LHS z = deriv RHS z := by
          apply Filter.eventually_iff_exists_mem.mpr
          use g'.U
          constructor
          · exact g'.isOpen_U.mem_nhds hc
          · intro z hz
            apply Filter.EventuallyEq.deriv_eq
            apply Filter.eventually_iff_exists_mem.mpr
            use g'.U
            exact ⟨g'.isOpen_U.mem_nhds hz, h_eq⟩
       exact Filter.EventuallyEq.deriv_eq h_d1_eq
    rw [h_LHS_deriv2, h_RHS_deriv2] at h_deriv2_eq
    exact h_deriv2_eq

  rcases mul_eq_zero.mp h_contra with ha_zero | h_deriv_zero
  · exact ha ha_zero
  · exact h_simple h_deriv_zero

/--
Theorem: Existence of a Renormalization Fixed Point.
We prove that defaultBMol is a fixed point of Rfast because it is not renormalizable.
-/
theorem fixed_point_exists : ∃ f : BMol, Rfast f = f ∧ criticalValue f = 0 := by
  use defaultBMol
  constructor
  · -- Prove Rfast defaultBMol = defaultBMol
    rw [Rfast]
    simp [defaultBMol_not_renormalizable]
  · -- Prove criticalValue defaultBMol = 0
    -- The critical point is 0
    have h_cp : criticalPoint defaultBMol = 0 := by
      rw [criticalPoint]
      -- unique_critical_point of defaultBMol
      have u := defaultBMol.unique_critical_point
      -- We know 0 satisfies it
      have h0 : 0 ∈ defaultBMol.U ∧ deriv defaultBMol.f 0 = 0 := by
        constructor
        · apply Metric.mem_ball.mpr
          norm_num
        · dsimp [defaultBMol]
          rw [deriv_pow_field 2]
          simp
      -- Uniqueness implies Classical.choose = 0
      exact Eq.symm ((Classical.choose_spec u).2 0 h0)
    
    rw [criticalValue, h_cp]
    dsimp [defaultBMol]
    simp

end MLC
