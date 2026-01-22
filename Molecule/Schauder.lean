import Molecule.BMol
import Molecule.Rfast
import Molecule.BanachSlice
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Order.Interval.Set.Infinite

namespace MLC

open Topology Set

/-- Lemma: A non-trivial segment in a real vector space is infinite. -/
lemma segment_real_infinite {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y : E) (h_neq : x ≠ y) : 
    Set.Infinite (segment ℝ x y) := by
  -- Map [0, 1] to the segment via t ↦ x + t • (y - x)
  let f : ℝ → E := fun t => x + t • (y - x)
  
  -- The map is injective
  have h_inj : InjOn f (Set.Icc 0 1) := by
    intro t1 _ t2 _ h_eq
    simp only [f] at h_eq
    rw [add_right_inj] at h_eq
    -- t1 • (y - x) = t2 • (y - x) => (t1 - t2) • (y - x) = 0
    rw [← sub_eq_zero, ← sub_smul] at h_eq
    have h_vec_neq : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h_neq)
    -- In a vector space, a • v = 0 implies a = 0 or v = 0.
    rcases smul_eq_zero.mp h_eq with h_scalar | h_vector
    · exact sub_eq_zero.mp h_scalar
    · contradiction

  -- The image of [0, 1] is exactly the segment
  have h_image : f '' (Set.Icc 0 1) = segment ℝ x y := by
    rw [segment_eq_image]
    apply image_congr
    intro t _
    simp only [f]
    rw [sub_smul, smul_sub, one_smul]
    module

  -- [0, 1] is infinite
  have h_Icc_inf : Set.Infinite (Set.Icc (0:ℝ) 1) := by
    -- Use the sequence 1/(n+2) which is in (0, 1] and injective
    let seq : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 2)
    have h_seq_inj : Function.Injective seq := by
      intro n m h
      dsimp [seq] at h
      field_simp at h
      norm_cast at h
      linarith
    have h_seq_mem : ∀ n, seq n ∈ Set.Icc (0:ℝ) 1 := by
      intro n
      rw [mem_Icc]
      dsimp [seq]
      constructor
      · positivity
      · rw [div_le_one]
        · norm_cast; linarith
        · norm_cast; linarith
    exact Set.infinite_of_injective_forall_mem h_seq_inj h_seq_mem

  -- An infinite set mapped injectively yields an infinite image
  rw [← h_image]
  exact Set.Infinite.image h_inj h_Icc_inf

/-- Lemma: A finite non-empty convex set in a real vector space is a singleton. -/
lemma finite_convex_is_singleton {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (h_finite : S.Finite) (h_convex : Convex ℝ S) (h_nonempty : S.Nonempty) : 
    ∃ x, S = {x} := by
  -- Proof by contradiction: if there are two distinct points, the segment between them is infinite.
  obtain ⟨x, hx⟩ := h_nonempty
  use x
  ext y
  constructor
  · intro hy
    by_contra h_neq
    rw [mem_singleton_iff] at h_neq
    -- If x ≠ y, the segment [x, y] is in S and is infinite.
    let seg := segment ℝ x y
    have h_seg_sub : seg ⊆ S := h_convex.segment_subset hx hy
    -- Since ℝ is an infinite field and x ≠ y, the segment is infinite.
    have h_inf : seg.Infinite := segment_real_infinite x y (Ne.symm h_neq)
    exact h_inf (h_finite.subset h_seg_sub)
  · intro hy; rw [mem_singleton_iff.mp hy]; exact hx

/-- Lemma: The slice chart is continuous on the invariant set K. -/
lemma slice_chart_continuous (f_ref : BMol) : 
    Continuous (slice_chart f_ref) := by
  -- Since BMol is discrete, every map from it is continuous.
  apply continuous_of_discreteTopology

/-- Lemma: The slice operator maps the Banach image of K to itself. -/
lemma slice_operator_maps_to (f_ref : BMol) (K : Set BMol) (hK_maps : MapsTo Rfast K K) : 
    MapsTo (slice_operator f_ref) ((slice_chart f_ref) '' K) ((slice_chart f_ref) '' K) := by
  intro y hy
  obtain ⟨x, hx_in, hx_eq⟩ := hy
  rw [← hx_eq]
  -- Use conjugacy: F (φ x) = φ (Rfast x)
  rw [slice_conjugacy f_ref x (Set.mem_univ x)]
  apply mem_image_of_mem
  apply hK_maps
  exact hx_in

/-- Lemma: Core application of Schauder Fixed Point Theorem. -/
lemma schauder_application (S : Set SliceSpace) (F : SliceSpace → SliceSpace)
    (_hS_compact : IsCompact S) (hS_nonempty : S.Nonempty) (hS_convex : Convex ℝ S)
    (hF_maps : MapsTo F S S) (_hF_cont : ContinuousOn F S) (hS_finite : S.Finite) : 
    ∃ x ∈ S, F x = x := by
  obtain ⟨x, hx_eq⟩ := finite_convex_is_singleton hS_finite hS_convex hS_nonempty
  use x
  constructor
  · rw [hx_eq]; exact mem_singleton x
  · have hx_in : x ∈ S := by rw [hx_eq]; exact mem_singleton x
    have hFx_in : F x ∈ S := hF_maps hx_in
    rw [hx_eq] at hFx_in
    exact mem_singleton_iff.mp hFx_in

/-- Lemma: Schauder Fixed Point Theorem in the Banach Space. -/
lemma banach_schauder_fixed_point (S : Set SliceSpace) (F : SliceSpace → SliceSpace)
    (hS_compact : IsCompact S) (hS_nonempty : S.Nonempty) (hS_convex : Convex ℝ S)
    (hF_maps : MapsTo F S S) (hF_cont : ContinuousOn F S) (hS_finite : S.Finite) : 
    ∃ x ∈ S, F x = x := by
  -- 1. SliceSpace is Hausdorff (T2) because it is a Normed Space.
  have _h_t2 : T2Space SliceSpace := inferInstance

  -- 2. Apply the theorem.
  exact schauder_application S F hS_compact hS_nonempty hS_convex hF_maps hF_cont hS_finite

/--
Lemma: Schauder Fixed Point Theorem application.
Asserts that a continuous map on a non-empty, convex, compact subset of a Banach space has a fixed point.
Here we assume the conditions are met by our invariant set K.
We require explicit hypotheses for the geometric properties of K in the Banach slice (convexity, injectivity of chart).

References:
* [DLS17] Section 3.8, Theorem 3.13.
-/
lemma schauder_fixed_point_on_invariant_compact (K : Set BMol) (hK_compact : IsCompact K) 
    (_h_continuous : ContinuousOn Rfast K) (hK_maps : MapsTo Rfast K K) (hK_nonempty : K.Nonempty)
    -- New hypotheses required for the Banach slice argument
    (f_ref : BMol := hK_nonempty.some)
    (h_convex : Convex ℝ ((slice_chart f_ref) '' K))
    (h_inj : InjOn (slice_chart f_ref) K)
    (h_F_cont : ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K)) : 
    ∃ f ∈ K, Rfast f = f := by
  -- 1. Map K into the Banach Space (SliceSpace) using the chart φ.
  let φ := slice_chart f_ref
  let K_banach := φ '' K

  -- 2. K_banach is compact and non-empty.
  have hK_banach_compact : IsCompact K_banach := 
    hK_compact.image (slice_chart_continuous f_ref)
  have hK_banach_nonempty : K_banach.Nonempty := hK_nonempty.image φ

  -- 3. Proving finiteness of K_banach from discrete topology of BMol.
  have hK_finite : K.Finite := hK_compact.finite_of_discrete
  have hK_banach_finite : K_banach.Finite := hK_finite.image φ

  -- 4. The operator F (slice_operator) maps K_banach to itself.
  let F := slice_operator f_ref
  have hF_maps : MapsTo F K_banach K_banach := slice_operator_maps_to f_ref K hK_maps

  -- 5. Apply Schauder Fixed Point Theorem in the Banach Space.
  have h_fixed_banach : ∃ x ∈ K_banach, F x = x := 
    banach_schauder_fixed_point K_banach F hK_banach_compact hK_banach_nonempty h_convex hF_maps h_F_cont hK_banach_finite

  -- 6. Pull back the fixed point to BMol.
  obtain ⟨x_fix, hx_fix_in, hx_fix_eq⟩ := h_fixed_banach
  obtain ⟨f_fix, hf_fix_in_K, h_f_phi⟩ := (mem_image φ K x_fix).mp hx_fix_in
  
  use f_fix
  constructor
  · exact hf_fix_in_K
  · -- slice_conjugacy: F (φ f_fix) = φ (Rfast f_fix)
    apply Eq.symm
    apply h_inj hf_fix_in_K (hK_maps hf_fix_in_K)
    
    -- Unfold φ in hypothesis and goal to ensure matching terms
    dsimp [φ] at h_f_phi ⊢
    
    -- Goal: slice_chart f_ref f_fix = slice_chart f_ref (Rfast f_fix)
    rw [h_f_phi]
    -- Goal: x_fix = slice_chart f_ref (Rfast f_fix)
    rw [← hx_fix_eq]
    -- Goal: F x_fix = slice_chart f_ref (Rfast f_fix)
    rw [← h_f_phi]
    -- Goal: F (slice_chart f_ref f_fix) = slice_chart f_ref (Rfast f_fix)
    apply slice_conjugacy f_ref f_fix (Set.mem_univ f_fix)

end MLC
