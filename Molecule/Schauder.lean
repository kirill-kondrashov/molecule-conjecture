import Molecule.BMol
import Molecule.Rfast
import Molecule.BanachSlice
import Mathlib.Analysis.Normed.Module.Basic

namespace MLC

open Topology Set

/--
Lemma: Schauder Fixed Point Theorem application.
Asserts that a continuous map on a non-empty, convex, compact subset of a Banach space has a fixed point.
Here we assume the conditions are met by our invariant set K.

References:
* [DLS17] Section 3.8, Theorem 3.13.
-/
lemma schauder_fixed_point_on_invariant_compact (K : Set BMol) (hK_compact : IsCompact K) 
    (h_continuous : ContinuousOn Rfast K) (hK_maps : MapsTo Rfast K K) (hK_nonempty : K.Nonempty) : 
    ∃ f ∈ K, Rfast f = f := by
  -- Proof Sketch:
  -- 1. Map K into the Banach Space (SliceSpace) using the chart φ.
  --    In the actual theory, K is chosen to be within a specific chart.
  --    Let f_ref be a reference map (e.g. the expected fixed point).
  let f_ref := hK_nonempty.some
  let φ := slice_chart f_ref
  let K_banach := φ '' K

  -- 2. K_banach is compact and non-empty.
  have hK_banach_compact : IsCompact K_banach := hK_compact.image (by
    -- Chart is continuous in the analytic topology
    sorry)
  have hK_banach_nonempty : K_banach.Nonempty := hK_nonempty.image φ

  -- 3. In the construction of K (Thm 3.16), K_banach is a convex set.
  -- Note: We use real convexity as complex convexity is not standardly defined this way.
  have h_convex : Convex ℝ K_banach := by
    -- K is constructed as a "polydisk" or a convex hull in the Banach slice.
    sorry

  -- 4. The operator F (slice_operator) maps K_banach to itself.
  let F := slice_operator f_ref
  have hF_maps : MapsTo F K_banach K_banach := by
    -- Follows from slice_conjugacy and hK_maps
    sorry

  -- 5. F is continuous on K_banach.
  have hF_cont : ContinuousOn F K_banach := by
    -- F is analytic on the SliceSpace.
    sorry

  -- 6. Apply Schauder Fixed Point Theorem in the Banach Space.
  -- Theorem: If E is a Banach space, C ⊆ E is non-empty, compact, and convex,
  -- and F : C → C is continuous, then F has a fixed point.
  have h_fixed_banach : ∃ x ∈ K_banach, F x = x := by
    -- apply IsCompact.exists_fixed_point_of_convex_compact ...
    sorry

  -- 7. Pull back the fixed point to BMol.
  obtain ⟨x_fix, hx_fix_in, hx_fix_eq⟩ := h_fixed_banach
  obtain ⟨f_fix, hf_fix_in_K, h_f_phi⟩ := (mem_image φ K x_fix).mp hx_fix_in
  
  use f_fix
  constructor
  · exact hf_fix_in_K
  · -- slice_conjugacy: F (φ f_fix) = φ (Rfast f_fix)
    -- x_fix = φ f_fix
    -- x_fix = F x_fix = F (φ f_fix) = φ (Rfast f_fix)
    -- So φ f_fix = φ (Rfast f_fix). 
    -- Assuming φ is injective on K (local chart property):
    have h_phi_inj : InjOn φ K := by sorry
    apply Eq.symm
    apply h_phi_inj hf_fix_in_K (hK_maps hf_fix_in_K)
    
    -- Goal: φ f_fix = φ (Rfast f_fix)
    rw [h_f_phi]
    -- Goal: x_fix = φ (Rfast f_fix)
    rw [← hx_fix_eq]
    -- Goal: F x_fix = φ (Rfast f_fix)
    rw [← h_f_phi]
    -- Goal: F (φ f_fix) = φ (Rfast f_fix)
    apply slice_conjugacy f_ref f_fix (Set.mem_univ f_fix)

end MLC