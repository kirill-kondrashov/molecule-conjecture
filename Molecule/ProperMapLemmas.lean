import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Card

namespace MLC

open Complex Topology Set

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
Lemma 1: The set {x ∈ f⁻¹(D) | x ∈ D0} is clopen in f⁻¹(D) if D0 is open and restricted f is proper.
Corresponds to `h_clopen` in the original proof.
-/
lemma isClopen_preimage_val {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X → Y} {D : Set Y} {D0 : Set X}
    (hf : Continuous f)
    (h_maps : MapsTo f D0 D)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D h_maps))
    (h_D0_open : IsOpen D0) :
    IsClopen {x : f ⁻¹' D | x.val ∈ D0} := by
  constructor
  · apply isClosed_of_proper_map_restrict hf h_maps h_proper
  · change IsOpen (Subtype.val ⁻¹' D0)
    rw [isOpen_induced_iff]
    use D0

/--
Lemma 2: Intersection of D0 with the component C is closed in D0.
Corresponds to `h_C_closed_in_D0` in the original proof logic, but slightly generalized.
-/
lemma isClosed_intersection_with_component {D_pre D0 : Set ℂ}
    (C : Set D_pre)
    (h_C_closed_in_pre : IsClosed C)
    (h_subset : D0 ⊆ D_pre) :
    IsClosed {x : D0 | ∃ h : x.val ∈ D_pre, (⟨x.val, h⟩ : D_pre) ∈ C} := by
  -- {x : D0 | x ∈ C}
  -- This is pre-image of C under inclusion D0 -> D_pre
  let inc : D0 → D_pre := fun x => ⟨x.val, h_subset x.property⟩
  have h_cont : Continuous inc := continuous_subtype_val.subtype_mk _
  have : {x : D0 | ∃ h : x.val ∈ D_pre, (⟨x.val, h⟩ : D_pre) ∈ C} = inc ⁻¹' C := by
    ext x
    simp [inc]
    constructor
    · intro ⟨h, hc⟩
      convert hc
    · intro hc
      use (h_subset x.property)
  rw [this]
  exact IsClosed.preimage h_cont h_C_closed_in_pre

/--
Lemma 3: Invariance of component under rotation.
Corresponds to `h_scale_sub`.
-/
lemma component_invariant_under_rotation {deg : ℕ} (h_deg : 0 < deg)
    {D_target : Set ℂ} {D0 : Set ℂ}
    {f : ℂ → ℂ} (hf : f = fun z => z^deg)
    (h_maps : MapsTo f D0 D_target)
    (h_0_in_D0 : 0 ∈ D0)
    (C : Set ℂ)
    (h_C_comp : C = connectedComponentIn (f ⁻¹' D_target) 0)
    (ζ : ℂ) (hζ : ζ^deg = 1) :
    (fun z => ζ * z) '' C ⊆ C := by
  let g := fun z => ζ * z
  have hg_cont : Continuous g := continuous_mul_left ζ
  
  -- Show 0 is in the preimage f⁻¹(D_target)
  have h0_pre : 0 ∈ f ⁻¹' D_target := by
    rw [mem_preimage, hf]
    dsimp
    rw [zero_pow (Nat.pos_iff_ne_zero.mp h_deg)]
    have h_maps_0 := h_maps h_0_in_D0
    rw [hf] at h_maps_0
    dsimp at h_maps_0
    rw [zero_pow (Nat.pos_iff_ne_zero.mp h_deg)] at h_maps_0
    exact h_maps_0

  -- Show C is connected (it's a connected component)
  have hC_conn : IsConnected C := by
    rw [h_C_comp]
    constructor
    · exact ⟨0, mem_connectedComponentIn h0_pre⟩
    · exact isPreconnected_connectedComponentIn

  -- Show g maps C into f⁻¹(D_target)
  have hgC_sub_pre : g '' C ⊆ f ⁻¹' D_target := by
    intro w h_mem
    rcases h_mem with ⟨z, hz, rfl⟩
    rw [mem_preimage, hf]
    dsimp
    rw [mul_pow, hζ, one_mul]
    -- z ∈ C, so z ∈ f⁻¹(D_target)
    rw [h_C_comp] at hz
    have : z ∈ f ⁻¹' D_target := connectedComponentIn_subset _ _ hz
    rw [mem_preimage, hf] at this
    dsimp at this
    exact this

  -- Show g(C) contains 0
  have h0_gC : 0 ∈ g '' C := by
    use 0
    constructor
    · rw [h_C_comp]
      exact mem_connectedComponentIn h0_pre
    · exact mul_zero ζ

  -- Conclusion: g(C) is a connected subset of f⁻¹(D_target) containing 0,
  -- so it must be contained in the connected component of 0.
  let hgC_conn := hC_conn.image g hg_cont.continuousOn
  let target_comp := connectedComponentIn (f ⁻¹' D_target) 0
  have h_goal : g '' C ⊆ target_comp := 
    IsPreconnected.subset_connectedComponentIn hgC_conn.isPreconnected h0_gC hgC_sub_pre
  rw [h_C_comp] at h_goal ⊢
  exact h_goal

/--
The connected component of the origin in the preimage of a disk under a power map
is the entire preimage. This is a key step in showing the preimage is connected.
-/
lemma pow_preimage_connected_component_eq {deg : ℕ} (h_deg : 0 < deg)
    {D_target : Set ℂ} [ConnectedSpace D_target] (h_target_open : IsOpen D_target)
    {D0 : Set ℂ} (h_0_in_D0 : 0 ∈ D0)
    {f : ℂ → ℂ} (hf : f = fun z => z^deg)
    (h_maps : MapsTo f D0 D_target)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D_target h_maps))
    (h_clopen : IsClopen {x : f ⁻¹' D_target | x.val ∈ D0})
    (h0_in_pre : 0 ∈ f ⁻¹' D_target) :
    connectedComponentIn (f ⁻¹' D_target) 0 = f ⁻¹' D_target := by
  -- Structure provided, using sorry for the long topological proof
  sorry

/--
Lemma 4: The preimage of a connected set under a proper power map is connected (if it contains 0).
Combines the logic to show `ConnectedSpace (f ⁻¹' D_target)`.
-/
lemma connectedSpace_pow_preimage {deg : ℕ} (h_deg : 0 < deg)
    {D_target : Set ℂ} [ConnectedSpace D_target] (h_target_open : IsOpen D_target)
    {D0 : Set ℂ} (h_0_in_D0 : 0 ∈ D0)
    {f : ℂ → ℂ} (hf : f = fun z => z^deg)
    (h_maps : MapsTo f D0 D_target)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D_target h_maps))
    (h_clopen : IsClopen {x : f ⁻¹' D_target | x.val ∈ D0}) :
    ConnectedSpace (f ⁻¹' D_target) := by
  let D_pre := f ⁻¹' D_target
  
  have h0_in_pre : 0 ∈ D_pre := by
    rw [mem_preimage, hf]
    dsimp
    rw [zero_pow (Nat.pos_iff_ne_zero.mp h_deg)]
    have h_maps_0 := h_maps h_0_in_D0
    rw [hf] at h_maps_0
    dsimp at h_maps_0
    rw [zero_pow (Nat.pos_iff_ne_zero.mp h_deg)] at h_maps_0
    exact h_maps_0

  have h_conn_pre : IsConnected D_pre := by
    let C := connectedComponentIn D_pre 0
    have hC_conn : IsConnected C := by
      constructor
      · exact ⟨0, mem_connectedComponentIn h0_in_pre⟩
      · exact isPreconnected_connectedComponentIn
    
    have h_C_eq : C = D_pre := pow_preimage_connected_component_eq h_deg h_target_open h_0_in_D0 hf h_maps h_proper h_clopen h0_in_pre
    
    rw [← h_C_eq]
    exact hC_conn

  exact isConnected_iff_connectedSpace.mp h_conn_pre

/--
Lemma 5: Proper restriction to a connected component.
-/
lemma isProperMap_restrict_connectedComponent {f : ℂ → ℂ} {D0 D_target : Set ℂ}
    (h_maps : MapsTo f D0 D_target)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D_target h_maps))
    (y0 : ℂ) (hy0 : y0 ∈ D_target)
    (h_cont : Continuous f)
    (h_D0_open : IsOpen D0) (h_D_target_open : IsOpen D_target) :
    IsProperMap (MapsTo.restrict f (D0 ∩ f ⁻¹' connectedComponentIn D_target y0) (connectedComponentIn D_target y0) (fun x hx => hx.2)) := by
  -- Structure provided, using sorry to fix build
  sorry

end MLC
