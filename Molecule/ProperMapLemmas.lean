import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Card

namespace MLC

open Complex Topology Set Filter

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
    simp only [inc, mem_preimage]
    constructor
    · rintro ⟨h, hc⟩
      convert hc
    · intro hc
      exact ⟨_, hc⟩
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
    have : z ∈ f ⁻¹' D_target := connectedComponentIn_subset (f ⁻¹' D_target) 0 hz
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
Helper lemma: The power map is an open map.
-/
lemma pow_isOpenMap {deg : ℕ} (h_deg : 0 < deg) {f : ℂ → ℂ} (hf : f = fun z => z^deg) :
    IsOpenMap f := by
  rw [hf]
  let p := fun z : ℂ => z^deg
  have h_anal : AnalyticOnNhd ℂ p univ := by
    intro z _
    have h_id : AnalyticAt ℂ (fun w => w) z := analyticAt_id
    exact h_id.pow deg
  rcases h_anal.is_constant_or_isOpen isPreconnected_univ with ⟨w, hw⟩ | h_open
  · exfalso
    have h0 : p 0 = w := hw 0 (mem_univ _)
    have h1 : p 1 = w := hw 1 (mem_univ _)
    dsimp [p] at h0 h1
    rw [zero_pow (Nat.pos_iff_ne_zero.mp h_deg)] at h0
    rw [one_pow] at h1
    rw [← h0] at h1
    exact one_ne_zero h1
  · intro U hU
    exact h_open U (subset_univ _) hU

/--
Helper lemma: The image of the connected component is a subset of the target.
-/
lemma pow_image_subset_target {f : ℂ → ℂ} {D_target : Set ℂ}
    (C : Set ℂ) (hC : C = connectedComponentIn (f ⁻¹' D_target) 0) :
    f '' C ⊆ D_target := by
  rw [hC]
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact (connectedComponentIn_subset (f ⁻¹' D_target) 0 hx)

lemma isClosedEmbedding_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t)
    (h_closed : IsClosed {x : t | x.val ∈ s}) : IsClosedEmbedding (Set.inclusion h) := by
  constructor
  · constructor
    · rw [← IsInducing.of_comp_iff (g := (Subtype.val : t → X)) ⟨rfl⟩]
      exact ⟨rfl⟩
    · exact Set.inclusion_injective h
  · rw [Set.range_inclusion h]
    exact h_closed

/--
Helper lemma: The image of the connected component is closed in the target.
-/
lemma pow_image_closed_in_target
    {D_target : Set ℂ} {D0 : Set ℂ} {f : ℂ → ℂ}
    (h_maps : MapsTo f D0 D_target)
    (h_proper : IsProperMap (MapsTo.restrict f D0 D_target h_maps))
    (h_clopen : IsClopen {x : f ⁻¹' D_target | x.val ∈ D0})
    (h0_in_pre : 0 ∈ f ⁻¹' D_target)
    (h_0_in_D0 : 0 ∈ D0)
    (C : Set ℂ) (hC : C = connectedComponentIn (f ⁻¹' D_target) 0) :
    IsClosed (Subtype.val ⁻¹' (f '' C) : Set D_target) := by
  let D_pre := f ⁻¹' D_target
  let C_subtype := {x : ℂ | x ∈ C}
  have hfC_sub : f '' C ⊆ D_target := pow_image_subset_target C hC
  have h_maps_C : MapsTo f C_subtype D_target := fun x hx => hfC_sub ⟨x, hx, rfl⟩
  let f_C := MapsTo.restrict f C_subtype D_target h_maps_C

  have h_f_C_proper : IsProperMap f_C := by
    have hD0_sub_pre : D0 ⊆ D_pre := h_maps
    have hC_sub_D0 : C ⊆ D0 := by
      intro x hx
      -- Need to show x ∈ D0.
      let U := {z : D_pre | z.val ∈ D0}
      have hU_clopen : IsClopen U := h_clopen
      have h0_U : (⟨0, h0_in_pre⟩ : D_pre) ∈ U := h_0_in_D0
      have h_comp_sub : connectedComponent (⟨0, h0_in_pre⟩ : D_pre) ⊆ U :=
        hU_clopen.connectedComponent_subset h0_U

      -- x ∈ C means x ∈ D_pre and ⟨x, _⟩ ∈ connectedComponent ...
      have hx_pre : x ∈ D_pre := connectedComponentIn_subset (f ⁻¹' D_target) 0 (by rw [←hC]; exact hx)
      have hx_comp : (⟨x, hx_pre⟩ : D_pre) ∈ connectedComponent (⟨0, h0_in_pre⟩ : D_pre) := by
        rw [hC] at hx
        simp [connectedComponentIn] at hx
        rw [dif_pos h0_in_pre] at hx
        rcases hx with ⟨y, hy, rfl⟩
        exact hy

      have hx_U := h_comp_sub hx_comp
      exact hx_U

    have hC_closed_in_D0 : IsClosed {x : D0 | x.val ∈ C} := by
      let inc : D0 → D_pre := fun x => ⟨x.val, hD0_sub_pre x.property⟩
      have h_inc_cont : Continuous inc := continuous_subtype_val.subtype_mk _
      have hC_closed_in_pre : IsClosed (connectedComponent (⟨0, h0_in_pre⟩ : D_pre)) := isClosed_connectedComponent
      have : {x : D0 | x.val ∈ C} = inc ⁻¹' (connectedComponent (⟨0, h0_in_pre⟩ : D_pre)) := by
        ext x
        simp only [hC, connectedComponentIn, dif_pos h0_in_pre, mem_setOf_eq, mem_preimage, mem_image,
          Subtype.exists, exists_and_right, exists_eq_right]
        constructor
        · rintro ⟨h, hc⟩
          have : h = hD0_sub_pre x.property := rfl
          subst this
          exact hc
        · intro hc
          exact ⟨hD0_sub_pre x.property, hc⟩
      rw [this]
      apply IsClosed.preimage h_inc_cont hC_closed_in_pre

    let f_res := MapsTo.restrict f D0 D_target h_maps
    let inc_C : C_subtype → D0 := Set.inclusion hC_sub_D0
    have h_inc_C : IsClosedEmbedding inc_C :=
      isClosedEmbedding_inclusion hC_sub_D0 hC_closed_in_D0
    have h_comp : f_C = f_res ∘ inc_C := by ext ⟨x, hx⟩; rfl
    rw [h_comp]
    apply IsProperMap.comp h_proper h_inc_C.isProperMap

  have h_closed_map := h_f_C_proper.isClosedMap
  have h_univ_closed : IsClosed (univ : Set C_subtype) := isClosed_univ
  have h_img_eq : f_C '' univ = Subtype.val ⁻¹' (f '' C) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, -, hy⟩
      refine ⟨x, hx, ?_⟩
      rw [← hy]; rfl
    · rintro ⟨x, hx, hy⟩
      refine ⟨⟨x, hx⟩, mem_univ _, ?_⟩
      apply Subtype.ext
      exact hy
  rw [← h_img_eq]
  apply h_closed_map univ h_univ_closed

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
  let D_pre := f ⁻¹' D_target
  let C := connectedComponentIn D_pre 0
  have h_f_cont : Continuous f := by rw [hf]; exact continuous_pow deg
  have h_pre_open : IsOpen D_pre := h_target_open.preimage h_f_cont

  -- 1. C is open in ℂ
  have hC_open : IsOpen C := h_pre_open.connectedComponentIn

  -- 2. f is an open map
  have hf_open : IsOpenMap f := pow_isOpenMap h_deg hf

  -- 3. f(C) is open in D_target
  have hfC_open : IsOpen (f '' C) := hf_open C hC_open

  -- 4. f(C) is closed in D_target
  have hfC_closed_in_target : IsClosed (Subtype.val ⁻¹' (f '' C) : Set D_target) :=
    pow_image_closed_in_target h_maps h_proper h_clopen h0_in_pre h_0_in_D0 C rfl

  -- 5. f(C) = D_target
  have hfC_open_in_target : IsOpen (Subtype.val ⁻¹' (f '' C) : Set D_target) := by
    rw [isOpen_induced_iff]
    exact ⟨f '' C, hfC_open, rfl⟩

  have hfC_clopen : IsClopen (Subtype.val ⁻¹' (f '' C) : Set D_target) := ⟨hfC_closed_in_target, hfC_open_in_target⟩

  have hfC_nonempty : (Subtype.val ⁻¹' (f '' C) : Set D_target).Nonempty := by
    use ⟨f 0, h_maps h_0_in_D0⟩
    simp only [mem_preimage, mem_image]
    use 0
    exact ⟨mem_connectedComponentIn h0_in_pre, rfl⟩

  have hfC_univ : Subtype.val ⁻¹' (f '' C) = univ :=
    isClopen_iff.mp hfC_clopen |>.resolve_left hfC_nonempty.ne_empty

  have hfC_eq_target : f '' C = D_target := by
    have hfC_univ_pre : Subtype.val '' (Subtype.val ⁻¹' (f '' C)) = D_target ∩ f '' C :=
      Subtype.image_preimage_coe D_target (f '' C)
    rw [inter_comm] at hfC_univ_pre
    rw [hfC_univ, image_univ, Subtype.range_coe] at hfC_univ_pre
    rw [inter_eq_left.mpr (pow_image_subset_target C rfl)] at hfC_univ_pre
    exact hfC_univ_pre.symm

  -- 6. C = D_pre
  apply subset_antisymm
  · exact connectedComponentIn_subset _ _
  · intro z hz
    rw [mem_preimage] at hz
    have : f z ∈ f '' C := by rw [hfC_eq_target]; exact hz
    rcases this with ⟨x, hx, hfx_eq_fz⟩
    rw [hf] at hfx_eq_fz; dsimp at hfx_eq_fz
    have h_ex_zeta : ∃ ζ : ℂ, ζ^deg = 1 ∧ z = ζ * x := by
      by_cases hx0 : x = 0
      · subst hx0; rw [zero_pow (Nat.pos_iff_ne_zero.mp h_deg)] at hfx_eq_fz
        have : z = 0 := eq_zero_of_pow_eq_zero hfx_eq_fz.symm
        refine ⟨1, ?_⟩
        simp [h_deg, this]
      · refine ⟨z / x, ?_⟩
        constructor
        · rw [div_pow, hfx_eq_fz]
          rw [← hfx_eq_fz]
          rw [div_self (pow_ne_zero deg hx0)]
        · exact (div_mul_cancel₀ z hx0).symm
    rcases h_ex_zeta with ⟨ζ, hζ, rfl⟩
    apply component_invariant_under_rotation h_deg hf h_maps h_0_in_D0 C rfl ζ hζ
    refine ⟨x, hx, rfl⟩

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
    (y0 : ℂ) (_ : y0 ∈ D_target)
    (h_cont : Continuous f)
    (h_D0_open : IsOpen D0) (h_D_target_open : IsOpen D_target) :
    IsProperMap (MapsTo.restrict f (D0 ∩ f ⁻¹' connectedComponentIn D_target y0) (connectedComponentIn D_target y0) (fun _ hx => hx.2)) := by
  let V := connectedComponentIn D_target y0
  let U := D0 ∩ f ⁻¹' V
  have hV_open : IsOpen V := h_D_target_open.connectedComponentIn
  have hU_open : IsOpen U := h_D0_open.inter (hV_open.preimage h_cont)

  haveI : LocallyCompactSpace V := hV_open.locallyCompactSpace
  haveI : LocallyCompactSpace U := hU_open.locallyCompactSpace

  let i : V → D_target := fun x => ⟨x.val, connectedComponentIn_subset D_target y0 x.2⟩
  have hi_cont : Continuous i := Continuous.subtype_mk continuous_subtype_val _

  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · exact h_cont.continuousOn.mapsToRestrict _
  · intro K hK
    let K_in_target : Set D_target := i '' K
    have hK_target : IsCompact K_in_target := hK.image hi_cont
    let L_D0 := (MapsTo.restrict f D0 D_target h_maps) ⁻¹' K_in_target
    have hL_D0_compact : IsCompact L_D0 := h_proper.isCompact_preimage hK_target

    let pre_U := (MapsTo.restrict f U V (fun x hx => hx.2)) ⁻¹' K
    have h_eq_image : (Subtype.val : U → ℂ) '' pre_U = (Subtype.val : D0 → ℂ) '' L_D0 := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨u.val, u.2.1⟩, ?_, rfl⟩
        use (MapsTo.restrict f U V (fun x hx => hx.2) u)
        constructor
        · exact hu
        · ext
          rfl
      · rintro ⟨d, hd, rfl⟩
        rcases hd with ⟨k, hk, hik⟩
        have h_val : k.val = f d.val := by
          rw [Subtype.ext_iff] at hik
          exact hik
        have hz_U : d.val ∈ U := ⟨d.2, by
          show f d.val ∈ V
          rw [← h_val]
          exact k.2⟩
        refine ⟨⟨d.val, hz_U⟩, ?_, rfl⟩
        have h_eq : (MapsTo.restrict f U V (fun x hx => hx.2) ⟨d.val, hz_U⟩) = k := by
          apply Subtype.ext
          show f d.val = k.val
          rw [h_val]
        show (MapsTo.restrict f U V (fun x hx => hx.2) ⟨d.val, hz_U⟩) ∈ K
        rw [h_eq]
        exact hk

    rw [IsEmbedding.subtypeVal.isCompact_iff]
    rw [h_eq_image]
    exact hL_D0_compact.image continuous_subtype_val

end MLC
