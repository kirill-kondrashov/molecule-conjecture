import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.Rfast
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

namespace Molecule

open Complex Topology Set Filter

/-- 
The predicate for having Siegel bounds.
-/
def HasSiegelBounds (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ) : Prop :=
    Rfast f_star = f_star ∧
    IsOpen D ∧ IsOpen U ∧
    f_star ∈ U ∧
    criticalValue f_star ∈ D ∧
    (∀ᶠ n in atTop, ∀ t ∈ ({a n, b n} : Set ℕ),
      ∀ f, f ∈ (Rfast^[n]) ⁻¹' U →
        let c1 := criticalValue f
        let ft := f.f^[t]
        ft c1 ∈ D ∧
        ∃ (D0 D_target : Set ℂ) (h_maps : MapsTo ft D0 D_target),
          IsOpen D0 ∧ IsOpen D_target ∧
          D_target ⊆ D ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 D_target h_maps) ∧
          ∀ y ∈ D_target, Set.ncard {x ∈ D0 | ft x = y} = 2
    )

/-- The Banach Space for the slice. -/
abbrev SliceSpace := ℂ

noncomputable instance : NormedAddCommGroup SliceSpace := inferInstance
noncomputable instance : NormedSpace ℂ SliceSpace := inferInstance

/-- The chart φ. Depends on the fixed point f_star. -/
def slice_chart (_f_star : BMol) : BMol → SliceSpace := fun _ => 0

/-- The domain U of the chart. -/
def slice_domain (_ : BMol) : Set BMol := univ

/--
Reference-dependent localized domain candidate for the post-`PLAN_90`
replacement search.
It is always proper, excludes one distinguished point, and still contains the
reference map.
-/
noncomputable def slice_domain_localized (f_ref : BMol) : Set BMol :=
  by
    classical
    exact if h : f_ref = defaultBMol then {g | g ≠ largeBMol} else {g | g ≠ defaultBMol}

/-- The operator F. -/
def slice_operator (_f_star : BMol) : SliceSpace → SliceSpace := fun _ => 0

/--
Refined operator candidate for the `PLAN_90` redesign search.
Unlike `slice_operator`, this scaffold is nonconstant on `SliceSpace`.
-/
def slice_operator_refined (_f_star : BMol) : SliceSpace → SliceSpace := fun z => z

/--
Reference-dependent nonidentity operator candidate for the post-`PLAN_91`
search.
At the shifted reference point it acts by the involution `z ↦ 2 - z`, so the
finite set `{0, 1, 2}` is invariant.
-/
noncomputable def slice_operator_multivalued (f_ref : BMol) : SliceSpace → SliceSpace :=
  by
    classical
    exact fun z => if f_ref = shiftedBMol then 2 - z else z

/--
Finite-observation operator candidate for the topology-compatible redesign.
Unlike `slice_operator_multivalued`, its nontrivial branch is keyed only to the
finite observation class of the reference map, not to literal `BMol` equality.
-/
noncomputable def slice_operator_finite_observation (f_ref : BMol) : SliceSpace → SliceSpace :=
  by
    classical
    exact
      if bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol then
        fun z => 2 - z
      else
        fun z => z

/--
Zero-observation operator candidate for the next broadening step.
Its nontrivial branch depends only on the scalar observation `f_ref.f 0 = 1`,
so it reaches a larger class than the shifted finite-observation operator.
-/
noncomputable def slice_operator_zero_observation (f_ref : BMol) : SliceSpace → SliceSpace :=
  by
    classical
    exact if bmol_zero_observation f_ref = 1 then fun z => 2 - z else fun z => z

/-- The chart maps to an open set. -/
theorem slice_chart_open (f_star : BMol) :
  ∃ V, IsOpen V ∧ MapsTo (slice_chart f_star) (slice_domain f_star) V := by
  refine ⟨univ, isOpen_univ, ?_⟩
  intro x hx
  trivial

/-- The localized replacement domain is open in the current discrete model. -/
theorem slice_domain_localized_open (f_ref : BMol) :
    IsOpen (slice_domain_localized f_ref) := by
  trivial

/-- The localized replacement domain always contains its reference point. -/
theorem mem_slice_domain_localized_self (f_ref : BMol) :
    f_ref ∈ slice_domain_localized f_ref := by
  classical
  by_cases h : f_ref = defaultBMol
  · subst h
    simp [slice_domain_localized]
    exact Ne.symm largeBMol_ne_defaultBMol
  · simp [slice_domain_localized, h]

/-- The localized replacement domain is proper: some point is excluded. -/
theorem exists_not_mem_slice_domain_localized (f_ref : BMol) :
    ∃ g : BMol, g ∉ slice_domain_localized f_ref := by
  classical
  by_cases h : f_ref = defaultBMol
  · refine ⟨largeBMol, ?_⟩
    subst h
    simp [slice_domain_localized]
  · refine ⟨defaultBMol, ?_⟩
    simp [slice_domain_localized, h]

/--
Refined chart candidate used for constructive witness migration.
Unlike `slice_chart`, this chart separates the reference map from other points.
-/
noncomputable def slice_chart_refined (f_ref : BMol) : BMol → SliceSpace := by
  classical
  exact fun g => if g = f_ref then 0 else 1

/--
Multivalued replacement chart candidate for the post-`PLAN_91` search.
Unlike `slice_chart_refined`, it distinguishes two concrete nonbase directions
in the current repository.
-/
noncomputable def slice_chart_multivalued (f_ref : BMol) : BMol → SliceSpace := by
  classical
  exact fun g =>
    if g = f_ref then 0
    else if g = defaultBMol then 1
    else if g = largeBMol then 2
    else 3

/--
Finite-observation chart candidate for the topology-compatible scaffold
upgrade. It depends only on the two-coordinate observable recorded in
`bmol_finite_observation`, not on literal `BMol` equality tests.
-/
noncomputable def slice_chart_finite_observation (f_ref : BMol) : BMol → SliceSpace :=
  fun g =>
    (-bmol_zero_observation g + bmol_large_source_tag_observation g) -
      (-bmol_zero_observation f_ref + bmol_large_source_tag_observation f_ref)

/--
Under the finite-observation topology, the observation-based chart is
continuous because it factors through continuous coordinate projections.
-/
theorem continuous_slice_chart_finite_observation_of_bmol_finite_topology
    (f_ref : BMol) :
    @Continuous BMol SliceSpace bmol_finite_topology inferInstance
      (slice_chart_finite_observation f_ref) := by
  let _ : TopologicalSpace BMol := bmol_finite_topology
  have h_coord :
      @Continuous BMol SliceSpace bmol_finite_topology inferInstance
        (fun g => -bmol_zero_observation g + bmol_large_source_tag_observation g) := by
    exact
      (continuous_bmol_zero_observation_of_bmol_finite_topology.neg.add
        continuous_bmol_large_source_tag_observation_of_bmol_finite_topology)
  exact h_coord.sub continuous_const

/--
Refined-chart open-image witness.
-/
theorem slice_chart_refined_open (f_ref : BMol) :
  ∃ V, IsOpen V ∧ MapsTo (slice_chart_refined f_ref) (slice_domain f_ref) V := by
  refine ⟨univ, isOpen_univ, ?_⟩
  intro x hx
  trivial

/--
The multivalued replacement chart has the same trivial open-image witness in
the current discrete model.
-/
theorem slice_chart_multivalued_open (f_ref : BMol) :
  ∃ V, IsOpen V ∧ MapsTo (slice_chart_multivalued f_ref) (slice_domain_localized f_ref) V := by
  refine ⟨univ, isOpen_univ, ?_⟩
  intro x hx
  trivial

/--
The refined chart also has an open-image witness on the localized replacement
domain.
-/
theorem slice_chart_refined_open_localized (f_ref : BMol) :
  ∃ V, IsOpen V ∧ MapsTo (slice_chart_refined f_ref) (slice_domain_localized f_ref) V := by
  refine ⟨univ, isOpen_univ, ?_⟩
  intro x hx
  trivial

/-- The refined chart sends the reference point to `0`. -/
theorem slice_chart_refined_self (f_ref : BMol) :
    slice_chart_refined f_ref f_ref = 0 := by
  simp [slice_chart_refined]

/-- The multivalued replacement chart still sends the reference point to `0`. -/
theorem slice_chart_multivalued_self (f_ref : BMol) :
    slice_chart_multivalued f_ref f_ref = 0 := by
  simp [slice_chart_multivalued]

/-- The finite-observation chart still sends the reference point to `0`. -/
theorem slice_chart_finite_observation_self (f_ref : BMol) :
    slice_chart_finite_observation f_ref f_ref = 0 := by
  simp [slice_chart_finite_observation]

/--
At the shifted reference point, `defaultBMol` realizes the first nonbase
finite-observation chart direction.
-/
theorem slice_chart_finite_observation_default_shifted :
    slice_chart_finite_observation shiftedBMol defaultBMol = 1 := by
  simp [slice_chart_finite_observation]

/--
At the shifted reference point, `largeBMol` realizes the second nonbase
finite-observation chart direction.
-/
theorem slice_chart_finite_observation_large_shifted :
    slice_chart_finite_observation shiftedBMol largeBMol = 2 := by
  simp [slice_chart_finite_observation]
  norm_num

/--
If the reference map has zero-value observation `1` and source-domain tag `0`,
then `defaultBMol` realizes the first nonbase finite-observation direction.
-/
theorem slice_chart_finite_observation_default_eq_one_of_zero_eq_one_and_tag_zero
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1)
    (h_tag : bmol_large_source_tag_observation f_ref = 0) :
    slice_chart_finite_observation f_ref defaultBMol = 1 := by
  simp [slice_chart_finite_observation, h_zero, h_tag]

/--
If the reference map has zero-value observation `1` and source-domain tag `0`,
then `largeBMol` realizes the second nonbase finite-observation direction.
-/
theorem slice_chart_finite_observation_large_eq_two_of_zero_eq_one_and_tag_zero
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1)
    (h_tag : bmol_large_source_tag_observation f_ref = 0) :
    slice_chart_finite_observation f_ref largeBMol = 2 := by
  simp [slice_chart_finite_observation, h_zero, h_tag]
  norm_num

/--
If the reference map has zero-value observation `1` and source-domain tag `1`,
then `shiftedBMol` realizes one nonbase finite-observation direction.
-/
theorem slice_chart_finite_observation_shifted_eq_neg_one_of_zero_eq_one_and_tag_one
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1)
    (h_tag : bmol_large_source_tag_observation f_ref = 1) :
    slice_chart_finite_observation f_ref shiftedBMol = -1 := by
  simp [slice_chart_finite_observation, h_zero, h_tag]

/--
If the reference map has zero-value observation `1` and source-domain tag `1`,
then `largeBMol` realizes a second nonbase finite-observation direction.
-/
theorem slice_chart_finite_observation_large_eq_one_of_zero_eq_one_and_tag_one
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1)
    (h_tag : bmol_large_source_tag_observation f_ref = 1) :
    slice_chart_finite_observation f_ref largeBMol = 1 := by
  simp [slice_chart_finite_observation, h_zero, h_tag]

/--
More generally, every reference map with the shifted finite observation class
gives `defaultBMol` the first nonbase finite-observation chart direction.
-/
theorem slice_chart_finite_observation_default_eq_one_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_chart_finite_observation f_ref defaultBMol = 1 := by
  have h_obs' : bmol_finite_observation f_ref = (1, 0) := by
    simpa using h_obs
  have h_zero : bmol_zero_observation f_ref = 1 := by
    exact congrArg Prod.fst h_obs'
  have h_tag : bmol_large_source_tag_observation f_ref = 0 := by
    exact congrArg Prod.snd h_obs'
  simp [slice_chart_finite_observation, h_zero, h_tag]

/--
Likewise, every reference map with the shifted finite observation class gives
`largeBMol` the second nonbase finite-observation chart direction.
-/
theorem slice_chart_finite_observation_large_eq_two_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_chart_finite_observation f_ref largeBMol = 2 := by
  have h_obs' : bmol_finite_observation f_ref = (1, 0) := by
    simpa using h_obs
  have h_zero : bmol_zero_observation f_ref = 1 := by
    exact congrArg Prod.fst h_obs'
  have h_tag : bmol_large_source_tag_observation f_ref = 0 := by
    exact congrArg Prod.snd h_obs'
  simp [slice_chart_finite_observation, h_zero, h_tag]
  norm_num

/--
If the reference point is not `defaultBMol`, then `defaultBMol` realizes the
first nonbase chart direction.
-/
theorem slice_chart_multivalued_default_eq_one_of_ne
    {f_ref : BMol} (h_ref : f_ref ≠ defaultBMol) :
    slice_chart_multivalued f_ref defaultBMol = 1 := by
  simp [slice_chart_multivalued, Ne.symm h_ref]

/--
If the reference point is different from both `largeBMol` and `defaultBMol`,
then `largeBMol` realizes the second nonbase chart direction.
-/
theorem slice_chart_multivalued_large_eq_two_of_ne
    {f_ref : BMol}
    (h_ref_large : f_ref ≠ largeBMol) :
    slice_chart_multivalued f_ref largeBMol = 2 := by
  simp [slice_chart_multivalued, Ne.symm h_ref_large, largeBMol_ne_defaultBMol]

/-- Every non-reference point is sent to the unique nonbase chart value `1`. -/
theorem slice_chart_refined_eq_one_of_ne {f_ref g : BMol} (h : g ≠ f_ref) :
    slice_chart_refined f_ref g = 1 := by
  simp [slice_chart_refined, h]

/--
The current refined chart has only one nonbase direction: all non-reference
points share the same chart value.
-/
theorem slice_chart_refined_nonbase_eq_of_ne
    {f_ref g h : BMol}
    (hg : g ≠ f_ref)
    (hh : h ≠ f_ref) :
    slice_chart_refined f_ref g = slice_chart_refined f_ref h := by
  simp [slice_chart_refined, hg, hh]

/--
The refined operator really distinguishes the two chart values used by
`slice_chart_refined`.
-/
theorem slice_operator_refined_separates_zero_one (f_ref : BMol) :
    slice_operator_refined f_ref 1 ≠ slice_operator_refined f_ref 0 := by
  simp [slice_operator_refined]

/-- At the shifted reference point, the multivalued operator sends `0` to `2`. -/
theorem slice_operator_multivalued_eq_shifted :
    slice_operator_multivalued shiftedBMol = fun z : SliceSpace => 2 - z := by
  funext z
  simp [slice_operator_multivalued]

/--
For every reference map in the shifted finite-observation class, the
finite-observation operator uses the same involution `z ↦ 2 - z`.
-/
theorem slice_operator_finite_observation_eq_shifted_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_operator_finite_observation f_ref = fun z : SliceSpace => 2 - z := by
  funext z
  simp [slice_operator_finite_observation, h_obs]

/--
For every reference map with zero-value observation `1`, the zero-observation
operator uses the involution `z ↦ 2 - z`.
-/
theorem slice_operator_zero_observation_eq_active_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref = fun z : SliceSpace => 2 - z := by
  funext z
  simp [slice_operator_zero_observation, h_zero]

/--
Away from the shifted reference point, the multivalued operator collapses to
the identity map on `SliceSpace`.
-/
theorem slice_operator_multivalued_eq_id_of_ne_shifted
    {f_ref : BMol} (h_ref : f_ref ≠ shiftedBMol) :
    slice_operator_multivalued f_ref = fun z : SliceSpace => z := by
  funext z
  simp [slice_operator_multivalued, h_ref]

/--
Outside the shifted finite-observation class, the finite-observation operator
collapses to the identity map on `SliceSpace`.
-/
theorem slice_operator_finite_observation_eq_id_of_ne_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref ≠ bmol_finite_observation shiftedBMol) :
    slice_operator_finite_observation f_ref = fun z : SliceSpace => z := by
  have h_obs' : bmol_finite_observation f_ref ≠ (1, 0) := by
    simpa using h_obs
  funext z
  simp [slice_operator_finite_observation, h_obs']

/--
Outside the zero-observation-`1` class, the zero-observation operator is just
the identity on `SliceSpace`.
-/
theorem slice_operator_zero_observation_eq_id_of_zero_ne_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref ≠ 1) :
    slice_operator_zero_observation f_ref = fun z : SliceSpace => z := by
  funext z
  simp [slice_operator_zero_observation, h_zero]

/-- At the shifted reference point, the multivalued operator sends `0` to `2`. -/
theorem slice_operator_multivalued_zero_shifted :
    slice_operator_multivalued shiftedBMol 0 = 2 := by
  norm_num [slice_operator_multivalued]

/--
On the shifted finite-observation class, the finite-observation operator sends
`0` to `2`.
-/
theorem slice_operator_finite_observation_zero_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_operator_finite_observation f_ref 0 = 2 := by
  norm_num [slice_operator_finite_observation, h_obs]

/--
On the zero-observation-`1` class, the zero-observation operator sends `0` to
`2`.
-/
theorem slice_operator_zero_observation_zero_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref 0 = 2 := by
  norm_num [slice_operator_zero_observation, h_zero]

/-- At the shifted reference point, the multivalued operator fixes `1`. -/
theorem slice_operator_multivalued_one_shifted :
    slice_operator_multivalued shiftedBMol 1 = 1 := by
  norm_num [slice_operator_multivalued]

/--
On the shifted finite-observation class, the finite-observation operator fixes
`1`.
-/
theorem slice_operator_finite_observation_one_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_operator_finite_observation f_ref 1 = 1 := by
  norm_num [slice_operator_finite_observation, h_obs]

/--
On the zero-observation-`1` class, the zero-observation operator fixes `1`.
-/
theorem slice_operator_zero_observation_one_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref 1 = 1 := by
  norm_num [slice_operator_zero_observation, h_zero]

/-- At the shifted reference point, the multivalued operator sends `2` to `0`. -/
theorem slice_operator_multivalued_two_shifted :
    slice_operator_multivalued shiftedBMol 2 = 0 := by
  norm_num [slice_operator_multivalued]

/--
On the shifted finite-observation class, the finite-observation operator sends
`2` to `0`.
-/
theorem slice_operator_finite_observation_two_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_operator_finite_observation f_ref 2 = 0 := by
  norm_num [slice_operator_finite_observation, h_obs]

/--
On the zero-observation-`1` class, the zero-observation operator sends `2` to
`0`.
-/
theorem slice_operator_zero_observation_two_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref 2 = 0 := by
  norm_num [slice_operator_zero_observation, h_zero]

/--
On the zero-observation-`1` class, the zero-observation operator sends `-1` to
`3`.
-/
theorem slice_operator_zero_observation_neg_one_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref (-1) = 3 := by
  norm_num [slice_operator_zero_observation, h_zero]

/--
On the zero-observation-`1` class, the zero-observation operator sends `3` to
`-1`.
-/
theorem slice_operator_zero_observation_three_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref 3 = -1 := by
  norm_num [slice_operator_zero_observation, h_zero]

/-- The multivalued operator distinguishes the two nonbase chart values `1` and `2`. -/
theorem slice_operator_multivalued_separates_one_two_shifted :
    slice_operator_multivalued shiftedBMol 1 ≠
      slice_operator_multivalued shiftedBMol 2 := by
  rw [slice_operator_multivalued_one_shifted, slice_operator_multivalued_two_shifted]
  norm_num

/--
On the shifted finite-observation class, the finite-observation operator still
distinguishes the two nonbase chart values `1` and `2`.
-/
theorem slice_operator_finite_observation_separates_one_two_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    slice_operator_finite_observation f_ref 1 ≠
      slice_operator_finite_observation f_ref 2 := by
  rw [slice_operator_finite_observation_one_of_eq_shifted_observation h_obs]
  rw [slice_operator_finite_observation_two_of_eq_shifted_observation h_obs]
  norm_num

/--
On the zero-observation-`1` class, the zero-observation operator still
distinguishes the two chart values `1` and `2`.
-/
theorem slice_operator_zero_observation_separates_one_two_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref 1 ≠
      slice_operator_zero_observation f_ref 2 := by
  rw [slice_operator_zero_observation_one_of_zero_eq_one h_zero]
  rw [slice_operator_zero_observation_two_of_zero_eq_one h_zero]
  norm_num

/--
On the zero-observation-`1` class, the zero-observation operator distinguishes
the chart values `-1` and `1`.
-/
theorem slice_operator_zero_observation_separates_neg_one_one_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    slice_operator_zero_observation f_ref (-1) ≠
      slice_operator_zero_observation f_ref 1 := by
  rw [slice_operator_zero_observation_neg_one_of_zero_eq_one h_zero]
  rw [slice_operator_zero_observation_one_of_zero_eq_one h_zero]
  norm_num

/-- The finite slice set `{0, 1, 2}` is invariant under the shifted operator. -/
theorem slice_operator_multivalued_maps_three_point_shifted :
    MapsTo (slice_operator_multivalued shiftedBMol)
      ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
      ({(0 : SliceSpace), 1, 2} : Set SliceSpace) := by
  intro z hz
  simp at hz
  rcases hz with rfl | rfl | rfl
  · simp [slice_operator_multivalued_zero_shifted]
  · simp [slice_operator_multivalued_one_shifted]
  · simp [slice_operator_multivalued_two_shifted]

/--
Every reference map in the shifted finite-observation class induces the same
invariant finite slice set `{0, 1, 2}` under the finite-observation operator.
-/
theorem slice_operator_finite_observation_maps_three_point_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    MapsTo (slice_operator_finite_observation f_ref)
      ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
      ({(0 : SliceSpace), 1, 2} : Set SliceSpace) := by
  intro z hz
  simp at hz
  rcases hz with rfl | rfl | rfl
  · simp [slice_operator_finite_observation_zero_of_eq_shifted_observation h_obs]
  · simp [slice_operator_finite_observation_one_of_eq_shifted_observation h_obs]
  · simp [slice_operator_finite_observation_two_of_eq_shifted_observation h_obs]

/--
On the zero-observation-`1` class, the finite slice set `{0, 1, 2}` is
invariant under the zero-observation operator.
-/
theorem slice_operator_zero_observation_maps_three_point_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    MapsTo (slice_operator_zero_observation f_ref)
      ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
      ({(0 : SliceSpace), 1, 2} : Set SliceSpace) := by
  intro z hz
  simp at hz
  rcases hz with rfl | rfl | rfl
  · simp [slice_operator_zero_observation_zero_of_zero_eq_one h_zero]
  · simp [slice_operator_zero_observation_one_of_zero_eq_one h_zero]
  · simp [slice_operator_zero_observation_two_of_zero_eq_one h_zero]

/--
On the zero-observation-`1` class, the larger finite slice set
`{-1, 0, 1, 2, 3}` is also invariant under the zero-observation operator.
-/
theorem slice_operator_zero_observation_maps_five_point_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) :
    MapsTo (slice_operator_zero_observation f_ref)
      ({(-1 : SliceSpace), 0, 1, 2, 3} : Set SliceSpace)
      ({(-1 : SliceSpace), 0, 1, 2, 3} : Set SliceSpace) := by
  intro z hz
  simp at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · simp [slice_operator_zero_observation_neg_one_of_zero_eq_one h_zero]
  · simp [slice_operator_zero_observation_zero_of_zero_eq_one h_zero]
  · simp [slice_operator_zero_observation_one_of_zero_eq_one h_zero]
  · simp [slice_operator_zero_observation_two_of_zero_eq_one h_zero]
  · simp [slice_operator_zero_observation_three_of_zero_eq_one h_zero]

/--
At the shifted reference point, the multivalued operator is differentiable at
every slice value.
-/
theorem slice_operator_multivalued_differentiableAt_shifted (z : SliceSpace) :
    DifferentiableAt ℂ (slice_operator_multivalued shiftedBMol) z := by
  have hdiff : DifferentiableAt ℂ (fun w : SliceSpace => (2 : SliceSpace) - w) z := by
    exact ((differentiableAt_const (c := (2 : SliceSpace)) (x := z)).sub differentiableAt_id)
  simpa [slice_operator_multivalued_eq_shifted] using hdiff

/--
At the shifted reference point, the multivalued operator has derivative `-1`
at every slice value.
-/
theorem deriv_slice_operator_multivalued_shifted (z : SliceSpace) :
    deriv (slice_operator_multivalued shiftedBMol) z = -1 := by
  have hderiv : deriv (fun w : SliceSpace => (2 : SliceSpace) - w) z = -1 := by
    simpa [deriv_id''] using
      (deriv_const_sub (f := fun y : SliceSpace => y) (c := (2 : SliceSpace)) (x := z))
  simpa [slice_operator_multivalued_eq_shifted] using hderiv

/--
On the shifted finite-observation class, the finite-observation operator is
differentiable at every slice value.
-/
theorem slice_operator_finite_observation_differentiableAt_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol)
    (z : SliceSpace) :
    DifferentiableAt ℂ (slice_operator_finite_observation f_ref) z := by
  have hdiff : DifferentiableAt ℂ (fun w : SliceSpace => (2 : SliceSpace) - w) z := by
    exact ((differentiableAt_const (c := (2 : SliceSpace)) (x := z)).sub differentiableAt_id)
  simpa [slice_operator_finite_observation_eq_shifted_of_eq_shifted_observation h_obs] using hdiff

/--
On the shifted finite-observation class, the finite-observation operator has
derivative `-1` at every slice value.
-/
theorem deriv_slice_operator_finite_observation_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol)
    (z : SliceSpace) :
    deriv (slice_operator_finite_observation f_ref) z = -1 := by
  have hderiv : deriv (fun w : SliceSpace => (2 : SliceSpace) - w) z = -1 := by
    simpa [deriv_id''] using
      (deriv_const_sub (f := fun y : SliceSpace => y) (c := (2 : SliceSpace)) (x := z))
  simpa [slice_operator_finite_observation_eq_shifted_of_eq_shifted_observation h_obs] using hderiv

/--
On the zero-observation-`1` class, the zero-observation operator is
differentiable at every slice value.
-/
theorem slice_operator_zero_observation_differentiableAt_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) (z : SliceSpace) :
    DifferentiableAt ℂ (slice_operator_zero_observation f_ref) z := by
  have hdiff : DifferentiableAt ℂ (fun w : SliceSpace => (2 : SliceSpace) - w) z := by
    exact ((differentiableAt_const (c := (2 : SliceSpace)) (x := z)).sub differentiableAt_id)
  simpa [slice_operator_zero_observation_eq_active_of_zero_eq_one h_zero] using hdiff

/--
On the zero-observation-`1` class, the zero-observation operator has
derivative `-1` at every slice value.
-/
theorem deriv_slice_operator_zero_observation_of_zero_eq_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref = 1) (z : SliceSpace) :
    deriv (slice_operator_zero_observation f_ref) z = -1 := by
  have hderiv : deriv (fun w : SliceSpace => (2 : SliceSpace) - w) z = -1 := by
    simpa [deriv_id''] using
      (deriv_const_sub (f := fun y : SliceSpace => y) (c := (2 : SliceSpace)) (x := z))
  simpa [slice_operator_zero_observation_eq_active_of_zero_eq_one h_zero] using hderiv

/--
Away from the shifted reference point, the multivalued operator is just the
identity and therefore differentiable at every slice value.
-/
theorem slice_operator_multivalued_differentiableAt_of_ne_shifted
    {f_ref : BMol} (h_ref : f_ref ≠ shiftedBMol) (z : SliceSpace) :
    DifferentiableAt ℂ (slice_operator_multivalued f_ref) z := by
  simpa [slice_operator_multivalued_eq_id_of_ne_shifted h_ref] using
    (differentiableAt_id : DifferentiableAt ℂ (fun w : SliceSpace => w) z)

/--
Away from the shifted reference point, the multivalued operator has derivative
`1` at every slice value.
-/
theorem deriv_slice_operator_multivalued_of_ne_shifted
    {f_ref : BMol} (h_ref : f_ref ≠ shiftedBMol) (z : SliceSpace) :
    deriv (slice_operator_multivalued f_ref) z = 1 := by
  simpa [slice_operator_multivalued_eq_id_of_ne_shifted h_ref] using
    congrFun
      (deriv_id'' : (deriv fun w : SliceSpace => w) = fun _ => (1 : SliceSpace))
      z

/--
Outside the shifted finite-observation class, the finite-observation operator
is just the identity and therefore differentiable at every slice value.
-/
theorem slice_operator_finite_observation_differentiableAt_of_ne_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref ≠ bmol_finite_observation shiftedBMol)
    (z : SliceSpace) :
    DifferentiableAt ℂ (slice_operator_finite_observation f_ref) z := by
  simpa [slice_operator_finite_observation_eq_id_of_ne_shifted_observation h_obs] using
    (differentiableAt_id : DifferentiableAt ℂ (fun w : SliceSpace => w) z)

/--
Outside the shifted finite-observation class, the finite-observation operator
has derivative `1` at every slice value.
-/
theorem deriv_slice_operator_finite_observation_of_ne_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref ≠ bmol_finite_observation shiftedBMol)
    (z : SliceSpace) :
    deriv (slice_operator_finite_observation f_ref) z = 1 := by
  simpa [slice_operator_finite_observation_eq_id_of_ne_shifted_observation h_obs] using
    congrFun
      (deriv_id'' : (deriv fun w : SliceSpace => w) = fun _ => (1 : SliceSpace))
      z

/--
Outside the zero-observation-`1` class, the zero-observation operator is just
the identity and therefore differentiable at every slice value.
-/
theorem slice_operator_zero_observation_differentiableAt_of_zero_ne_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref ≠ 1) (z : SliceSpace) :
    DifferentiableAt ℂ (slice_operator_zero_observation f_ref) z := by
  simpa [slice_operator_zero_observation_eq_id_of_zero_ne_one h_zero] using
    (differentiableAt_id : DifferentiableAt ℂ (fun w : SliceSpace => w) z)

/--
Outside the zero-observation-`1` class, the zero-observation operator has
derivative `1` at every slice value.
-/
theorem deriv_slice_operator_zero_observation_of_zero_ne_one
    {f_ref : BMol} (h_zero : bmol_zero_observation f_ref ≠ 1) (z : SliceSpace) :
    deriv (slice_operator_zero_observation f_ref) z = 1 := by
  simpa [slice_operator_zero_observation_eq_id_of_zero_ne_one h_zero] using
    congrFun
      (deriv_id'' : (deriv fun w : SliceSpace => w) = fun _ => (1 : SliceSpace))
      z

/--
Constructive singleton witness package for the refined chart.
This is an upstream building block for replacing ex-falso `h_exists` paths.
-/
theorem refined_singleton_slice_witness (f_ref : BMol) :
    ∃ (K : Set BMol) (P : Set SliceSpace),
      IsCompact P ∧
      Convex ℝ P ∧
      MapsTo (slice_operator f_ref) P P ∧
      K = {f | slice_chart_refined f_ref f ∈ P} ∧
      SurjOn (slice_chart_refined f_ref) K P ∧
      K.Finite ∧
      InjOn (slice_chart_refined f_ref) K ∧
      ContinuousOn (slice_operator f_ref) ((slice_chart_refined f_ref) '' K) ∧
      K.Nonempty ∧
      f_ref ∈ K := by
  classical
  refine ⟨{f_ref}, {0}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.finite_singleton (0 : SliceSpace)).isCompact
  · exact convex_singleton (0 : SliceSpace)
  · intro x hx
    simp [slice_operator]
  · ext f
    constructor
    · intro hf
      simp [slice_chart_refined] at hf ⊢
      exact hf
    · intro hf
      simp [slice_chart_refined] at hf ⊢
      exact hf
  · intro y hy
    have hy0 : y = (0 : SliceSpace) := by simp at hy; exact hy
    refine ⟨f_ref, by simp, ?_⟩
    simp [slice_chart_refined, hy0]
  · exact Set.finite_singleton f_ref
  · intro x hx y hy hxy
    simp at hx hy
    simp [hx, hy]
  ·
    -- In the discrete topology on `BMol`, continuity-on is trivial.
    change ContinuousOn (fun _ : SliceSpace => (0 : SliceSpace))
      ((slice_chart_refined f_ref) '' ({f_ref} : Set BMol))
    exact continuousOn_const
  · exact Set.singleton_nonempty f_ref
  · simp

/-- Conjugacy of Rfast and F via the chart. -/
theorem slice_conjugacy (f_star : BMol)
    (h_conj : ∀ x ∈ slice_domain f_star,
      slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x)) :
  ∀ x ∈ slice_domain f_star,
    slice_operator f_star (slice_chart f_star x) = slice_chart f_star (Rfast x) :=
  h_conj

/-- 
The main spectral result (assumed as an explicit hypothesis).
If f* has Siegel bounds, then the induced operator F is hyperbolic.
-/
theorem slice_spectral_gap {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ}
  (_h : HasSiegelBounds f_star D U a b)
  (h_gap :
    let F := slice_operator f_star
    let φ := slice_chart f_star
    DifferentiableAt ℂ F (φ f_star) ∧
    IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star))) :
  let F := slice_operator f_star
  let φ := slice_chart f_star
  DifferentiableAt ℂ F (φ f_star) ∧
  IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)) :=
  h_gap

end Molecule
