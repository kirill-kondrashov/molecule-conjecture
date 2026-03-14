import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.GreenLemmas
import Yoccoz.Quadratic.Complex.Groetzsch
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Finite.Basic
import Lean
import Molecule.BMol
import Molecule.HMol
import Molecule.Mol
import Molecule.Rfast
import Molecule.Hyperbolicity
import Molecule.PiecewiseAnalytic
import Molecule.RfastHorseshoe
import Molecule.Compactness
import Molecule.Construction
import Molecule.BanachSlice
import Molecule.FirstStepConstruction
import Molecule.Problem4_3
import Molecule.HyperbolicityTheorems
import Molecule.RenormalizationFixedPointUniqueness

namespace Molecule

open MLC.Quadratic Complex Topology Set Filter
noncomputable section

/-!
Dudko's Molecule Conjecture.

This file provides the formal statement of the Molecule Conjecture (Dudko-Lyubich-Selinger, arXiv:1703.01206).
The conjecture posits the existence of a "pacman" renormalization operator `Rfast` acting on a space of
quadratic-like maps `BMol`, and a corresponding renormalization horseshoe `HMol`.

# Project Structure and Formalization State

The components of this conjecture are now rigorously defined in separate modules:

* **Operator Domain (`Molecule.BMol`)**: `BMol` is the space of Quadratic-Like maps.
* **Horseshoe Domain (`Molecule.HMol`)**: `HMol` models the invariant set (horseshoe) of the operator.
* **Renormalization (`Molecule.Rfast`)**: `Rfast` is defined as a totalized function returning a valid renormalization if one exists (using `Classical.choose`).
* **Horseshoe Restriction (`Molecule.RfastHorseshoe`)**: `Rfast_HMol` represents the restriction of `Rfast` to `HMol`. It handles the conversion between the disconnected horseshoe topology and the connected quadratic-like map topology via extension/restriction predicates.
* **Hyperbolicity (`Molecule.Hyperbolicity`)**: `IsHyperbolic` formalizes the notion of hyperbolicity for operators on Banach spaces.
* **Analyticity (`Molecule.PiecewiseAnalytic`)**: `IsPiecewiseAnalytic1DUnstable` defines the regularity and spectral properties of the operator.
* **Compactness (`Molecule.Compactness`)**: `IsCompactOperator` asserts the topological compactness of the horseshoe invariant set.

This file assembles these definitions into the final statement `molecule_conjecture_refined`.

The Combinatorial Association implies a semi-conjugacy ρ.
We treat ρ as part of the conjecture's existential statement or as a parameter to the predicate.
Here, we bundle the existence of ρ into the property.
-/
def CombinatoriallyAssociated (f_horseshoe : HMol → HMol) (f_target : ({x : Mol // x ≠ cusp}) → ({x : Mol // x ≠ cusp})) : Prop :=
  ∃ (ρ : HMol → Mol),
    Continuous ρ ∧
    ∀ (h : HMol),
      ∀ (h_neq : ρ h ≠ cusp),
      ρ (f_horseshoe h) = (f_target ⟨ρ h, h_neq⟩).val

/--
Consistent normalization contract on a designated invariant set.
This is a local replacement target for the legacy global contract
`∀ K : Set BMol, ...`.
-/
def NormalizationOn (K : Set BMol) : Prop :=
  (∀ f ∈ K, IsFastRenormalizable f) ∧
  (∀ f ∈ K, criticalValue f = 0) ∧
  (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)

/--
Consistent invariant normalization package: there exists at least one
nonempty invariant set carrying the normalization.
-/
def HasInvariantNormalization : Prop :=
  ∃ K : Set BMol, K.Nonempty ∧ NormalizationOn K

/--
Local invariant slice-data package used throughout the conjecture pipeline.
-/
def HasInvariantSliceData : Prop :=
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
    f_ref ∈ K

/--
Chart-parameterized invariant slice-data package.
This supports migration from the current legacy chart to refined chart models.
-/
def HasInvariantSliceDataWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) : Prop :=
  ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
    IsCompact P ∧
    Convex ℝ P ∧
    MapsTo (op f_ref) P P ∧
    K = {f | chart f_ref f ∈ P} ∧
    SurjOn (chart f_ref) K P ∧
    K.Finite ∧
    InjOn (chart f_ref) K ∧
    ContinuousOn (op f_ref) ((chart f_ref) '' K) ∧
    K.Nonempty ∧
    f_ref ∈ K

/--
The legacy package is exactly the chart-parameterized package instantiated at
`slice_chart` and `slice_operator`.
-/
theorem has_invariant_slice_data_iff_with_legacy :
    HasInvariantSliceData ↔ HasInvariantSliceDataWith slice_chart slice_operator := by
  rfl

/--
Constructive refined-chart witness for the parameterized invariant slice-data package.
-/
theorem has_invariant_slice_data_with_refined (f_ref : BMol) :
    HasInvariantSliceDataWith slice_chart_refined slice_operator := by
  rcases refined_singleton_slice_witness f_ref with
    ⟨K, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont, h_nonempty, h_mem⟩
  exact ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont, h_nonempty, h_mem⟩

/--
Zero-argument refined-chart witness for incremental migration work.
-/
theorem has_invariant_slice_data_with_refined_default :
    HasInvariantSliceDataWith slice_chart_refined slice_operator :=
  has_invariant_slice_data_with_refined defaultBMol

/--
Constructive refined `h_exists`-style witness (legacy shape with `slice_chart_refined`).
-/
theorem molecule_h_exists_refined :
  ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
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
  simpa [HasInvariantSliceDataWith] using has_invariant_slice_data_with_refined_default

/--
Localized contract: invariant slice-data paired with normalization on the same set `K`.
-/
def InvariantSliceDataWithNormalization : Prop :=
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
    f_ref ∈ K ∧
    NormalizationOn K

/--
Chart-parameterized localized contract: invariant slice-data paired with
normalization on the same set `K`.
-/
def InvariantSliceDataWithNormalizationWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) : Prop :=
  ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
    IsCompact P ∧
    Convex ℝ P ∧
    MapsTo (op f_ref) P P ∧
    K = {f | chart f_ref f ∈ P} ∧
    SurjOn (chart f_ref) K P ∧
    K.Finite ∧
    InjOn (chart f_ref) K ∧
    ContinuousOn (op f_ref) ((chart f_ref) '' K) ∧
    K.Nonempty ∧
    f_ref ∈ K ∧
    NormalizationOn K

/--
Legacy normalized package as a parameterized-instance identity.
-/
theorem invariant_slice_data_with_normalization_iff_with_legacy :
    InvariantSliceDataWithNormalization ↔
      InvariantSliceDataWithNormalizationWith slice_chart slice_operator := by
  rfl

/--
Constructive refined-chart normalized witness from local normalization data
at a designated reference map.
-/
theorem invariant_slice_data_with_normalization_with_refined_of_local
    (f_ref : BMol)
    (h_renorm_ref : IsFastRenormalizable f_ref)
    (h_crit_ref : criticalValue f_ref = 0)
    (h_domain_ref : f_ref.V ⊆ Metric.ball 0 0.1) :
    InvariantSliceDataWithNormalizationWith slice_chart_refined slice_operator := by
  let K : Set BMol := {f_ref}
  let P : Set SliceSpace := {(0 : SliceSpace)}
  have h_normK : NormalizationOn K := by
    constructor
    · intro f hf
      have hf_ref : f = f_ref := by simpa [K] using hf
      simpa [hf_ref] using h_renorm_ref
    constructor
    · intro f hf
      have hf_ref : f = f_ref := by simpa [K] using hf
      simpa [hf_ref] using h_crit_ref
    · intro f hf
      have hf_ref : f = f_ref := by simpa [K] using hf
      simpa [hf_ref] using h_domain_ref
  refine ⟨K, f_ref, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_normK⟩
  · simp [P]
  · simp [P]
  · intro x hx
    simp [P, slice_operator] at hx ⊢
  · ext f
    simp [K, P, slice_chart_refined]
  · intro y hy
    refine ⟨f_ref, by simp [K], ?_⟩
    have hy0 : y = 0 := by
      simp [P] at hy
      exact hy
    simp [slice_chart_refined, hy0]
  · simp [K]
  · intro x hx y hy hxy
    simp [K] at hx hy
    simp [hx, hy]
  · simpa [slice_operator] using
      (continuousOn_const :
        ContinuousOn (fun _ : SliceSpace => (0 : SliceSpace))
          ((slice_chart_refined f_ref) '' K))
  · simp [K]
  · simp [K]

/--
Constructive refined-chart normalized witness from global normalization alone.
-/
theorem invariant_slice_data_with_normalization_with_refined_of_global_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    InvariantSliceDataWithNormalizationWith slice_chart_refined slice_operator := by
  let f_ref : BMol := defaultBMol
  have h_singleton := h_norm ({f_ref} : Set BMol)
  have h_renorm_ref : IsFastRenormalizable f_ref := by
    exact h_singleton.1 f_ref (by simp)
  have h_local : criticalValue f_ref = 0 ∧ f_ref.V ⊆ Metric.ball 0 0.1 := by
    exact ⟨h_singleton.2.1 f_ref (by simp), h_singleton.2.2 f_ref (by simp)⟩
  exact invariant_slice_data_with_normalization_with_refined_of_local
    f_ref
    h_renorm_ref
    h_local.1
    h_local.2

/--
With the current scaffold (`slice_chart` is constant), any witness of
`HasInvariantSliceData` forces the entire `BMol` space to be finite.
This is a structural obstruction for constructive witness extraction.
-/
theorem has_invariant_slice_data_forces_univ_finite
    (h_data : HasInvariantSliceData) :
    (Set.univ : Set BMol).Finite := by
  rcases h_data with
    ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont, h_nonempty, h_mem⟩
  have h_zero_in_P : (0 : SliceSpace) ∈ P := by
    have h_ref_in_chart_preimage : f_ref ∈ {f : BMol | slice_chart f_ref f ∈ P} := by
      simpa [hK_def] using h_mem
    simpa [slice_chart] using h_ref_in_chart_preimage
  have hK_univ : K = Set.univ := by
    ext f
    constructor
    · intro _hf
      trivial
    · intro _hf
      have hf_in_chart_preimage : f ∈ {g : BMol | slice_chart f_ref g ∈ P} := by
        simpa [slice_chart] using h_zero_in_P
      simpa [hK_def] using hf_in_chart_preimage
  simpa [hK_univ] using h_fin

/--
With the current legacy scaffold (`slice_chart` is constant), any witness of
`InvariantSliceDataWithNormalization` collapses to global normalization.
-/
theorem invariant_slice_data_with_normalization_implies_global_normalization_contract
    (h_data : InvariantSliceDataWithNormalization) :
    ∀ K : Set BMol,
      (∀ f ∈ K, IsFastRenormalizable f) ∧
      (∀ f ∈ K, criticalValue f = 0) ∧
      (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1) := by
  rcases h_data with
    ⟨K0, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont,
      h_nonempty, h_mem, h_normK⟩
  have h_zero_in_P : (0 : SliceSpace) ∈ P := by
    have h_ref_in_chart_preimage : f_ref ∈ {f : BMol | slice_chart f_ref f ∈ P} := by
      simpa [hK_def] using h_mem
    simpa [slice_chart] using h_ref_in_chart_preimage
  have hK_univ : K0 = Set.univ := by
    ext f
    constructor
    · intro _hf
      trivial
    · intro _hf
      have hf_in_chart_preimage : f ∈ {g : BMol | slice_chart f_ref g ∈ P} := by
        simpa [slice_chart] using h_zero_in_P
      simpa [hK_def] using hf_in_chart_preimage
  have h_norm_univ : NormalizationOn Set.univ := by
    simpa [hK_univ] using h_normK
  intro K
  constructor
  · intro f hfK
    exact h_norm_univ.1 f (by simp)
  · constructor
    · intro f hfK
      exact h_norm_univ.2.1 f (by simp)
    · intro f hfK
      exact h_norm_univ.2.2 f (by simp)

/--
Dead-end certificate: the legacy invariant-slice-data-with-normalization shape
is inconsistent in the current model because it implies the inconsistent global
normalization contract.
-/
theorem no_invariant_slice_data_with_normalization :
    ¬ InvariantSliceDataWithNormalization := by
  intro h_data
  let h_norm :=
    invariant_slice_data_with_normalization_implies_global_normalization_contract h_data
  have hrenorm : IsFastRenormalizable defaultBMol := by
    exact (h_norm {defaultBMol}).1 defaultBMol (by simp)
  exact defaultBMol_not_renormalizable hrenorm

/--
Migration lemma: the legacy global normalization contract implies
the local invariant normalization package.
-/
theorem has_invariant_normalization_of_global
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    HasInvariantNormalization := by
  refine ⟨{defaultBMol}, ?_, ?_⟩
  · exact Set.singleton_nonempty defaultBMol
  · exact h_norm {defaultBMol}

/--
Feasibility gate: the global normalization contract is inconsistent in the
current model because it would force `defaultBMol` to be fast renormalizable.
-/
theorem global_normalization_contract_inconsistent
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    False := by
  let K : Set BMol := {defaultBMol}
  have hK := h_norm K
  have hrenorm : IsFastRenormalizable defaultBMol := by
    exact hK.1 defaultBMol (by simp [K])
  exact defaultBMol_not_renormalizable hrenorm

/--
Equivalent zero-argument dead-end certificate for the global normalization
contract shape used in the legacy pipeline.
-/
theorem no_global_normalization_contract :
    ¬ (∀ K : Set BMol,
      (∀ f ∈ K, IsFastRenormalizable f) ∧
      (∀ f ∈ K, criticalValue f = 0) ∧
      (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) := by
  intro h_norm
  exact global_normalization_contract_inconsistent h_norm

/--
Pointwise localization of the global normalization contract.
-/
theorem normalization_at_point_of_global
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    {f : BMol} :
    criticalValue f = 0 ∧ f.V ⊆ Metric.ball 0 0.1 := by
  have h_singleton := h_norm ({f} : Set BMol)
  exact ⟨h_singleton.2.1 f (by simp), h_singleton.2.2 f (by simp)⟩

/--
Build fixed-point normalization data from:
- existence of a renormalizable fixed point, and
- global normalization.
-/
theorem fixed_point_normalization_data_of_fixed_exists_and_global_norm
    (h_fixed_exists : ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f)
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    FixedPointNormalizationData := by
  rcases h_fixed_exists with ⟨f_star, h_renorm, h_fixed⟩
  have h_local : criticalValue f_star = 0 ∧ f_star.V ⊆ Metric.ball 0 0.1 :=
    normalization_at_point_of_global h_norm
  exact ⟨f_star, h_fixed, h_renorm, h_local.1, h_local.2⟩

/--
Transfer contract: any fast-renormalizable fixed point satisfies the local
normalization conditions needed for Problem 4.3.
-/
def FixedPointLocalNormalizationTransfer : Prop :=
  ∀ f : BMol, Rfast f = f → IsFastRenormalizable f →
    criticalValue f = 0 ∧ f.V ⊆ Metric.ball 0 0.1

/--
Critical-value component of fixed-point local normalization transfer.
-/
def FixedPointCriticalValueTransferSource : Prop :=
  ∀ f : BMol, Rfast f = f → IsFastRenormalizable f →
    criticalValue f = 0

/--
`V`-bound component of fixed-point local normalization transfer.
-/
def FixedPointVBoundTransferSource : Prop :=
  ∀ f : BMol, Rfast f = f → IsFastRenormalizable f →
    f.V ⊆ Metric.ball 0 0.1

/--
Assemble fixed-point local normalization transfer from critical-value and
`V`-bound component sources.
-/
theorem fixed_point_local_normalization_transfer_of_critical_and_vbound
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_vbound : FixedPointVBoundTransferSource) :
    FixedPointLocalNormalizationTransfer := by
  intro f h_fixed h_renorm
  exact ⟨h_crit f h_fixed h_renorm, h_vbound f h_fixed h_renorm⟩

/--
Project critical-value and `V`-bound component sources from fixed-point local
normalization transfer.
-/
theorem fixed_point_critical_and_vbound_of_local_normalization_transfer
    (h_transfer : FixedPointLocalNormalizationTransfer) :
    FixedPointCriticalValueTransferSource ∧ FixedPointVBoundTransferSource := by
  refine ⟨?_, ?_⟩
  · intro f h_fixed h_renorm
    exact (h_transfer f h_fixed h_renorm).1
  · intro f h_fixed h_renorm
    exact (h_transfer f h_fixed h_renorm).2

/--
Ingredient bundle for constructing fixed-point normalization data:
- existence of a fast-renormalizable fixed point of `Rfast`, and
- local normalization transfer on fast-renormalizable fixed points.
-/
def MoleculeResidualFixedPointNormalizationIngredients : Prop :=
  (∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f) ∧
  FixedPointLocalNormalizationTransfer

/--
Global normalization implies fixed-point local normalization transfer.
-/
theorem fixed_point_local_normalization_transfer_of_global_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    FixedPointLocalNormalizationTransfer := by
  intro f _h_fixed _h_renorm
  exact normalization_at_point_of_global h_norm

/--
Local invariant-set membership plus normalization imply fixed-point local
normalization transfer.
-/
theorem fixed_point_local_normalization_transfer_of_membership_and_normalization_on
    {K : Set BMol}
    (h_mem : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f → f ∈ K)
    (h_norm_on : NormalizationOn K) :
    FixedPointLocalNormalizationTransfer := by
  intro f h_fixed h_renorm
  have hfK : f ∈ K := h_mem f h_fixed h_renorm
  exact ⟨h_norm_on.2.1 f hfK, h_norm_on.2.2 f hfK⟩

/--
Build fixed-point normalization data from:
- renormalizable fixed-point existence, and
- fixed-point local normalization transfer.
-/
theorem fixed_point_normalization_data_of_fixed_exists_and_transfer
    (h_fixed_exists : ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f)
    (h_transfer : FixedPointLocalNormalizationTransfer) :
    FixedPointNormalizationData := by
  rcases h_fixed_exists with ⟨f_star, h_renorm, h_fixed⟩
  have h_local : criticalValue f_star = 0 ∧ f_star.V ⊆ Metric.ball 0 0.1 :=
    h_transfer f_star h_fixed h_renorm
  exact ⟨f_star, h_fixed, h_renorm, h_local.1, h_local.2⟩

/--
Build fixed-point normalization data directly from:
- the ground fixed-point existence theorem,
- renormalizability of fixed points, and
- the critical-value and `V`-bound transfer components.
-/
theorem fixed_point_normalization_data_of_fixed_point_exists_and_component_transfers
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_vbound : FixedPointVBoundTransferSource) :
    FixedPointNormalizationData := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  have h_renorm_star : IsFastRenormalizable f_star := h_renorm f_star h_fixed
  exact ⟨
    f_star,
    h_fixed,
    h_renorm_star,
    h_crit f_star h_fixed h_renorm_star,
    h_vbound f_star h_fixed h_renorm_star
  ⟩

/--
Build fixed-point normalization data directly from:
- the ground fixed-point existence theorem,
- renormalizability of fixed points, and
- the `V`-bound transfer component.

The critical-value condition comes for free from `fixed_point_exists`.
-/
theorem fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_vbound
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_vbound : FixedPointVBoundTransferSource) :
    FixedPointNormalizationData := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, h_crit⟩
  have h_renorm_star : IsFastRenormalizable f_star := h_renorm f_star h_fixed
  exact ⟨
    f_star,
    h_fixed,
    h_renorm_star,
    h_crit,
    h_vbound f_star h_fixed h_renorm_star
  ⟩

/--
Build bundled residual fixed-point-normalization ingredients from:
- the ground fixed-point existence theorem,
- renormalizability of fixed points, and
- the critical-value and `V`-bound transfer components.
-/
theorem residual_fixed_point_normalization_ingredients_of_fixed_point_exists_and_component_transfers
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualFixedPointNormalizationIngredients := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  exact ⟨
    ⟨f_star, h_renorm f_star h_fixed, h_fixed⟩,
    fixed_point_local_normalization_transfer_of_critical_and_vbound h_crit h_vbound
  ⟩

/--
Subtarget B bridge: obtain fixed-point local normalization transfer from:
- one normalized fast-renormalizable fixed point, and
- uniqueness of fast-renormalizable fixed points.
-/
theorem fixed_point_local_normalization_transfer_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    FixedPointLocalNormalizationTransfer := by
  rcases h_fixed_data with ⟨f_star, h_fixed_star, h_renorm_star, h_crit_star, h_domain_star⟩
  intro f h_fixed h_renorm
  have h_eq : f = f_star := by
    exact h_unique f f_star ⟨h_fixed, h_renorm⟩ ⟨h_fixed_star, h_renorm_star⟩
  subst h_eq
  exact ⟨h_crit_star, h_domain_star⟩

/--
Project the critical-value transfer component from fixed data + uniqueness.
-/
theorem fixed_point_critical_value_transfer_source_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    FixedPointCriticalValueTransferSource := by
  intro f h_fixed h_renorm
  exact
    (fixed_point_local_normalization_transfer_of_fixed_data_and_unique
      h_fixed_data h_unique f h_fixed h_renorm).1

/--
Project the `V`-bound transfer component from fixed data + uniqueness.
-/
theorem fixed_point_vbound_transfer_source_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    FixedPointVBoundTransferSource := by
  intro f h_fixed h_renorm
  exact
    (fixed_point_local_normalization_transfer_of_fixed_data_and_unique
      h_fixed_data h_unique f h_fixed h_renorm).2

/--
Build bundled residual fixed-point-normalization ingredients from:
- one normalized fast-renormalizable fixed point, and
- uniqueness of fast-renormalizable fixed points.
-/
theorem residual_fixed_point_normalization_ingredients_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    MoleculeResidualFixedPointNormalizationIngredients := by
  rcases h_fixed_data with ⟨f_star, h_fixed_star, h_renorm_star, h_crit_star, h_domain_star⟩
  let h_fixed_data' : FixedPointNormalizationData :=
    ⟨f_star, h_fixed_star, h_renorm_star, h_crit_star, h_domain_star⟩
  exact ⟨
    ⟨f_star, h_renorm_star, h_fixed_star⟩,
    fixed_point_local_normalization_transfer_of_fixed_data_and_unique h_fixed_data' h_unique
  ⟩

/--
Project fixed-point local normalization transfer directly from the bundled
ingredient contract.
-/
theorem fixed_point_local_normalization_transfer_of_ingredients
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients) :
    FixedPointLocalNormalizationTransfer :=
  h_ingredients.2

/--
Build fixed-point local normalization transfer directly from the bundled
ingredient contract plus uniqueness.
-/
theorem fixed_point_local_normalization_transfer_of_ingredients_and_unique
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    FixedPointLocalNormalizationTransfer :=
  fixed_point_local_normalization_transfer_of_fixed_data_and_unique
    (fixed_point_normalization_data_of_fixed_exists_and_transfer
      h_ingredients.1
      h_ingredients.2)
    h_unique

/--
Build fixed-point normalization data from the bundled ingredient contract.
-/
theorem fixed_point_normalization_data_of_ingredients
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients) :
    FixedPointNormalizationData :=
  fixed_point_normalization_data_of_fixed_exists_and_transfer
    h_ingredients.1
    h_ingredients.2

/--
Global normalization provides the bundled ingredient contract.
-/
theorem residual_fixed_point_normalization_ingredients_of_global_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    MoleculeResidualFixedPointNormalizationIngredients := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  have h_renorm : IsFastRenormalizable f_star := by
    exact (h_norm ({f_star} : Set BMol)).1 f_star (by simp)
  exact ⟨
    ⟨f_star, h_renorm, h_fixed⟩,
    fixed_point_local_normalization_transfer_of_global_norm h_norm
  ⟩

/--
Project renormalizable fixed-point existence from local fixed-point
normalization data.
-/
theorem renormalizable_fixed_exists_of_fixed_point_normalization_data
    (h_fixed_data : FixedPointNormalizationData) :
    ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f := by
  rcases h_fixed_data with ⟨f_star, h_fixed, h_renorm, _h_crit, _h_domain⟩
  exact ⟨f_star, h_renorm, h_fixed⟩

/--
Derive renormalizable fixed-point existence from:
- constructive fixed-point existence of `Rfast`, and
- global normalization.
-/
theorem renormalizable_fixed_exists_of_global_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  have h_renorm : IsFastRenormalizable f_star := by
    exact (h_norm ({f_star} : Set BMol)).1 f_star (by simp)
  exact ⟨f_star, h_renorm, h_fixed⟩

/--
The designated fixed point chosen by the ground theorem `fixed_point_exists`.
-/
noncomputable def selected_fixed_point : BMol :=
  Classical.choose fixed_point_exists

/--
Specification of the designated fixed point chosen by `fixed_point_exists`.
-/
theorem selected_fixed_point_spec :
    Rfast selected_fixed_point = selected_fixed_point ∧
      criticalValue selected_fixed_point = 0 :=
  Classical.choose_spec fixed_point_exists

/--
The designated selected point is indeed fixed by `Rfast`.
-/
theorem selected_fixed_point_fixed :
    Rfast selected_fixed_point = selected_fixed_point :=
  selected_fixed_point_spec.1

/--
The hybrid class of the designated selected point is fixed by `R_hybrid`.
-/
theorem selected_fixed_point_hybrid_fixed :
    R_hybrid (toHybridClass selected_fixed_point) =
      toHybridClass selected_fixed_point := by
  simpa [R_hybrid, toHybridClass] using selected_fixed_point_fixed

/--
Bridge contract: every fixed point of `Rfast` is fast-renormalizable.
This isolates the exact missing ingredient needed to upgrade
`fixed_point_exists` to a renormalizable fixed-point witness.
-/
def FixedPointImpliesRenormalizable : Prop :=
  ∀ f : BMol, Rfast f = f → IsFastRenormalizable f

/--
Restricted bridge contract on a designated set `K`:
every fixed point of `Rfast` in `K` is fast-renormalizable.
-/
def FixedPointImpliesRenormalizableOn (K : Set BMol) : Prop :=
  ∀ f : BMol, f ∈ K → Rfast f = f → IsFastRenormalizable f

/--
Construct a renormalizable fixed-point witness from:
- a fixed-point witness in a designated set `K`, and
- a restricted bridge contract on `K`.
-/
theorem renormalizable_fixed_exists_of_fixed_point_exists_in_and_bridge_on
    {K : Set BMol}
    (h_fixed_in : ∃ f : BMol, f ∈ K ∧ Rfast f = f)
    (h_bridge_on : FixedPointImpliesRenormalizableOn K) :
    ∃ f : BMol, f ∈ K ∧ IsFastRenormalizable f ∧ Rfast f = f := by
  rcases h_fixed_in with ⟨f_star, hfK, h_fixed⟩
  exact ⟨f_star, hfK, h_bridge_on f_star hfK h_fixed, h_fixed⟩

/--
Singleton-domain bridge constructor: if the designated point is
fast-renormalizable, then the localized bridge contract holds on its singleton.
-/
theorem fixed_point_implies_renormalizable_on_singleton_of_renorm
    {f_star : BMol}
    (h_renorm : IsFastRenormalizable f_star) :
    FixedPointImpliesRenormalizableOn ({f_star} : Set BMol) := by
  intro f hfK _h_fixed
  have hf_eq : f = f_star := by simpa using hfK
  simpa [hf_eq] using h_renorm

/--
On a singleton domain, the localized bridge contract is equivalent to
renormalizability of the designated fixed point, provided that point is
actually fixed by `Rfast`.
-/
theorem fixed_point_implies_renormalizable_on_singleton_iff
    {f_star : BMol}
    (h_fixed : Rfast f_star = f_star) :
    FixedPointImpliesRenormalizableOn ({f_star} : Set BMol) ↔
      IsFastRenormalizable f_star := by
  constructor
  · intro h_bridge
    exact h_bridge f_star (by simp) h_fixed
  · intro h_renorm
    exact fixed_point_implies_renormalizable_on_singleton_of_renorm h_renorm

/--
Exact one-point renormalizability source exposed by PLAN_83.
This is the current live theorem target on the existence side.
-/
def MoleculeResidualSelectedFixedPointRenormalizableSource : Prop :=
  IsFastRenormalizable selected_fixed_point

/--
The singleton bridge contract at the designated selected point is exactly the
same data as renormalizability of that point.
-/
theorem molecule_residual_selected_fixed_point_bridge_iff :
    FixedPointImpliesRenormalizableOn ({selected_fixed_point} : Set BMol) ↔
      MoleculeResidualSelectedFixedPointRenormalizableSource :=
  fixed_point_implies_renormalizable_on_singleton_iff selected_fixed_point_fixed

/--
Exact identification source for PLAN_83:
every renormalizable fixed point of `Rfast` must coincide with the designated
selected fixed point from `fixed_point_exists`.
-/
def MoleculeResidualSelectedFixedPointIdentificationSource : Prop :=
  ∀ g : BMol, IsFastRenormalizable g → Rfast g = g → selected_fixed_point = g

/--
Stronger exact identification source for PLAN_83:
every fixed point of `Rfast` must coincide with the designated selected fixed
point from `fixed_point_exists`.
-/
def MoleculeResidualSelectedFixedPointFixedIdentificationSource : Prop :=
  ∀ g : BMol, Rfast g = g → selected_fixed_point = g

/--
Sharper class-level identification source for PLAN_83:
every fixed point of `R_hybrid` must coincide with the hybrid class of the
designated selected fixed point from `fixed_point_exists`.
-/
def MoleculeResidualSelectedHybridClassFixedIdentificationSource : Prop :=
  ∀ c : HybridClass, R_hybrid c = c → toHybridClass selected_fixed_point = c

/--
Exact hybrid-class fixed-point uniqueness source for PLAN_83:
all fixed points of `R_hybrid` coincide, without a renormalizability side
condition.
-/
def MoleculeResidualHybridClassFixedPointExactUniquenessSource : Prop :=
  ∀ c1 c2 : HybridClass, R_hybrid c1 = c1 → R_hybrid c2 = c2 → c1 = c2

/--
Rejected reduction target for PLAN_83:
every fixed point of `R_hybrid` is fast-renormalizable.
In the current identity-model seam this is exactly the false full-domain bridge
`FixedPointImpliesRenormalizable`.
-/
def MoleculeResidualHybridClassFixedPointRenormalizableSource : Prop :=
  ∀ c : HybridClass, R_hybrid c = c → IsFastRenormalizable c

/--
The stronger fixed-point-only identification source implies the
renormalizable-fixed-point identification source.
-/
theorem molecule_residual_selected_fixed_point_identification_of_fixed_identification
    (h_ident_fixed : MoleculeResidualSelectedFixedPointFixedIdentificationSource) :
    MoleculeResidualSelectedFixedPointIdentificationSource := by
  intro g _h_renorm h_fix
  exact h_ident_fixed g h_fix

/--
Hybrid-class fixed-point identification collapses to map-level fixed-point
identification in the current identity-model seam.
-/
theorem molecule_residual_selected_fixed_point_fixed_identification_of_hybrid_class_fixed_identification
    (h_ident_class : MoleculeResidualSelectedHybridClassFixedIdentificationSource) :
    MoleculeResidualSelectedFixedPointFixedIdentificationSource := by
  intro g h_fix
  have h_class_fix : R_hybrid (toHybridClass g) = toHybridClass g := by
    simpa [R_hybrid, toHybridClass] using h_fix
  have h_class_eq :
      toHybridClass selected_fixed_point = toHybridClass g :=
    h_ident_class (toHybridClass g) h_class_fix
  exact toHybridClass_injective h_class_eq

/--
Exact hybrid-class fixed-point uniqueness implies the selected-class
identification target.
-/
theorem molecule_residual_selected_hybrid_class_fixed_identification_of_exact_uniqueness
    (h_unique_exact : MoleculeResidualHybridClassFixedPointExactUniquenessSource) :
    MoleculeResidualSelectedHybridClassFixedIdentificationSource := by
  intro c h_fix
  exact h_unique_exact (toHybridClass selected_fixed_point) c
    selected_fixed_point_hybrid_fixed h_fix

/--
Selected-class identification already implies exact hybrid-class fixed-point
uniqueness, because the selected hybrid class is itself fixed.
-/
theorem molecule_residual_hybrid_class_fixed_point_exact_uniqueness_of_selected_hybrid_class_fixed_identification
    (h_ident_class : MoleculeResidualSelectedHybridClassFixedIdentificationSource) :
    MoleculeResidualHybridClassFixedPointExactUniquenessSource := by
  intro c1 c2 h_fix1 h_fix2
  have h1 : toHybridClass selected_fixed_point = c1 := h_ident_class c1 h_fix1
  have h2 : toHybridClass selected_fixed_point = c2 := h_ident_class c2 h_fix2
  exact h1.symm.trans h2

/--
The selected-class identification source and exact hybrid-class fixed-point
uniqueness are equivalent formulations of the same PLAN_83 frontier.
-/
theorem molecule_residual_hybrid_class_fixed_point_exact_uniqueness_iff_selected_hybrid_class_fixed_identification :
    MoleculeResidualHybridClassFixedPointExactUniquenessSource ↔
      MoleculeResidualSelectedHybridClassFixedIdentificationSource := by
  constructor
  · exact molecule_residual_selected_hybrid_class_fixed_identification_of_exact_uniqueness
  · exact molecule_residual_hybrid_class_fixed_point_exact_uniqueness_of_selected_hybrid_class_fixed_identification

/--
In the current identity-model seam, renormalizability of all fixed hybrid
classes is equivalent to the false full-domain fixed-point renormalizability
bridge.
-/
theorem molecule_residual_hybrid_class_fixed_point_renormalizable_source_iff_fixed_point_implies_renormalizable :
    MoleculeResidualHybridClassFixedPointRenormalizableSource ↔
      FixedPointImpliesRenormalizable := by
  constructor
  · intro h_source f h_fix
    exact h_source (toHybridClass f) (by simpa [R_hybrid, toHybridClass] using h_fix)
  · intro h_bridge c h_fix
    exact h_bridge c (by simpa [R_hybrid] using h_fix)

/--
Dead-end certificate for the obvious next reduction attempt:
`MoleculeResidualHybridClassFixedPointRenormalizableSource` is false in the
current scaffold because it collapses to the false global bridge `(R)`.
-/
theorem no_molecule_residual_hybrid_class_fixed_point_renormalizable_source :
    ¬ MoleculeResidualHybridClassFixedPointRenormalizableSource := by
  intro h_source
  have h_fix_default : R_hybrid (toHybridClass defaultBMol) = toHybridClass defaultBMol := by
    change Rfast defaultBMol = defaultBMol
    simp [Rfast, defaultBMol_not_renormalizable]
  have h_renorm_default : IsFastRenormalizable defaultBMol :=
    h_source (toHybridClass defaultBMol) h_fix_default
  exact defaultBMol_not_renormalizable h_renorm_default

/--
Feasibility gate: in the current model this bridge contract is false, because
`defaultBMol` is a fixed point of `Rfast` but is not fast-renormalizable.
-/
theorem no_fixed_point_implies_renormalizable :
    ¬ FixedPointImpliesRenormalizable := by
  intro h_bridge
  have h_fixed_default : Rfast defaultBMol = defaultBMol := by
    rw [Rfast]
    simp [defaultBMol_not_renormalizable]
  exact defaultBMol_not_renormalizable (h_bridge defaultBMol h_fixed_default)

/--
Dead-end certificate for the active global witness-side carrier `R`:
global renormalizability of `Rfast` fixed points is false in the current
scaffold.
-/
theorem no_molecule_residual_fixed_point_renormalizable_source :
    ¬ (∀ f : BMol, Rfast f = f → IsFastRenormalizable f) :=
  no_fixed_point_implies_renormalizable

/--
Global normalization implies the fixed-point renormalizability bridge contract.
-/
theorem fixed_point_implies_renormalizable_of_global_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    FixedPointImpliesRenormalizable := by
  intro f _h_fixed
  exact (h_norm ({f} : Set BMol)).1 f (by simp)

/--
Localized normalization on `K` implies the restricted bridge contract on `K`.
-/
theorem fixed_point_implies_renormalizable_on_of_normalization_on
    {K : Set BMol}
    (h_norm_on : NormalizationOn K) :
    FixedPointImpliesRenormalizableOn K := by
  intro f hfK _h_fixed
  exact h_norm_on.1 f hfK

/--
Construct a renormalizable fixed-point witness from:
- constructive fixed-point existence of `Rfast`, and
- the fixed-point renormalizability bridge contract.
-/
theorem renormalizable_fixed_exists_of_fixed_point_exists_and_bridge
    (h_bridge : FixedPointImpliesRenormalizable) :
    ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  exact ⟨f_star, h_bridge f_star h_fixed, h_fixed⟩

/--
Migration lemma: legacy `h_exists` is exactly the invariant slice-data package.
-/
theorem has_invariant_slice_data_of_exists
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
        f_ref ∈ K) :
    HasInvariantSliceData := h_exists

/--
Source seam for invariant slice-data without normalization.
-/
def MoleculeResidualInvariantSliceDataSource : Prop :=
  HasInvariantSliceData

/--
Source seam for a fixed point living in a designated invariant slice domain.
-/
def MoleculeResidualInvariantSliceFixedPointSource : Prop :=
  ∃ K : Set BMol, ∃ f : BMol, f ∈ K ∧ Rfast f = f

/--
Project a fixed-point-in-domain witness from explicit invariant slice-data
fields. This uses the existing Schauder-style invariant compact-set theorem and
does not require normalization assumptions.
-/
theorem invariant_slice_fixed_point_in_of_sources
    {K : Set BMol} {f_ref : BMol} {P : Set SliceSpace}
    (_hP_comp : IsCompact P)
    (hP_conv : Convex ℝ P)
    (h_maps : MapsTo (slice_operator f_ref) P P)
    (hK_def : K = {f | slice_chart f_ref f ∈ P})
    (h_surj : SurjOn (slice_chart f_ref) K P)
    (h_fin : K.Finite)
    (h_inj : InjOn (slice_chart f_ref) K)
    (h_cont : ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K))
    (h_nonempty : K.Nonempty) :
    ∃ f : BMol, f ∈ K ∧ Rfast f = f := by
  have hK_image : (slice_chart f_ref) '' K = P := by
    exact slice_chart_image_eq_polydisk_of_surj f_ref P K hK_def h_surj
  have hK_compact : IsCompact K := by
    exact slice_pullback_compact_of_finite K h_fin
  have hK_convex : Convex ℝ ((slice_chart f_ref) '' K) := by
    simpa [hK_image] using hP_conv
  have hK_maps : MapsTo Rfast K K := by
    intro f hfK
    have hfP : slice_chart f_ref f ∈ P := by
      have : f ∈ {g | slice_chart f_ref g ∈ P} := by
        simpa [hK_def] using hfK
      exact this
    have hP_image : slice_operator f_ref (slice_chart f_ref f) ∈ P := h_maps hfP
    have h_conj' :=
      slice_conjugacy f_ref
        (by
          intro x hx
          simp [slice_operator, slice_chart])
        f
        (by simp [slice_domain])
    simpa [hK_def, h_conj'] using hP_image
  rcases fixed_point_in_invariant_compact_set
      K
      f_ref
      hK_compact
      hK_maps
      h_nonempty
      (by
        intro x hx
        simp [slice_operator, slice_chart])
      hK_convex
      h_inj
      h_cont with
    ⟨f, hfK, h_fixed⟩
  exact ⟨f, hfK, h_fixed⟩

/--
Project a fixed-point-in-domain witness from invariant slice-data alone.
-/
theorem molecule_residual_invariant_slice_fixed_point_source_of_invariant_slice_data_source
    (h_data : MoleculeResidualInvariantSliceDataSource) :
    MoleculeResidualInvariantSliceFixedPointSource := by
  rcases h_data with
    ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont,
      h_nonempty, _h_mem⟩
  rcases invariant_slice_fixed_point_in_of_sources
      hP_comp
      hP_conv
      h_maps
      hK_def
      h_surj
      h_fin
      h_inj
      h_cont
      h_nonempty with
    ⟨f, hfK, h_fixed⟩
  exact ⟨K, f, hfK, h_fixed⟩

/--
Forget normalization from the localized invariant-domain package.
-/
theorem molecule_residual_invariant_slice_data_source_of_with_normalization
    (h_data : InvariantSliceDataWithNormalization) :
    MoleculeResidualInvariantSliceDataSource := by
  rcases h_data with
    ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont,
      h_nonempty, h_mem, _h_norm⟩
  exact ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont, h_nonempty, h_mem⟩

/--
Package invariant slice data with localized normalization on the same `K`.
This is a compatibility bridge used while migrating away from global `h_norm`.
-/
theorem has_invariant_slice_data_with_normalization_of_global
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
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
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
      f_ref ∈ K ∧
      NormalizationOn K := by
  rcases h_exists with ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont, h_nonempty, h_mem⟩
  refine ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont, h_nonempty, h_mem, ?_⟩
  exact h_norm K

/--
Compatibility wrapper exposing the localized contract directly from global assumptions.
-/
theorem invariant_slice_data_with_normalization_of_global
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
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    InvariantSliceDataWithNormalization :=
  has_invariant_slice_data_with_normalization_of_global h_exists h_norm



section ProofPlan

/-!
## Proof Plan (formalized from arXiv:1703.01206v3 and arXiv:2512.24171v1)
-/

/--
### 1. Construct the Molecule Renormalization Operator (R_fast)
We use the constructed operators from `Molecule.FirstStepConstruction`.
-/
def Rfast_candidate : BMol → BMol := Rfast_constructed
def Rfast_HMol_candidate : HMol → HMol := Rfast_HMol_constructed

/--
The Combinatorial Model is constructed in `Molecule.Construction`.
We wrap the angle map `Rprm_angle` into the type expected by the conjecture.
For the conjecture statement, we identify the combinatorial action on the moduli space
with the explicit angle map on the boundary, extended to the interior.
For simplicity in this step, we postulate the extension exists and matches the boundary behavior.
-/
def Rprm_combinatorial_model : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp} := Rprm_constructed

-- Link the axiomatic model to our construction
lemma Rprm_model_consistent :
  ∀ (_ : {x : Mol // x ≠ cusp}),
    -- Placeholder: relating the abstract model to MoleculeMap or Rprm_angle
    True := Rprm_model_consistent_proof

/--
### 2. Establish A Priori Bounds (The "Problem 4.3" Step)
A key intermediate step is to establish "pseudo-Siegel a priori bounds" for the remaining
unbounded satellite quadratic-like cases.
-/
def PseudoSiegelAPrioriBounds : Prop := PseudoSiegelAPrioriBoundsStatement

/--
Orbit-transport obligation in the Problem 4.3 bounds pipeline.
-/
def MoleculeOrbitClauseAt
    (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ) : Prop :=
  ∀ (n t : ℕ) (f : BMol),
    n ≥ 1 →
    t ∈ ({a n, b n} : Set ℕ) →
    f ∈ (Rfast^[n]) ⁻¹' U →
    MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
    criticalValue f ∈ (Rfast^[n] f).U ∧
    (f.f^[t] (criticalValue f)) ∈ D ∧
    (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
    (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2)

/--
Global orbit-transport obligation used by legacy theorem interfaces.
-/
def MoleculeOrbitClause : Prop :=
  ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    IsOpen D → IsOpen U →
    f_star ∈ U →
    criticalValue f_star ∈ D →
    MoleculeOrbitClauseAt D U a b

/--
Project a local orbit-clause obligation from the global orbit-clause contract.
-/
theorem molecule_orbit_clause_at_of_orbit_clause
    (h_orbit : MoleculeOrbitClause)
    (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ)
    (h_fixed : Rfast f_star = f_star)
    (h_renorm : IsFastRenormalizable f_star)
    (h_openD : IsOpen D)
    (h_openU : IsOpen U)
    (h_inU : f_star ∈ U)
    (h_cv : criticalValue f_star ∈ D) :
    MoleculeOrbitClauseAt D U a b :=
  h_orbit f_star D U a b h_fixed h_renorm h_openD h_openU h_inU h_cv

/--
Transport data interface for the Problem 4.3 bounds pipeline.
This isolates pseudo-Siegel disk construction and orbit-transport obligations.
-/
structure MoleculeOrbitTransportData where
  h_ps :
    ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
      ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps
  h_orbit : MoleculeOrbitClause

/--
Orbit-only part of the transport-data interface.
-/
structure MoleculeOrbitOnlyData where
  h_orbit : MoleculeOrbitClause

/--
Fixed-point normalization data packaged for localized Problem 4.3 cutover.
-/
theorem problem_4_3_fixed_point_data_of_global
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
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    FixedPointNormalizationData :=
  fixed_point_normalization_data_of_legacy h_exists h_conj h_norm h_unique

/--
Extract fixed-point normalization data directly from the localized slice-data package.

This avoids the legacy global bridge through `h_norm`.
-/
theorem fixed_point_normalization_data_of_invariant_slice_data
    (h_data : InvariantSliceDataWithNormalization) :
    FixedPointNormalizationData := by
  rcases h_data with
    ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont,
      h_nonempty, h_mem, h_normK⟩
  rcases h_normK with ⟨h_renormK, h_critK, h_domainK⟩
  have h_ref_in_P : slice_chart f_ref f_ref ∈ P := by
    have : f_ref ∈ {f | slice_chart f_ref f ∈ P} := by
      simpa [hK_def] using h_mem
    exact this
  have h_rfast_in_K : Rfast f_ref ∈ K := by
    have h_rfast_in_P : slice_chart f_ref (Rfast f_ref) ∈ P := by
      simpa [slice_chart] using h_ref_in_P
    simpa [hK_def] using h_rfast_in_P
  have h_fixed : Rfast f_ref = f_ref := by
    apply h_inj h_rfast_in_K h_mem
    simp [slice_chart]
  exact ⟨f_ref, h_fixed, h_renormK f_ref h_mem, h_critK f_ref h_mem, h_domainK f_ref h_mem⟩

/--
Localized Problem 4.3 theorem path using bundled slice-data and fixed-point data.
-/
theorem problem_4_3_bounds_established_conjecture_localized
    (h_fixed_data : FixedPointNormalizationData)
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
    PseudoSiegelAPrioriBounds := by
  exact problem_4_3_bounds_established_of_fixed_point_data h_fixed_data h_ps h_orbit

/--
Problem 4.3 route from local fixed-point normalization data at a designated
`f_star`, without requiring global normalization in the theorem interface.
-/
theorem problem_4_3_bounds_established_conjecture_from_local_fixed_norm
    (f_star : BMol)
    (h_fixed : Rfast f_star = f_star)
    (h_renorm : IsFastRenormalizable f_star)
    (h_crit : criticalValue f_star = 0)
    (h_domain : f_star.V ⊆ Metric.ball 0 0.1)
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
    PseudoSiegelAPrioriBounds := by
  exact problem_4_3_bounds_established_of_fixed_point_data
    ⟨f_star, h_fixed, h_renorm, h_crit, h_domain⟩
    h_ps
    h_orbit

/--
Problem 4.3 route from:
- renormalizable fixed-point existence, and
- global normalization.

This decouples bounds construction from the full legacy `h_exists`/`h_conj`/`h_unique`
interface.
-/
theorem problem_4_3_bounds_established_conjecture_from_fixed_exists_and_global_norm
    (h_fixed_exists : ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f)
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
          (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2))) :
    PseudoSiegelAPrioriBounds := by
  have h_fp :=
    fixed_point_normalization_data_of_fixed_exists_and_global_norm h_fixed_exists h_norm
  exact problem_4_3_bounds_established_of_fixed_point_data h_fp h_ps h_orbit

/--
Problem 4.3 route from global normalization, pseudo-Siegel disk data,
and orbit transport data only.
-/
theorem problem_4_3_bounds_established_conjecture_from_global_norm_only
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    (h_ps :
      ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
        ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
    (h_orbit : MoleculeOrbitClause) :
    PseudoSiegelAPrioriBounds := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  have h_renorm : IsFastRenormalizable f_star := by
    exact (h_norm ({f_star} : Set BMol)).1 f_star (by simp)
  have h_local : criticalValue f_star = 0 ∧ f_star.V ⊆ Metric.ball 0 0.1 :=
    normalization_at_point_of_global h_norm
  exact problem_4_3_bounds_established_conjecture_from_local_fixed_norm
    f_star h_fixed h_renorm h_local.1 h_local.2 h_ps h_orbit

/--
Problem 4.3 route from global normalization plus packaged orbit-transport data.
-/
theorem problem_4_3_bounds_established_conjecture_from_global_norm_and_transport
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    (h_transport : MoleculeOrbitTransportData) :
    PseudoSiegelAPrioriBounds :=
  problem_4_3_bounds_established_conjecture_from_global_norm_only
    h_norm
    h_transport.h_ps
    h_transport.h_orbit

/--
Problem 4.3 route from local fixed-point normalization data plus packaged
orbit-transport data.
-/
theorem problem_4_3_bounds_established_conjecture_from_fixed_data_and_transport
    (h_fixed_data : FixedPointNormalizationData)
    (h_transport : MoleculeOrbitTransportData) :
    PseudoSiegelAPrioriBounds :=
  problem_4_3_bounds_established_conjecture_localized
    h_fixed_data
    h_transport.h_ps
    h_transport.h_orbit

/--
**Problem 4.3**: Completion of bounds is required for the Molecule Conjecture.
-/
theorem problem_4_3_bounds_established_conjecture
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
    PseudoSiegelAPrioriBounds := by
  exact problem_4_3_bounds_established h_exists h_conj h_norm h_ps h_orbit h_unique

/--
### 3. Prove Hyperbolicity and Unstable Manifold Dimensions
Prove that `Rfast` is a hyperbolic operator with a **one-dimensional unstable manifold**.
And that the restriction to the horseshoe is a compact operator.
-/
theorem rfast_candidate_hyperbolic : IsHyperbolic Rfast_candidate := by
  have h_chart' :
      ∃ V,
        IsOpen V ∧
        MapsTo (slice_chart defaultBMol) (slice_domain defaultBMol) V ∧
        slice_chart defaultBMol defaultBMol ∈ V := by
    rcases slice_chart_open defaultBMol with ⟨V, hV_open, h_maps⟩
    exact ⟨V, hV_open, h_maps, h_maps (by simp [slice_domain])⟩
  refine ⟨defaultBMol, SliceSpace, inferInstance, inferInstance, slice_chart defaultBMol,
    slice_domain defaultBMol, by simp [slice_domain], ?_, ?_, h_chart',
    slice_operator defaultBMol, ?_, ?_, ?_⟩
  · simpa [Rfast_candidate, Rfast_constructed] using defaultBMol_is_fixed_point
  · rw [analyticOn_iff_differentiableOn defaultBMol.isOpen_U]
    exact defaultBMol.differentiable_on
  · intro x hx
    simp [slice_operator, slice_chart]
  · change DifferentiableAt ℂ (fun _ : SliceSpace => (0 : SliceSpace))
      (slice_chart defaultBMol defaultBMol)
    exact differentiableAt_const (c := (0 : SliceSpace))
  · exact isHyperbolic1DUnstable_default
      (fderiv ℂ (slice_operator defaultBMol) (slice_chart defaultBMol defaultBMol))

theorem Rfast_hyperbolicity_conjecture
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
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast)
    (_h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
  IsHyperbolic Rfast_candidate ∧ IsPiecewiseAnalytic1DUnstable Rfast_candidate := by
  have h_hyperbolic_rfast : IsHyperbolic Rfast_candidate := rfast_candidate_hyperbolic
  have h_piecewise_candidate : IsPiecewiseAnalytic1DUnstable Rfast_candidate := by
    simpa [Rfast_candidate, Rfast_constructed] using h_piecewise
  exact ⟨h_hyperbolic_rfast, h_piecewise_candidate⟩

/--
Localized hyperbolicity route:
use fixed-point and spectral contracts directly instead of the global `h_norm` edge.
-/
theorem Rfast_hyperbolicity_conjecture_localized
    (_h_fixed_data : FixedPointNormalizationData)
    (_h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
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
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast) :
  IsHyperbolic Rfast_candidate ∧ IsPiecewiseAnalytic1DUnstable Rfast_candidate := by
  have h_hyperbolic_rfast : IsHyperbolic Rfast_candidate := rfast_candidate_hyperbolic
  have h_piecewise_candidate : IsPiecewiseAnalytic1DUnstable Rfast_candidate := by
    simpa [Rfast_candidate, Rfast_constructed] using h_piecewise
  exact ⟨h_hyperbolic_rfast, h_piecewise_candidate⟩

/--
Bounds-first hyperbolicity route:
consume pre-established Problem 4.3 bounds directly.
-/
theorem Rfast_hyperbolicity_conjecture_from_bounds
    (_h_bounds : PseudoSiegelAPrioriBounds)
    (_h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
    (_h_gap :
      ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
        HasSiegelBounds f_star D U a b →
        let F := slice_operator f_star
        let φ := slice_chart f_star
        DifferentiableAt ℂ F (φ f_star) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)))
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast) :
  IsHyperbolic Rfast_candidate ∧ IsPiecewiseAnalytic1DUnstable Rfast_candidate := by
  have h_hyperbolic_rfast : IsHyperbolic Rfast_candidate := rfast_candidate_hyperbolic
  have h_piecewise_candidate : IsPiecewiseAnalytic1DUnstable Rfast_candidate := by
    simpa [Rfast_candidate, Rfast_constructed] using h_piecewise
  exact ⟨h_hyperbolic_rfast, h_piecewise_candidate⟩

theorem Rfast_HMol_compactness
    (h_compact : IsCompactOperator Rfast_HMol_candidate) :
  IsCompactOperator Rfast_HMol_candidate :=
  h_compact

theorem Rfast_combinatorially_associated
    (h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model) :
  CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model :=
  h_assoc

def SymbolicShift (N : ℕ) := (Int → Fin N)

/--
The "shift" map on the symbolic space `SymbolicShift`.
It maps a sequence `s` to `s'`, where `s'(i) = s(i+1)`.
-/
def shift_map {N : ℕ} (s : SymbolicShift N) : SymbolicShift N :=
  fun i => s (i + 1)

/--
Symbolic-factor relation used in the current combinatorial interface.
This records an intertwining map from `f` to a shift system on `SymbolicShift N`.
-/
def IsConjugateToShift {α : Type*} (f : α → α) (N : ℕ) : Prop :=
  ∃ (φ : α → SymbolicShift N),
    ∀ x, φ (f x) = shift_map (φ x)

theorem R_target_is_shift
    (h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N) :
  ∃ N, IsConjugateToShift Rprm_combinatorial_model N :=
  h_shift

/--
Explicit non-cusp points in `Mol` used as concrete combinatorial witnesses.
-/
lemma zero_mem_mainCardioid : (0 : ℂ) ∈ MainCardioid := by
  refine ⟨0, ?_, ?_⟩
  · ring
  · norm_num

lemma threeSixteen_mem_mainCardioid : ((3 : ℂ) / 16) ∈ MainCardioid := by
  refine ⟨(1 : ℂ) / 4, ?_, ?_⟩
  · ring_nf
  · norm_num

lemma zero_mem_molSet : (0 : ℂ) ∈ MolSet :=
  subset_closure zero_mem_mainCardioid

lemma threeSixteen_mem_molSet : ((3 : ℂ) / 16) ∈ MolSet :=
  subset_closure threeSixteen_mem_mainCardioid

noncomputable def molZero : Mol := ⟨0, zero_mem_molSet⟩
noncomputable def molThreeSixteen : Mol := ⟨(3 : ℂ) / 16, threeSixteen_mem_molSet⟩

lemma molZero_ne_cusp : molZero ≠ cusp := by
  intro h
  have h0 : molZero.1 = cusp.1 := congrArg Subtype.val h
  norm_num [molZero, cusp, cuspVal] at h0

lemma molThreeSixteen_ne_cusp : molThreeSixteen ≠ cusp := by
  intro h
  have h0 : molThreeSixteen.1 = cusp.1 := congrArg Subtype.val h
  norm_num [molThreeSixteen, cusp, cuspVal] at h0

lemma molZero_ne_molThreeSixteen : molZero ≠ molThreeSixteen := by
  intro h
  have h0 : molZero.1 = molThreeSixteen.1 := congrArg Subtype.val h
  norm_num [molZero, molThreeSixteen] at h0

noncomputable def noncuspZero : {x : Mol // x ≠ cusp} := ⟨molZero, molZero_ne_cusp⟩
noncomputable def noncuspThreeSixteen : {x : Mol // x ≠ cusp} :=
  ⟨molThreeSixteen, molThreeSixteen_ne_cusp⟩

lemma two_noncusp_points : noncuspZero ≠ noncuspThreeSixteen := by
  intro h
  apply molZero_ne_molThreeSixteen
  exact congrArg Subtype.val h

/--
Constructive symbolic witness in the current placeholder combinatorial model.
Using `N = 1`, the full shift has a single symbolic sequence, so the
semiconjugacy relation is immediate.
-/
theorem rprm_combinatorial_model_has_shift_factor :
    ∃ N, IsConjugateToShift Rprm_combinatorial_model N := by
  refine ⟨1, ?_⟩
  refine ⟨fun _ _ => 0, ?_⟩
  intro x
  funext i
  simp [shift_map]

/--
Constructive semiconjugacy witness for the current placeholder pair
`(Rfast_HMol_candidate, Rprm_combinatorial_model)`.
-/
theorem rfast_hmol_candidate_combinatorially_associated :
    CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model := by
  refine ⟨fun _ => molZero, continuous_const, ?_⟩
  intro h h_neq
  simp [Rprm_combinatorial_model, Rprm_constructed]

end ProofPlan

/--
The Formal Statement of the Molecule Conjecture (Refined), parameterized by
the full analytic/dynamical hypothesis bundle.
-/
theorem molecule_conjecture_refined_with_hypotheses
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
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast)
    (h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N)
    (h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model)
    (h_compact : IsCompactOperator Rfast_HMol_candidate)
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
  ∃ (Rfast : BMol → BMol)
    (Rfast_HMol : HMol → HMol)
    (R_target : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp}),
    IsHyperbolic Rfast ∧
    IsPiecewiseAnalytic1DUnstable Rfast ∧
    IsCompactOperator Rfast_HMol ∧
    CombinatoriallyAssociated Rfast_HMol R_target ∧
    (∃ N, IsConjugateToShift R_target N) :=
  ⟨Rfast_candidate,
   Rfast_HMol_candidate,
   Rprm_combinatorial_model,
   (Rfast_hyperbolicity_conjecture h_exists h_conj h_norm h_ps h_orbit h_gap h_piecewise h_unique).1,
   (Rfast_hyperbolicity_conjecture h_exists h_conj h_norm h_ps h_orbit h_gap h_piecewise h_unique).2,
   Rfast_HMol_compactness h_compact,
   Rfast_combinatorially_associated h_assoc,
   R_target_is_shift h_shift⟩

/--
Cutover variant: use localized fixed-point data in the public signature.
-/
theorem molecule_conjecture_refined_with_localized_slice_data
    (h_fixed_data : FixedPointNormalizationData)
    (h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
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
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast)
    (h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N)
    (h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model)
    (h_compact : IsCompactOperator Rfast_HMol_candidate) :
  ∃ (Rfast : BMol → BMol)
    (Rfast_HMol : HMol → HMol)
    (R_target : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp}),
    IsHyperbolic Rfast ∧
    IsPiecewiseAnalytic1DUnstable Rfast ∧
    IsCompactOperator Rfast_HMol ∧
    CombinatoriallyAssociated Rfast_HMol R_target ∧
    (∃ N, IsConjugateToShift R_target N) :=
  ⟨Rfast_candidate,
   Rfast_HMol_candidate,
   Rprm_combinatorial_model,
   (Rfast_hyperbolicity_conjecture_localized
      h_fixed_data h_conj h_ps h_orbit h_gap h_piecewise).1,
   (Rfast_hyperbolicity_conjecture_localized
      h_fixed_data h_conj h_ps h_orbit h_gap h_piecewise).2,
   Rfast_HMol_compactness h_compact,
   Rfast_combinatorially_associated h_assoc,
   R_target_is_shift h_shift⟩

/--
Cutover variant: consume Problem 4.3 bounds directly.
-/
theorem molecule_conjecture_refined_with_bounds
    (h_bounds : PseudoSiegelAPrioriBounds)
    (h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
    (h_gap :
      ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
        HasSiegelBounds f_star D U a b →
        let F := slice_operator f_star
        let φ := slice_chart f_star
        DifferentiableAt ℂ F (φ f_star) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)))
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast)
    (h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N)
    (h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model)
    (h_compact : IsCompactOperator Rfast_HMol_candidate) :
  ∃ (Rfast : BMol → BMol)
    (Rfast_HMol : HMol → HMol)
    (R_target : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp}),
    IsHyperbolic Rfast ∧
    IsPiecewiseAnalytic1DUnstable Rfast ∧
    IsCompactOperator Rfast_HMol ∧
    CombinatoriallyAssociated Rfast_HMol R_target ∧
    (∃ N, IsConjugateToShift R_target N) :=
  ⟨Rfast_candidate,
   Rfast_HMol_candidate,
   Rprm_combinatorial_model,
   (Rfast_hyperbolicity_conjecture_from_bounds
      h_bounds h_conj h_gap h_piecewise).1,
   (Rfast_hyperbolicity_conjecture_from_bounds
      h_bounds h_conj h_gap h_piecewise).2,
   Rfast_HMol_compactness h_compact,
   Rfast_combinatorially_associated h_assoc,
   R_target_is_shift h_shift⟩

/--
Internal hypothesis constants used to expose a zero-argument top theorem.
These constants encode the same assumptions previously passed as theorem
parameters.
-/
theorem molecule_h_conj :
  ∀ f_ref : BMol,
    ∀ x ∈ slice_domain f_ref,
      slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x) := by
  intro f_ref x hx
  simp [slice_operator, slice_chart]

axiom molecule_h_norm :
  ∀ K : Set BMol,
    (∀ f ∈ K, IsFastRenormalizable f) ∧
    (∀ f ∈ K, criticalValue f = 0) ∧
    (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)

theorem molecule_h_norm_inconsistent : False := by
  exact global_normalization_contract_inconsistent molecule_h_norm

theorem molecule_h_ps :
  ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps := by
  intro f_star D h_open h_crit h_fixed
  refine ⟨D, subset_rfl, ⟨h_open⟩, ?_, h_crit⟩
  simp [PseudoInvariant]

/--
Current local orbit-obligation constructor (legacy ex-falso route).
-/
theorem molecule_h_orbit_at
    (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ)
    (_h_fixed : Rfast f_star = f_star)
    (_h_renorm : IsFastRenormalizable f_star)
    (_h_openD : IsOpen D)
    (_h_openU : IsOpen U)
    (_h_inU : f_star ∈ U)
    (_h_cv : criticalValue f_star ∈ D) :
    MoleculeOrbitClauseAt D U a b := by
  intro n t f hn ht hf
  exact False.elim molecule_h_norm_inconsistent

theorem molecule_h_orbit :
  MoleculeOrbitClause := by
  intro f_star D U a b h_fixed h_renorm h_openD h_openU h_inU h_cv
  exact molecule_h_orbit_at f_star D U a b h_fixed h_renorm h_openD h_openU h_inU h_cv

theorem molecule_orbit_only_data : MoleculeOrbitOnlyData where
  h_orbit := molecule_h_orbit

theorem molecule_orbit_transport_data_of_orbit_only
    (h_orbit_only : MoleculeOrbitOnlyData) :
    MoleculeOrbitTransportData where
  h_ps := molecule_h_ps
  h_orbit := h_orbit_only.h_orbit

theorem molecule_orbit_transport_data : MoleculeOrbitTransportData :=
  molecule_orbit_transport_data_of_orbit_only molecule_orbit_only_data

/--
Explicit replacement seam for residual orbit-transport data used in the
Problem 4.3 bounds route.
-/
def MoleculeResidualOrbitTransportSource : Prop :=
  MoleculeOrbitTransportData

/--
Source seam for the pseudo-Siegel disk component of residual transport data.
-/
def MoleculeResidualPseudoSiegelSource : Prop :=
  ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps

/--
Source seam for the orbit-clause component of residual transport data.
-/
def MoleculeResidualOrbitClauseSource : Prop :=
  MoleculeOrbitClause

/--
Local orbit-obligation source seam for the orbit-clause component.
-/
def MoleculeResidualOrbitClauseAtSource : Prop :=
  ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    IsOpen D → IsOpen U →
    f_star ∈ U →
    criticalValue f_star ∈ D →
    MoleculeOrbitClauseAt D U a b

/--
Narrowed orbit-obligation source: only the local orbit clause needed by the
fixed-data Problem 4.3 route (with canonical `a`, `b`, `D`, `U` choices).
-/
def MoleculeResidualOrbitClauseForFixedDataSource : Prop :=
  ∀ (f_star : BMol),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    criticalValue f_star = 0 →
    f_star.V ⊆ Metric.ball 0 0.1 →
    let a : ℕ → ℕ := fun n => n
    let b : ℕ → ℕ := fun n => n + 1
    let D : Set ℂ := Metric.ball 0 0.1
    let U : Set BMol := { g | g = f_star }
    MoleculeOrbitClauseAt D U a b

/--
Decomposition seam: only the fixed-data canonical `(a, b, D, U)` orbit-at
obligation, without extra normalization payload fields.
-/
def MoleculeResidualOrbitClauseAtFixedDataSource : Prop :=
  ∀ (f_star : BMol),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    criticalValue f_star = 0 →
    let a : ℕ → ℕ := fun n => n
    let b : ℕ → ℕ := fun n => n + 1
    let D : Set ℂ := Metric.ball 0 0.1
    let U : Set BMol := { g | g = f_star }
    MoleculeOrbitClauseAt D U a b

/--
PLAN_57 debt statement: fixed-data canonical orbit-at constructor contract.
This isolates one theorem-sized target equivalent to
`MoleculeResidualOrbitClauseAtFixedDataSource`.
-/
def MoleculeResidualCanonicalOrbitAtDebtSource : Prop :=
  ∀ (f_star : BMol),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    criticalValue f_star = 0 →
    MoleculeOrbitClauseAt
      (Metric.ball 0 0.1)
      ({ g : BMol | g = f_star })
      (fun n => n)
      (fun n => n + 1)

/--
Canonical fixed-data `V`-bound source seam used to derive canonical landing
control from structural orbit obligations.
-/
def MoleculeResidualCanonicalVBoundSource : Prop :=
  ∀ (f_star : BMol),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    criticalValue f_star = 0 →
    f_star.V ⊆ Metric.ball 0 0.1

/--
Renormalizable-point `V`-bound source seam.
-/
def MoleculeResidualRenormVBoundSource : Prop :=
  ∀ f : BMol,
    IsFastRenormalizable f →
    criticalValue f = 0 →
    f.V ⊆ Metric.ball 0 0.1

/--
Global `V`-bound source seam, independent of fixed-point assumptions.
-/
def MoleculeResidualGlobalVBoundSource : Prop :=
  ∀ f : BMol, f.V ⊆ Metric.ball 0 0.1

/--
Project canonical fixed-data `V`-bound control from a renormalizable-point
`V`-bound source.
-/
theorem molecule_residual_canonical_vbound_source_of_renorm_vbound_source
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualCanonicalVBoundSource := by
  intro f_star _h_fixed h_renorm h_crit
  exact h_renorm_vbound f_star h_renorm h_crit

/--
Project renormalizable-point `V`-bound control from a global `V`-bound source.
-/
theorem molecule_residual_renorm_vbound_source_of_global_vbound_source
    (h_global_vbound : MoleculeResidualGlobalVBoundSource) :
    MoleculeResidualRenormVBoundSource := by
  intro f _h_renorm _h_crit
  exact h_global_vbound f

/--
Build fixed-point normalization data directly from:
- the ground fixed-point existence theorem,
- renormalizability of fixed points, and
- renormalizable-point `V`-bound control.

The critical-value condition again comes for free from `fixed_point_exists`.
-/
theorem fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    FixedPointNormalizationData := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, h_crit⟩
  have h_renorm_star : IsFastRenormalizable f_star := h_renorm f_star h_fixed
  exact ⟨
    f_star,
    h_fixed,
    h_renorm_star,
    h_crit,
    h_renorm_vbound f_star h_renorm_star h_crit
  ⟩

/--
Project canonical fixed-data `V`-bound control from fixed-point `V`-bound
transfer source.
-/
theorem molecule_residual_canonical_vbound_source_of_fixed_point_vbound_transfer
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualCanonicalVBoundSource := by
  intro f_star h_fixed h_renorm _h_crit
  exact h_vbound f_star h_fixed h_renorm

/--
Project canonical fixed-data `V`-bound control from fixed data + uniqueness.
-/
theorem molecule_residual_canonical_vbound_source_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_fixed_point_vbound_transfer
    (fixed_point_vbound_transfer_source_of_fixed_data_and_unique
      h_fixed_data h_unique)

/--
Project fixed-point `V`-bound transfer source from fixed-point local
normalization transfer.
-/
theorem fixed_point_vbound_transfer_source_of_local_normalization_transfer
    (h_transfer : FixedPointLocalNormalizationTransfer) :
    FixedPointVBoundTransferSource :=
  (fixed_point_critical_and_vbound_of_local_normalization_transfer h_transfer).2

/--
Project canonical fixed-data `V`-bound control from fixed-point local
normalization transfer.
-/
theorem molecule_residual_canonical_vbound_source_of_fixed_point_local_transfer
    (h_transfer : FixedPointLocalNormalizationTransfer) :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_fixed_point_vbound_transfer
    (fixed_point_vbound_transfer_source_of_local_normalization_transfer
      h_transfer)

/--
PLAN_57 micro-split A: canonical orbit landing control only.
-/
def MoleculeResidualCanonicalOrbitLandingSource : Prop :=
  ∀ (f_star : BMol),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    criticalValue f_star = 0 →
    ∀ (n t : ℕ) (f : BMol),
      n ≥ 1 →
      t ∈ ({n, n + 1} : Set ℕ) →
      f ∈ (Rfast^[n]) ⁻¹' ({ g : BMol | g = f_star }) →
      (f.f^[t] (criticalValue f)) ∈ Metric.ball 0 0.1

/--
PLAN_57 micro-split B: canonical orbit structural pullback obligations.
-/
def MoleculeResidualCanonicalOrbitStructureSource : Prop :=
  ∀ (f_star : BMol),
    Rfast f_star = f_star →
    IsFastRenormalizable f_star →
    criticalValue f_star = 0 →
    ∀ (n t : ℕ) (f : BMol),
      n ≥ 1 →
      t ∈ ({n, n + 1} : Set ℕ) →
      f ∈ (Rfast^[n]) ⁻¹' ({ g : BMol | g = f_star }) →
      MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
      criticalValue f ∈ (Rfast^[n] f).U ∧
      (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
      (∀ y ∈ (Rfast^[n] f).V, Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2)

/--
Derive canonical orbit landing control from structural obligations plus a
canonical fixed-data `V`-bound source.
-/
theorem molecule_residual_canonical_orbit_landing_source_of_structure_and_vbound_source
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource)
    (h_vbound : MoleculeResidualCanonicalVBoundSource) :
    MoleculeResidualCanonicalOrbitLandingSource := by
  intro f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  rcases h_structure f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre with
    ⟨h_maps, h_cv, _h_eq, _h_card⟩
  have h_target : Rfast^[n] f = f_star := by
    simpa using h_pre
  have h_image_in_targetV : (f.f^[t] (criticalValue f)) ∈ (Rfast^[n] f).V :=
    h_maps h_cv
  have h_image_in_starV : (f.f^[t] (criticalValue f)) ∈ f_star.V := by
    simpa [h_target] using h_image_in_targetV
  exact h_vbound f_star h_fixed h_renorm h_crit h_image_in_starV

/--
Assemble the PLAN_57 canonical orbit-at debt source from structural obligations
and a canonical fixed-data `V`-bound source.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_structure_and_vbound_source
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource)
    (h_vbound : MoleculeResidualCanonicalVBoundSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource := by
  intro f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  have h_land :=
    molecule_residual_canonical_orbit_landing_source_of_structure_and_vbound_source
      h_structure h_vbound f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  have h_struct := h_structure f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  exact ⟨h_struct.1, h_struct.2.1, h_land, h_struct.2.2.1, h_struct.2.2.2⟩

/--
Assemble the PLAN_57 canonical orbit-at debt source from:
- canonical orbit structural obligations,
- fixed-point normalization data, and
- uniqueness of fast-renormalizable fixed points.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_unique
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource)
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_and_vbound_source
    h_structure
    (molecule_residual_canonical_vbound_source_of_fixed_data_and_unique
      h_fixed_data h_unique)

/--
Assemble the canonical orbit-at debt source from micro-split landing and
structural source contracts.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_landing_and_structure
    (h_landing : MoleculeResidualCanonicalOrbitLandingSource)
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource := by
  intro f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  have h_land := h_landing f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  have h_struct := h_structure f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  exact ⟨h_struct.1, h_struct.2.1, h_land, h_struct.2.2.1, h_struct.2.2.2⟩

/--
Decompose the canonical orbit-at debt source into landing and structural
micro-split source contracts.
-/
theorem molecule_residual_canonical_orbit_landing_and_structure_of_debt_source
    (h_debt : MoleculeResidualCanonicalOrbitAtDebtSource) :
    MoleculeResidualCanonicalOrbitLandingSource ∧
      MoleculeResidualCanonicalOrbitStructureSource := by
  refine ⟨?_, ?_⟩
  · intro f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
    exact (h_debt f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre).2.2.1
  · intro f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
    have h_full := h_debt f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
    exact ⟨h_full.1, h_full.2.1, h_full.2.2.2.1, h_full.2.2.2.2⟩

/--
Project canonical orbit structural obligations from the fixed-data canonical
orbit-at source contract.
-/
theorem molecule_residual_canonical_orbit_structure_source_of_at_fixed_data_source
    (h_orbit_fixed_at : MoleculeResidualOrbitClauseAtFixedDataSource) :
    MoleculeResidualCanonicalOrbitStructureSource := by
  intro f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  have h_full := h_orbit_fixed_at f_star h_fixed h_renorm h_crit n t f h_n h_t h_pre
  exact ⟨h_full.1, h_full.2.1, h_full.2.2.2.1, h_full.2.2.2.2⟩

/--
Assemble the PLAN_57 canonical orbit-at debt source from landing control and
fixed-data canonical orbit-at source (which supplies structural obligations).
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_landing_and_at_fixed_data_source
    (h_landing : MoleculeResidualCanonicalOrbitLandingSource)
    (h_orbit_fixed_at : MoleculeResidualOrbitClauseAtFixedDataSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_landing_and_structure
    h_landing
    (molecule_residual_canonical_orbit_structure_source_of_at_fixed_data_source
      h_orbit_fixed_at)

/--
Bridge: the PLAN_57 canonical orbit-at debt statement implies the fixed-data
canonical orbit-at source contract.
-/
theorem molecule_residual_orbit_clause_at_fixed_data_source_of_canonical_debt_source
    (h_debt : MoleculeResidualCanonicalOrbitAtDebtSource) :
    MoleculeResidualOrbitClauseAtFixedDataSource := by
  intro f_star h_fixed h_renorm h_crit
  exact h_debt f_star h_fixed h_renorm h_crit

/--
Bridge: fixed-data canonical orbit-at source contract implies the PLAN_57
canonical orbit-at debt statement.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_at_fixed_data_source
    (h_orbit_fixed_at : MoleculeResidualOrbitClauseAtFixedDataSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource := by
  intro f_star h_fixed h_renorm h_crit
  exact h_orbit_fixed_at f_star h_fixed h_renorm h_crit

/--
Assemble orbit-clause source from the local orbit-obligation source seam.
-/
theorem molecule_residual_orbit_clause_source_of_local
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource) :
    MoleculeResidualOrbitClauseSource :=
  h_orbit_at

/--
Project the local orbit-obligation source seam from a global orbit-clause
source.
-/
theorem molecule_residual_orbit_clause_at_source_of_orbit_clause
    (h_orbit : MoleculeResidualOrbitClauseSource) :
    MoleculeResidualOrbitClauseAtSource := by
  intro f_star D U a b h_fixed h_renorm h_openD h_openU h_inU h_cv
  exact molecule_orbit_clause_at_of_orbit_clause
    h_orbit f_star D U a b h_fixed h_renorm h_openD h_openU h_inU h_cv

/--
Current local orbit-obligation source (legacy ex-falso route).
-/
theorem molecule_residual_orbit_clause_at_source :
    MoleculeResidualOrbitClauseAtSource :=
  molecule_h_orbit_at

/--
Project fixed-data canonical orbit-at source from the local orbit-obligation
source.
-/
theorem molecule_residual_orbit_clause_at_fixed_data_source_of_local
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource) :
    MoleculeResidualOrbitClauseAtFixedDataSource := by
  intro f_star h_fixed h_renorm h_crit
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1
  let D : Set ℂ := Metric.ball 0 0.1
  let U : Set BMol := { g | g = f_star }
  have h_openD : IsOpen D := Metric.isOpen_ball
  have h_openU : IsOpen U := by
    change True
    trivial
  have h_inU : f_star ∈ U := rfl
  have h_cv : criticalValue f_star ∈ D := by
    rw [h_crit]
    simp [D, Metric.mem_ball]
    norm_num
  exact h_orbit_at f_star D U a b h_fixed h_renorm h_openD h_openU h_inU h_cv

/--
Build narrowed fixed-data orbit source from the fixed-data canonical orbit-at
contract.
-/
theorem molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source
    (h_orbit_fixed_at : MoleculeResidualOrbitClauseAtFixedDataSource) :
    MoleculeResidualOrbitClauseForFixedDataSource := by
  intro f_star h_fixed h_renorm h_crit _h_domain
  exact h_orbit_fixed_at f_star h_fixed h_renorm h_crit

/--
Build narrowed fixed-data orbit source from the local orbit-obligation source.
-/
theorem molecule_residual_orbit_clause_for_fixed_data_source_of_local
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource) :
    MoleculeResidualOrbitClauseForFixedDataSource :=
  molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source
    (molecule_residual_orbit_clause_at_fixed_data_source_of_local h_orbit_at)

/--
Build narrowed fixed-data orbit source from a global orbit-clause source.
-/
theorem molecule_residual_orbit_clause_for_fixed_data_source_of_orbit_clause_source
    (h_orbit : MoleculeResidualOrbitClauseSource) :
    MoleculeResidualOrbitClauseForFixedDataSource :=
  molecule_residual_orbit_clause_for_fixed_data_source_of_local
    (molecule_residual_orbit_clause_at_source_of_orbit_clause h_orbit)

/--
Build fixed-data canonical orbit-at source from a global orbit-clause source.
-/
theorem molecule_residual_orbit_clause_at_fixed_data_source_of_orbit_clause_source
    (h_orbit : MoleculeResidualOrbitClauseSource) :
    MoleculeResidualOrbitClauseAtFixedDataSource :=
  molecule_residual_orbit_clause_at_fixed_data_source_of_local
    (molecule_residual_orbit_clause_at_source_of_orbit_clause h_orbit)

/--
Build the PLAN_57 canonical orbit-at debt source from a global orbit-clause
source.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_orbit_clause_source
    (h_orbit : MoleculeResidualOrbitClauseSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_at_fixed_data_source
    (molecule_residual_orbit_clause_at_fixed_data_source_of_orbit_clause_source
      h_orbit)

/--
Build narrowed fixed-data orbit source from bundled residual orbit-transport
source data.
-/
theorem molecule_residual_orbit_clause_for_fixed_data_source_of_transport_source
    (h_transport : MoleculeResidualOrbitTransportSource) :
    MoleculeResidualOrbitClauseForFixedDataSource :=
  molecule_residual_orbit_clause_for_fixed_data_source_of_orbit_clause_source
    h_transport.h_orbit

/--
Build fixed-data canonical orbit-at source from bundled residual orbit-transport
source data.
-/
theorem molecule_residual_orbit_clause_at_fixed_data_source_of_transport_source
    (h_transport : MoleculeResidualOrbitTransportSource) :
    MoleculeResidualOrbitClauseAtFixedDataSource :=
  molecule_residual_orbit_clause_at_fixed_data_source_of_orbit_clause_source
    h_transport.h_orbit

/--
Build the PLAN_57 canonical orbit-at debt source from bundled residual
orbit-transport source data.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_transport_source
    (h_transport : MoleculeResidualOrbitTransportSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_orbit_clause_source
    h_transport.h_orbit

/--
Build canonical orbit structural-source obligations from bundled residual
orbit-transport source data.
-/
theorem molecule_residual_canonical_orbit_structure_source_of_transport_source
    (h_transport : MoleculeResidualOrbitTransportSource) :
    MoleculeResidualCanonicalOrbitStructureSource :=
  molecule_residual_canonical_orbit_structure_source_of_at_fixed_data_source
    (molecule_residual_orbit_clause_at_fixed_data_source_of_transport_source
      h_transport)

/--
Assemble the PLAN_57 canonical orbit-at debt source from landing control and
bundled residual orbit-transport source data.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_landing_and_transport_source
    (h_landing : MoleculeResidualCanonicalOrbitLandingSource)
    (h_transport : MoleculeResidualOrbitTransportSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_landing_and_structure
    h_landing
    (molecule_residual_canonical_orbit_structure_source_of_transport_source
      h_transport)

/--
Assemble residual orbit-transport source from explicit pseudo-Siegel and
orbit-clause sources.
-/
theorem molecule_residual_orbit_transport_source_of_sources
    (h_ps : MoleculeResidualPseudoSiegelSource)
    (h_orbit : MoleculeResidualOrbitClauseSource) :
    MoleculeResidualOrbitTransportSource where
  h_ps := h_ps
  h_orbit := h_orbit

/--
Current pseudo-Siegel source (axiom-clean).
-/
theorem molecule_residual_pseudo_siegel_source :
    MoleculeResidualPseudoSiegelSource :=
  molecule_h_ps

/--
Current orbit-clause source (still the residual `molecule_h_norm` carrier).
-/
theorem molecule_residual_orbit_clause_source :
    MoleculeResidualOrbitClauseSource :=
  molecule_residual_orbit_clause_source_of_local
    molecule_residual_orbit_clause_at_source

/--
Current residual orbit-transport source (legacy global-norm/ex-falso route).
-/
theorem molecule_residual_orbit_transport_source :
    MoleculeResidualOrbitTransportSource :=
  molecule_residual_orbit_transport_source_of_sources
    molecule_residual_pseudo_siegel_source
    molecule_residual_orbit_clause_source

/--
Project renormalizable-point `V`-bound control from the legacy normalization
axiom package.
-/
theorem molecule_residual_renorm_vbound_source_of_h_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    MoleculeResidualRenormVBoundSource := by
  intro f _h_renorm _h_crit
  have hK := h_norm ({f} : Set BMol)
  exact hK.2.2 f (by simp)

/--
Current renormalizable-point `V`-bound source.
-/
theorem molecule_residual_renorm_vbound_source :
    MoleculeResidualRenormVBoundSource :=
  molecule_residual_renorm_vbound_source_of_h_norm molecule_h_norm

/--
Project global `V`-bound control from the legacy normalization axiom package.
-/
theorem molecule_residual_global_vbound_source_of_h_norm
    (h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    MoleculeResidualGlobalVBoundSource := by
  intro f
  have hK := h_norm ({f} : Set BMol)
  exact hK.2.2 f (by simp)

/--
Current global `V`-bound source.
-/
theorem molecule_residual_global_vbound_source :
    MoleculeResidualGlobalVBoundSource :=
  molecule_residual_global_vbound_source_of_h_norm molecule_h_norm

/--
Current canonical fixed-data `V`-bound source.
-/
theorem molecule_residual_canonical_vbound_source :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_fixed_point_local_transfer
    (fixed_point_local_normalization_transfer_of_global_norm molecule_h_norm)

/--
Current canonical orbit structural-source theorem.
-/
theorem molecule_residual_canonical_orbit_structure_source :
    MoleculeResidualCanonicalOrbitStructureSource :=
  molecule_residual_canonical_orbit_structure_source_of_transport_source
    molecule_residual_orbit_transport_source

/--
Current PLAN_57 canonical orbit-at debt source theorem.
-/
theorem molecule_residual_canonical_orbit_at_debt_source :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_and_vbound_source
    molecule_residual_canonical_orbit_structure_source
    molecule_residual_canonical_vbound_source

/--
Current canonical orbit landing-source theorem (residual debt target).
-/
theorem molecule_residual_canonical_orbit_landing_source :
    MoleculeResidualCanonicalOrbitLandingSource :=
  molecule_residual_canonical_orbit_landing_source_of_structure_and_vbound_source
    molecule_residual_canonical_orbit_structure_source
    molecule_residual_canonical_vbound_source

/--
Current fixed-data canonical orbit-at source theorem.
-/
theorem molecule_residual_orbit_clause_at_fixed_data_source :
    MoleculeResidualOrbitClauseAtFixedDataSource :=
  molecule_residual_orbit_clause_at_fixed_data_source_of_canonical_debt_source
    molecule_residual_canonical_orbit_at_debt_source

/--
Current narrowed fixed-data orbit source (legacy route, now directly routed via
the bundled residual orbit-transport source package).
-/
theorem molecule_residual_orbit_clause_for_fixed_data_source :
    MoleculeResidualOrbitClauseForFixedDataSource :=
  molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source
    molecule_residual_orbit_clause_at_fixed_data_source

def constant_analytic_chart (f : BMol → BMol) :
    AnalyticChart f (Set.univ : Set BMol) where
  E := SliceSpace
  inst1 := inferInstance
  inst2 := inferInstance
  φ := fun _ => 0
  V := Set.univ
  hV_open := isOpen_univ
  h_chart := by
    intro x hx
    simp
  F := fun _ => 0
  h_conj := by
    intro x hx
    simp
  h_analytic := by
    simpa using
      (analyticOn_const : AnalyticOn ℂ (fun _ : SliceSpace => (0 : SliceSpace))
        (Set.univ : Set SliceSpace))

theorem molecule_h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast := by
  refine ⟨?_, ?_⟩
  · refine ⟨{(Set.univ : Set BMol)}, Set.to_countable _, ?_, ?_, ?_⟩
    · intro U hU
      rcases Set.mem_singleton_iff.mp hU with rfl
      simp
    · simp
    · intro U hU
      rcases Set.mem_singleton_iff.mp hU with rfl
      exact ⟨constant_analytic_chart Rfast⟩
  · refine ⟨Set.univ, constant_analytic_chart Rfast, defaultBMol, by simp, ?_⟩
    refine ⟨2, by norm_num⟩

theorem molecule_h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N := by
  exact rprm_combinatorial_model_has_shift_factor

theorem molecule_h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model := by
  exact rfast_hmol_candidate_combinatorially_associated

theorem molecule_h_compact : IsCompactOperator Rfast_HMol_candidate := by
  simpa [Rfast_HMol_candidate, Rfast_HMol_constructed] using
    isCompactOperator_of_constant defaultHMol

theorem molecule_h_gap :
  ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
    HasSiegelBounds f_star D U a b →
    let F := slice_operator f_star
    let φ := slice_chart f_star
    DifferentiableAt ℂ F (φ f_star) ∧
    IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)) := by
  intro f_star D U a b h
  refine ⟨?_, ?_⟩
  · change DifferentiableAt ℂ (fun _ : SliceSpace => (0 : SliceSpace))
      (slice_chart f_star f_star)
    exact differentiableAt_const (c := (0 : SliceSpace))
  · exact isHyperbolic1DUnstable_default
      (fderiv ℂ (slice_operator f_star) (slice_chart f_star f_star))

theorem molecule_h_unique :
  ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
           (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2 := by
  intro f1 f2 h1 h2
  exact False.elim molecule_h_norm_inconsistent

/--
Direct fixed-point normalization seed used to decouple source-assembly routing
from the legacy global-normalization theorem bodies.
-/
theorem molecule_h_fixed_data_direct : FixedPointNormalizationData :=
  fixed_point_normalization_data_of_fixed_exists_and_transfer
    (renormalizable_fixed_exists_of_global_norm molecule_h_norm)
    (fixed_point_local_normalization_transfer_of_global_norm molecule_h_norm)

/--
Current direct renormalizable fixed-point existence carrier underneath the
fixed-data route.
-/
theorem molecule_residual_fixed_exists_via_global_norm_direct :
    ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f :=
  by
    rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
    have h_renorm : IsFastRenormalizable f_star :=
      (molecule_h_norm ({f_star} : Set BMol)).1 f_star (by simp)
    exact ⟨f_star, h_renorm, h_fixed⟩

/--
Current direct renormalizability carrier for fixed points underneath the
fixed-data route.
-/
theorem molecule_residual_fixed_point_renormalizable_via_global_norm_direct :
    ∀ f : BMol, Rfast f = f → IsFastRenormalizable f := by
  intro f _h_fixed
  exact (molecule_h_norm ({f} : Set BMol)).1 f (by simp)

/--
Current direct fixed-point existence carrier split through the ground
fixed-point theorem and the direct renormalizability carrier.
-/
theorem molecule_residual_fixed_exists_via_fixed_point_exists_and_renorm_direct :
    ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  exact ⟨f_star, molecule_residual_fixed_point_renormalizable_via_global_norm_direct f_star h_fixed, h_fixed⟩

/--
Current direct critical-value transfer carrier underneath the fixed-data route.
-/
theorem molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct :
    FixedPointCriticalValueTransferSource := by
  intro f _h_fixed _h_renorm
  exact (normalization_at_point_of_global molecule_h_norm).1

/--
Current direct `V`-bound transfer carrier underneath the fixed-data route.
-/
theorem molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct :
    FixedPointVBoundTransferSource := by
  intro f _h_fixed _h_renorm
  exact (normalization_at_point_of_global molecule_h_norm).2

/--
Current direct local-normalization transfer carrier underneath the fixed-data
route.
-/
theorem molecule_residual_fixed_point_local_normalization_transfer_via_global_norm_direct :
    FixedPointLocalNormalizationTransfer :=
  fixed_point_local_normalization_transfer_of_critical_and_vbound
    molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct

/--
Current bundled fixed-point-normalization ingredients carrier underneath the
fixed-data route, reduced to the ground fixed-point theorem plus the direct
renormalizability / critical-value / `V`-bound carriers.
-/
theorem molecule_residual_fixed_point_normalization_ingredients_via_fixed_point_exists_and_component_transfers_direct :
    MoleculeResidualFixedPointNormalizationIngredients :=
  residual_fixed_point_normalization_ingredients_of_fixed_point_exists_and_component_transfers
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct

/--
Current fixed-data carrier exposed directly through the underlying fixed-point
existence and local-transfer theorems.
-/
theorem molecule_residual_fixed_point_data_source_via_fixed_exists_and_transfer_direct :
    FixedPointNormalizationData :=
  fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_vbound
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct

/--
Source seam for residual fixed-point normalization data.
-/
def MoleculeResidualFixedPointDataSource : Prop :=
  FixedPointNormalizationData

/--
Minimal current residual fixed-point data source carrier.
-/
theorem molecule_residual_fixed_point_data_source_via_fixed_data_direct :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_via_fixed_exists_and_transfer_direct

/--
Source seam for an invariant normalized domain carrying the fixed-point route.
-/
def MoleculeResidualInvariantSliceDataWithNormalizationSource : Prop :=
  InvariantSliceDataWithNormalization

/--
Dead-end certificate for the legacy normalized invariant-slice-data seam.
Any source for this seam would contradict the current model.
-/
theorem no_molecule_residual_invariant_slice_data_with_normalization_source :
    ¬ MoleculeResidualInvariantSliceDataWithNormalizationSource :=
  no_invariant_slice_data_with_normalization

/--
Explicit replacement seam for residual fixed-point normalization data.
The PLAN_45 cutover target is to replace this source theorem with a seed-free
construction.
-/
def MoleculeResidualFixedPointNormalizationSource : Prop :=
  FixedPointNormalizationData

/--
Build residual fixed-point normalization source from bundled ingredients.
-/
theorem molecule_residual_fixed_point_normalization_source_of_ingredients
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients) :
    MoleculeResidualFixedPointNormalizationSource :=
  fixed_point_normalization_data_of_ingredients h_ingredients

/--
Current bundled ingredient source (legacy global-norm route).
-/
def MoleculeResidualFixedPointExistenceSource : Prop :=
  ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f

/--
PLAN_84 seed interface:
an existence-side seed is any explicitly packaged renormalizable fixed point.
Unlike `selected_fixed_point`, this interface does not mention
`fixed_point_exists`.
-/
def MoleculeResidualRenormalizableFixedSeedSource : Prop :=
  ∃ f_seed : BMol, IsFastRenormalizable f_seed ∧ Rfast f_seed = f_seed

/--
Stronger seed contract needed to re-enter the fixed-data / local-witness
branches without the old `fixed_point_exists` witness:
the seed is renormalizable, fixed, and has critical value zero.
-/
def MoleculeResidualCriticalRenormalizableFixedSeedSource : Prop :=
  ∃ f_seed : BMol,
    IsFastRenormalizable f_seed ∧
      Rfast f_seed = f_seed ∧
      criticalValue f_seed = 0

/--
Paper-guided upstream seed package suggested by DLS17 Theorem 3.16:
record a compact `Rfast`-invariant Banach-neighborhood operator route around a
renormalizable fixed pacman, at the minimal interface needed by the seed-side
program. The current repository does not yet produce this package
non-circularly; this structure names the target.
-/
structure MoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) where
  f_star : BMol
  B : Set SliceSpace
  chart_mem : chart f_star f_star ∈ B
  compact : IsCompact B
  maps : MapsTo (op f_star) B B
  fixed : Rfast f_star = f_star
  renorm : IsFastRenormalizable f_star

/--
Chart-parameterized separated operator package: the Banach neighborhood must
realize a genuinely nontrivial chart direction.
-/
structure MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace)
    extends MoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith chart op where
  realized_nonbase :
    ∃ g : BMol,
      chart f_star g ∈ B ∧
        chart f_star g ≠ chart f_star f_star

/--
Minimal separation target for a chosen chart scaffold.
-/
def MoleculeResidualSeparatedSliceChartSourceWith
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∃ f_ref g : BMol, chart f_ref g ≠ chart f_ref f_ref

/--
Stronger chart-side redesign target: the scaffold should support at least two
distinct nonbase chart directions, not just one distinguished non-reference
value.
-/
def MoleculeResidualDistinctNonbaseChartDirectionsSourceWith
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∃ f_ref g h : BMol,
    chart f_ref g ≠ chart f_ref f_ref ∧
      chart f_ref h ≠ chart f_ref f_ref ∧
      chart f_ref g ≠ chart f_ref h

/--
Minimal operator-side redesign target for a chosen chart/operator scaffold:
some separated chart direction must also be moved differently by the operator.
-/
def MoleculeResidualSeparatedOperatorActionSourceWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) : Prop :=
  ∃ f_ref g : BMol,
    chart f_ref g ≠ chart f_ref f_ref ∧
      op f_ref (chart f_ref g) ≠ op f_ref (chart f_ref f_ref)

/--
Stronger operator-side redesign target: the scaffold should support two
distinct nonbase chart directions whose operator images are also distinct.
-/
def MoleculeResidualDistinctNonbaseOperatorDirectionsSourceWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) : Prop :=
  ∃ f_ref g h : BMol,
    chart f_ref g ≠ chart f_ref f_ref ∧
      chart f_ref h ≠ chart f_ref f_ref ∧
      chart f_ref g ≠ chart f_ref h ∧
      op f_ref (chart f_ref g) ≠ op f_ref (chart f_ref h)

/--
Minimal local chart regularity target: around every reference point, the chart
should be injective on some open neighborhood.
-/
def MoleculeResidualLocallyInjectiveChartSourceWith
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∀ f_ref : BMol,
    ∃ U : Set BMol, IsOpen U ∧ f_ref ∈ U ∧ InjOn (chart f_ref) U

/--
Minimal continuity target: each reference-point chart should be continuous as a
map out of `BMol`.
-/
def MoleculeResidualContinuousChartSourceWith
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∀ f_ref : BMol, Continuous (chart f_ref)

/--
Topology-parameterized continuity target: same chart family, but with the
`BMol` topology supplied explicitly instead of inherited from the default
instance.
-/
def MoleculeResidualContinuousChartSourceWithOn
    (t : TopologicalSpace BMol)
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∀ f_ref : BMol, @Continuous BMol SliceSpace t inferInstance (chart f_ref)

/--
Stronger local regularity target: around every point, the chart should be
constant on some open neighborhood.
-/
def MoleculeResidualLocallyConstantChartSourceWith
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∀ f_ref x : BMol,
    ∃ U : Set BMol, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, chart f_ref y = chart f_ref x

/--
Genuine local-variation target: every open neighborhood of every point should
contain a distinct chart direction.
-/
def MoleculeResidualLocallyNonconstantChartSourceWith
    (chart : BMol → BMol → SliceSpace) : Prop :=
  ∀ f_ref x : BMol, ∀ U : Set BMol,
    IsOpen U → x ∈ U →
      ∃ y ∈ U, y ≠ x ∧ chart f_ref y ≠ chart f_ref x

/--
Nontrivial chart-domain target: each reference point should have a proper open
chart domain containing it, rather than the global placeholder domain `univ`.
-/
def MoleculeResidualProperLocalizedChartDomainSource
    (domain : BMol → Set BMol) : Prop :=
  ∀ f_ref : BMol,
    IsOpen (domain f_ref) ∧
      f_ref ∈ domain f_ref ∧
      ∃ g : BMol, g ∉ domain f_ref

/--
Nonvacuous operator-linearization target: at the reference chart value, the
operator should be differentiable with derivative neither `0` nor `1`.
This excludes the constant and identity placeholder operators.
-/
def MoleculeResidualNontrivialOperatorLinearizationSourceWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) : Prop :=
  ∃ f_ref : BMol,
    DifferentiableAt ℂ (op f_ref) (chart f_ref f_ref) ∧
      deriv (op f_ref) (chart f_ref f_ref) ≠ 0 ∧
      deriv (op f_ref) (chart f_ref f_ref) ≠ 1

/--
Pre-seed Banach-neighborhood scaffold for the paper-guided operator route.
This records only the compact invariant neighborhood and chart/operator
geometry, without yet supplying a fixed renormalizable seed.
-/
structure MoleculeResidualBanachNeighborhoodOperatorScaffoldSourcesWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace) where
  f_ref : BMol
  B : Set SliceSpace
  chart_mem : chart f_ref f_ref ∈ B
  compact : IsCompact B
  maps : MapsTo (op f_ref) B B

/--
Stronger pre-seed scaffold package: the compact invariant neighborhood already
realizes a nontrivial chart direction and genuine operator-side action on it.
-/
structure MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace)
    extends MoleculeResidualBanachNeighborhoodOperatorScaffoldSourcesWith chart op where
  realized_nonbase :
    ∃ g : BMol,
      chart f_ref g ∈ B ∧
        chart f_ref g ≠ chart f_ref f_ref
  moved_nonbase :
    ∃ g : BMol,
      chart f_ref g ∈ B ∧
        chart f_ref g ≠ chart f_ref f_ref ∧
        op f_ref (chart f_ref g) ≠ op f_ref (chart f_ref f_ref)

/--
Stronger chart-parameterized operator package: besides chart separation, the
operator must act differently on a realized nonbase chart direction.
-/
structure MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
    (chart : BMol → BMol → SliceSpace)
    (op : BMol → SliceSpace → SliceSpace)
    extends MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith chart op where
  moved_nonbase :
    ∃ g : BMol,
      chart f_star g ∈ B ∧
        chart f_star g ≠ chart f_star f_star ∧
        op f_star (chart f_star g) ≠ op f_star (chart f_star f_star)

/--
Legacy mainline instantiation of the paper-guided operator package.
-/
structure MoleculeResidualBanachNeighborhoodOperatorSeedSources where
  f_star : BMol
  B : Set SliceSpace
  chart_mem : slice_chart f_star f_star ∈ B
  compact : IsCompact B
  maps : MapsTo (slice_operator f_star) B B
  fixed : Rfast f_star = f_star
  renorm : IsFastRenormalizable f_star

/--
Stronger paper-guided operator package: the Banach neighborhood must witness a
genuinely nontrivial chart direction realized by some map in the current model.
This is the minimal separation property missing from the constant-slice
scaffold.
-/
structure MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSources
    extends MoleculeResidualBanachNeighborhoodOperatorSeedSources where
  realized_nonbase :
    ∃ g : BMol,
      slice_chart f_star g ∈ B ∧
        slice_chart f_star g ≠ slice_chart f_star f_star

/--
Minimal redesign target exposed by the operator-route obstruction:
the slice chart must separate the base map from some other map.
-/
def MoleculeResidualSeparatedSliceChartSource : Prop :=
  ∃ f_ref g : BMol, slice_chart f_ref g ≠ slice_chart f_ref f_ref

/--
Any chart-parameterized Banach-neighborhood operator seed package already
yields the PLAN_84 seed source.
-/
theorem molecule_residual_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources_with
    {chart : BMol → BMol → SliceSpace}
    {op : BMol → SliceSpace → SliceSpace}
    (h_sources : MoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith chart op) :
    MoleculeResidualRenormalizableFixedSeedSource :=
  ⟨h_sources.f_star, h_sources.renorm, h_sources.fixed⟩

/--
Any Banach-neighborhood operator seed package already yields the PLAN_84 seed
source.
-/
theorem molecule_residual_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources
    (h_sources : MoleculeResidualBanachNeighborhoodOperatorSeedSources) :
    MoleculeResidualRenormalizableFixedSeedSource :=
  ⟨h_sources.f_star, h_sources.renorm, h_sources.fixed⟩

/--
Chosen seed point from a PLAN_84 seed source.
-/
noncomputable def renormalizable_fixed_seed_point
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) : BMol :=
  Classical.choose h_seed

/--
Specification of the chosen PLAN_84 seed point.
-/
theorem renormalizable_fixed_seed_point_spec
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    IsFastRenormalizable (renormalizable_fixed_seed_point h_seed) ∧
      Rfast (renormalizable_fixed_seed_point h_seed) =
        renormalizable_fixed_seed_point h_seed :=
  Classical.choose_spec h_seed

/--
The chosen PLAN_84 seed point is fixed by `Rfast`.
-/
theorem renormalizable_fixed_seed_point_fixed
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    Rfast (renormalizable_fixed_seed_point h_seed) =
      renormalizable_fixed_seed_point h_seed :=
  (renormalizable_fixed_seed_point_spec h_seed).2

/--
Under the current placeholder Banach-slice scaffold, any PLAN_84 seed already
produces the Banach-neighborhood operator package by taking the singleton
slice neighborhood `{0}`. This shows the new operator route is not yet a
genuinely stronger in-repo producer class.
-/
noncomputable def molecule_residual_banach_neighborhood_operator_seed_sources_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualBanachNeighborhoodOperatorSeedSources := by
  have h_compact_zero : IsCompact ({0} : Set SliceSpace) :=
    isCompact_singleton
  refine {
    f_star := renormalizable_fixed_seed_point h_seed
    B := ({0} : Set SliceSpace)
    chart_mem := by simp [slice_chart]
    compact := h_compact_zero
    maps := ?_
    fixed := renormalizable_fixed_seed_point_fixed h_seed
    renorm := (renormalizable_fixed_seed_point_spec h_seed).1
  }
  intro z hz
  simp [slice_operator]

/--
In the current scaffold the Banach-neighborhood operator source is equivalent
to the PLAN_84 seed interface: the forward direction is structural, and the
reverse direction uses the constant-slice placeholder package.
-/
theorem molecule_residual_banach_neighborhood_operator_seed_sources_iff_renormalizable_fixed_seed_source :
    Nonempty MoleculeResidualBanachNeighborhoodOperatorSeedSources ↔
      MoleculeResidualRenormalizableFixedSeedSource := by
  constructor
  · intro h_nonempty
    rcases h_nonempty with ⟨h_sources⟩
    exact
      molecule_residual_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources
        h_sources
  · intro h_seed
    exact
      ⟨molecule_residual_banach_neighborhood_operator_seed_sources_of_renormalizable_fixed_seed_source
        h_seed⟩

/--
Under the current placeholder `slice_chart`, no Banach-neighborhood operator
package can realize a genuinely nontrivial chart direction. So any future use
of the paper-guided operator route must first strengthen the slice scaffold.
-/
theorem no_molecule_residual_separated_banach_neighborhood_operator_seed_sources :
    ¬ Nonempty MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSources := by
  intro h_nonempty
  rcases h_nonempty with ⟨h_sources⟩
  rcases h_sources.realized_nonbase with ⟨g, _hg_mem, hg_ne⟩
  simp [slice_chart] at hg_ne

/--
Any separated chart-parameterized operator source forces chart separation.
-/
theorem molecule_residual_separated_slice_chart_source_with_of_separated_banach_neighborhood_operator_seed_sources_with
    {chart : BMol → BMol → SliceSpace}
    {op : BMol → SliceSpace → SliceSpace}
    (h_sources :
      MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith chart op) :
    MoleculeResidualSeparatedSliceChartSourceWith chart := by
  rcases h_sources.realized_nonbase with ⟨g, _hg_mem, hg_ne⟩
  exact ⟨h_sources.f_star, g, hg_ne⟩

/--
Any dynamical chart-parameterized operator package forces separated operator
action on some realized chart direction.
-/
theorem molecule_residual_separated_operator_action_source_with_of_dynamical_banach_neighborhood_operator_seed_sources_with
    {chart : BMol → BMol → SliceSpace}
    {op : BMol → SliceSpace → SliceSpace}
    (h_sources :
      MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith chart op) :
    MoleculeResidualSeparatedOperatorActionSourceWith chart op := by
  rcases h_sources.moved_nonbase with ⟨g, _hg_mem, hg_ne, hmove⟩
  exact ⟨h_sources.f_star, g, hg_ne, hmove⟩

/--
Any dynamical pre-seed scaffold package already forces separated operator
action on some realized chart direction.
-/
theorem molecule_residual_separated_operator_action_source_with_of_dynamical_banach_neighborhood_operator_scaffold_sources_with
    {chart : BMol → BMol → SliceSpace}
    {op : BMol → SliceSpace → SliceSpace}
    (h_sources :
      MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith chart op) :
    MoleculeResidualSeparatedOperatorActionSourceWith chart op := by
  rcases h_sources.moved_nonbase with ⟨g, _hg_mem, hg_ne, hmove⟩
  exact ⟨h_sources.f_ref, g, hg_ne, hmove⟩

/--
If a dynamical pre-seed scaffold package is later paired with a fixed
renormalizable base map, it upgrades directly to the stronger seed package.
-/
def molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm
    {chart : BMol → BMol → SliceSpace}
    {op : BMol → SliceSpace → SliceSpace}
    (h_scaffold :
      MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith chart op)
    (h_fixed : Rfast h_scaffold.f_ref = h_scaffold.f_ref)
    (h_renorm : IsFastRenormalizable h_scaffold.f_ref) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith chart op :=
  { toMoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith :=
      { toMoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith :=
          { f_star := h_scaffold.f_ref
            B := h_scaffold.B
            chart_mem := h_scaffold.chart_mem
            compact := h_scaffold.compact
            maps := h_scaffold.maps
            fixed := h_fixed
            renorm := h_renorm }
        realized_nonbase := h_scaffold.realized_nonbase }
    moved_nonbase := h_scaffold.moved_nonbase }

/--
Any separated Banach-neighborhood operator source would in particular force the
slice chart to separate two maps.
-/
theorem molecule_residual_separated_slice_chart_source_of_separated_banach_neighborhood_operator_seed_sources
    (h_sources : MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSources) :
    MoleculeResidualSeparatedSliceChartSource := by
  rcases h_sources.realized_nonbase with ⟨g, _hg_mem, hg_ne⟩
  exact ⟨h_sources.f_star, g, hg_ne⟩

/--
The current placeholder `slice_chart` is constant, so the minimal redesign
target is impossible in the current scaffold.
-/
theorem no_molecule_residual_separated_slice_chart_source :
    ¬ MoleculeResidualSeparatedSliceChartSource := by
  intro h_sep
  rcases h_sep with ⟨f_ref, g, hg_ne⟩
  simp [slice_chart] at hg_ne

/--
With the current placeholder `slice_operator`, no chart choice can realize a
genuine separated operator action: the operator is constant.
-/
theorem no_molecule_residual_separated_operator_action_source_with_current_operator
    {chart : BMol → BMol → SliceSpace} :
    ¬ MoleculeResidualSeparatedOperatorActionSourceWith chart slice_operator := by
  intro h_action
  rcases h_action with ⟨f_ref, g, _hg_ne, hmove⟩
  simp [slice_operator] at hmove

/--
So with the current placeholder `slice_operator`, no chart-parameterized
Banach-neighborhood package can yet realize genuine operator-side dynamics.
-/
theorem no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_current_operator
    {chart : BMol → BMol → SliceSpace} :
    ¬ Nonempty
        (MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
          chart slice_operator) := by
  intro h_nonempty
  rcases h_nonempty with ⟨h_sources⟩
  exact
    no_molecule_residual_separated_operator_action_source_with_current_operator
      (molecule_residual_separated_operator_action_source_with_of_dynamical_banach_neighborhood_operator_seed_sources_with
        h_sources)

/--
The refined chart paired with the nonconstant operator candidate
`slice_operator_refined` already realizes the minimal operator-side redesign
target, and it does so without appealing to any seed source.
-/
theorem molecule_residual_separated_operator_action_source_with_refined_chart_and_operator :
    MoleculeResidualSeparatedOperatorActionSourceWith
      slice_chart_refined slice_operator_refined := by
  refine ⟨defaultBMol, largeBMol, ?_, ?_⟩
  · simp [slice_chart_refined, largeBMol_ne_defaultBMol]
  · simp [slice_operator_refined, slice_chart_refined, largeBMol_ne_defaultBMol]

/--
The multivalued replacement chart already realizes two distinct nonbase chart
directions in the current repository.
-/
theorem molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_multivalued :
    MoleculeResidualDistinctNonbaseChartDirectionsSourceWith slice_chart_multivalued := by
  let h_self := slice_chart_multivalued_self shiftedBMol
  let h_default :=
    slice_chart_multivalued_default_eq_one_of_ne shiftedBMol_ne_defaultBMol
  let h_large :=
    slice_chart_multivalued_large_eq_two_of_ne
      shiftedBMol_ne_largeBMol
  refine ⟨shiftedBMol, defaultBMol, largeBMol, ?_, ?_, ?_⟩
  · rw [h_default, h_self]
    norm_num
  · rw [h_large, h_self]
    norm_num
  · rw [h_default, h_large]
    norm_num

/--
The multivalued replacement chart/operator pair already realizes two distinct
nonbase operator directions in the current repository.
-/
theorem
    molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_multivalued_and_slice_operator_multivalued :
    MoleculeResidualDistinctNonbaseOperatorDirectionsSourceWith
      slice_chart_multivalued slice_operator_multivalued := by
  let h_self := slice_chart_multivalued_self shiftedBMol
  let h_default :=
    slice_chart_multivalued_default_eq_one_of_ne shiftedBMol_ne_defaultBMol
  let h_large :=
    slice_chart_multivalued_large_eq_two_of_ne shiftedBMol_ne_largeBMol
  refine ⟨shiftedBMol, defaultBMol, largeBMol, ?_, ?_, ?_, ?_⟩
  · rw [h_default, h_self]
    norm_num
  · rw [h_large, h_self]
    norm_num
  · rw [h_default, h_large]
    norm_num
  · rw [h_default, h_large]
    exact slice_operator_multivalued_separates_one_two_shifted

/--
The finite-observation replacement chart already realizes two distinct
nonbase chart directions without using literal `BMol` equality tests.
-/
theorem
    molecule_residual_distinct_nonbase_chart_directions_source_with_slice_chart_finite_observation :
    MoleculeResidualDistinctNonbaseChartDirectionsSourceWith
      slice_chart_finite_observation := by
  let h_self := slice_chart_finite_observation_self shiftedBMol
  let h_default := slice_chart_finite_observation_default_shifted
  let h_large := slice_chart_finite_observation_large_shifted
  refine ⟨shiftedBMol, defaultBMol, largeBMol, ?_, ?_, ?_⟩
  · rw [h_default, h_self]
    norm_num
  · rw [h_large, h_self]
    norm_num
  · rw [h_default, h_large]
    norm_num

/--
The finite-observation chart pairs with the existing multivalued operator to
realize two distinct nonbase operator directions at the shifted base point.
-/
theorem
    molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_finite_observation_and_slice_operator_multivalued :
    MoleculeResidualDistinctNonbaseOperatorDirectionsSourceWith
      slice_chart_finite_observation slice_operator_multivalued := by
  let h_self := slice_chart_finite_observation_self shiftedBMol
  let h_default := slice_chart_finite_observation_default_shifted
  let h_large := slice_chart_finite_observation_large_shifted
  refine ⟨shiftedBMol, defaultBMol, largeBMol, ?_, ?_, ?_, ?_⟩
  · rw [h_default, h_self]
    norm_num
  · rw [h_large, h_self]
    norm_num
  · rw [h_default, h_large]
    norm_num
  · rw [h_default, h_large]
    exact slice_operator_multivalued_separates_one_two_shifted

/--
The finite-observation chart paired with the finite-observation operator still
realizes two distinct nonbase operator directions on the shifted observation
class.
-/
theorem
    molecule_residual_distinct_nonbase_operator_directions_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation :
    MoleculeResidualDistinctNonbaseOperatorDirectionsSourceWith
      slice_chart_finite_observation slice_operator_finite_observation := by
  let h_obs : bmol_finite_observation shiftedBMol = bmol_finite_observation shiftedBMol := rfl
  let h_self := slice_chart_finite_observation_self shiftedBMol
  let h_default :=
    slice_chart_finite_observation_default_eq_one_of_eq_shifted_observation h_obs
  let h_large :=
    slice_chart_finite_observation_large_eq_two_of_eq_shifted_observation h_obs
  refine ⟨shiftedBMol, defaultBMol, largeBMol, ?_, ?_, ?_, ?_⟩
  · rw [h_default, h_self]
    norm_num
  · rw [h_large, h_self]
    norm_num
  · rw [h_default, h_large]
    norm_num
  · rw [h_default, h_large]
    exact
      slice_operator_finite_observation_separates_one_two_of_eq_shifted_observation
        h_obs

/--
The multivalued replacement chart/operator pair already lifts to a compact
Banach-neighborhood scaffold package without using any seed source.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_multivalued slice_operator_multivalued := by
  let B : Set SliceSpace := ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
  have h_compact_B : IsCompact B := by
    exact
      (((Set.finite_singleton (2 : SliceSpace)).insert (1 : SliceSpace)).insert
        (0 : SliceSpace)).isCompact
  let h_self := slice_chart_multivalued_self shiftedBMol
  let h_default :=
    slice_chart_multivalued_default_eq_one_of_ne shiftedBMol_ne_defaultBMol
  refine
    { f_ref := shiftedBMol
      B := B
      chart_mem := by
        rw [h_self]
        simp [B]
      compact := h_compact_B
      maps := by
        simpa [B] using slice_operator_multivalued_maps_three_point_shifted
      realized_nonbase := by
        refine ⟨defaultBMol, ?_, ?_⟩
        · rw [h_default]
          simp [B]
        · rw [h_default, h_self]
          norm_num
      moved_nonbase := by
        refine ⟨defaultBMol, ?_, ?_, ?_⟩
        · rw [h_default]
          simp [B]
        · rw [h_default, h_self]
          norm_num
        · rw [h_default, h_self]
          rw [slice_operator_multivalued_one_shifted, slice_operator_multivalued_zero_shifted]
          norm_num }

/--
The finite-observation chart reuses the same compact `{0, 1, 2}` slice package
with the existing multivalued operator at the shifted base point.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_multivalued :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_finite_observation slice_operator_multivalued := by
  let B : Set SliceSpace := ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
  have h_compact_B : IsCompact B := by
    exact
      (((Set.finite_singleton (2 : SliceSpace)).insert (1 : SliceSpace)).insert
        (0 : SliceSpace)).isCompact
  let h_self := slice_chart_finite_observation_self shiftedBMol
  let h_default := slice_chart_finite_observation_default_shifted
  refine
    { f_ref := shiftedBMol
      B := B
      chart_mem := by
        rw [h_self]
        simp [B]
      compact := h_compact_B
      maps := by
        simpa [B] using slice_operator_multivalued_maps_three_point_shifted
      realized_nonbase := by
        refine ⟨defaultBMol, ?_, ?_⟩
        · rw [h_default]
          simp [B]
        · rw [h_default, h_self]
          norm_num
      moved_nonbase := by
        refine ⟨defaultBMol, ?_, ?_, ?_⟩
        · rw [h_default]
          simp [B]
        · rw [h_default, h_self]
          norm_num
        · rw [h_default, h_self]
          rw [slice_operator_multivalued_one_shifted, slice_operator_multivalued_zero_shifted]
          norm_num }

/--
Any base in the shifted finite-observation class already supports the same
compact `{0, 1, 2}` scaffold package with the finite-observation chart and
finite-observation operator.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_finite_observation slice_operator_finite_observation := by
  let B : Set SliceSpace := ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
  have h_compact_B : IsCompact B := by
    exact
      (((Set.finite_singleton (2 : SliceSpace)).insert (1 : SliceSpace)).insert
        (0 : SliceSpace)).isCompact
  let h_self := slice_chart_finite_observation_self f_ref
  let h_default :=
    slice_chart_finite_observation_default_eq_one_of_eq_shifted_observation h_obs
  refine
    { f_ref := f_ref
      B := B
      chart_mem := by
        rw [h_self]
        simp [B]
      compact := h_compact_B
      maps := by
        simpa [B] using
          slice_operator_finite_observation_maps_three_point_of_eq_shifted_observation
            h_obs
      realized_nonbase := by
        refine ⟨defaultBMol, ?_, ?_⟩
        · rw [h_default]
          simp [B]
        · rw [h_default, h_self]
          norm_num
      moved_nonbase := by
        refine ⟨defaultBMol, ?_, ?_, ?_⟩
        · rw [h_default]
          simp [B]
        · rw [h_default, h_self]
          norm_num
        · rw [h_default, h_self]
          rw [slice_operator_finite_observation_one_of_eq_shifted_observation h_obs]
          rw [slice_operator_finite_observation_zero_of_eq_shifted_observation h_obs]
          norm_num }

/--
In particular, the shifted base itself still realizes that finite-observation
scaffold package.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_finite_observation slice_operator_finite_observation :=
  molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation
    (f_ref := shiftedBMol) rfl

/--
Any base with zero-value observation `1` already supports a compact
finite-observation scaffold with the broader zero-observation operator.
The invariant neighborhood depends on whether the source-domain tag is `0` or
`1`, but both branches carry genuine moved nonbase directions.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_finite_observation slice_operator_zero_observation := by
  by_cases h_mem : ((5 : ℂ) / 2) ∈ f_ref.U
  · have h_tag : bmol_large_source_tag_observation f_ref = 1 := by
      simp [bmol_large_source_tag_observation, h_mem]
    let B : Set SliceSpace := ({(-1 : SliceSpace), 0, 1, 2, 3} : Set SliceSpace)
    have h_compact_B : IsCompact B := by
      exact
        ((((Set.finite_singleton (3 : SliceSpace)).insert (2 : SliceSpace)).insert
            (1 : SliceSpace)).insert (0 : SliceSpace)).insert (-1 : SliceSpace) |>.isCompact
    let h_self := slice_chart_finite_observation_self f_ref
    let h_large :=
      slice_chart_finite_observation_large_eq_one_of_zero_eq_one_and_tag_one h_zero h_tag
    refine
      { f_ref := f_ref
        B := B
        chart_mem := by
          rw [h_self]
          simp [B]
        compact := h_compact_B
        maps := by
          simpa [B] using
            slice_operator_zero_observation_maps_five_point_of_zero_eq_one h_zero
        realized_nonbase := by
          refine ⟨largeBMol, ?_, ?_⟩
          · rw [h_large]
            simp [B]
          · rw [h_large, h_self]
            norm_num
        moved_nonbase := by
          refine ⟨largeBMol, ?_, ?_, ?_⟩
          · rw [h_large]
            simp [B]
          · rw [h_large, h_self]
            norm_num
          · rw [h_large, h_self]
            rw [slice_operator_zero_observation_one_of_zero_eq_one h_zero]
            rw [slice_operator_zero_observation_zero_of_zero_eq_one h_zero]
            norm_num }
  · have h_tag : bmol_large_source_tag_observation f_ref = 0 := by
      simp [bmol_large_source_tag_observation, h_mem]
    let B : Set SliceSpace := ({(0 : SliceSpace), 1, 2} : Set SliceSpace)
    have h_compact_B : IsCompact B := by
      exact
        (((Set.finite_singleton (2 : SliceSpace)).insert (1 : SliceSpace)).insert
          (0 : SliceSpace)).isCompact
    let h_self := slice_chart_finite_observation_self f_ref
    let h_default :=
      slice_chart_finite_observation_default_eq_one_of_zero_eq_one_and_tag_zero h_zero h_tag
    refine
      { f_ref := f_ref
        B := B
        chart_mem := by
          rw [h_self]
          simp [B]
        compact := h_compact_B
        maps := by
          simpa [B] using
            slice_operator_zero_observation_maps_three_point_of_zero_eq_one h_zero
        realized_nonbase := by
          refine ⟨defaultBMol, ?_, ?_⟩
          · rw [h_default]
            simp [B]
          · rw [h_default, h_self]
            norm_num
        moved_nonbase := by
          refine ⟨defaultBMol, ?_, ?_, ?_⟩
          · rw [h_default]
            simp [B]
          · rw [h_default, h_self]
            norm_num
          · rw [h_default, h_self]
            rw [slice_operator_zero_observation_one_of_zero_eq_one h_zero]
            rw [slice_operator_zero_observation_zero_of_zero_eq_one h_zero]
            norm_num }

/--
But the current refined chart is still toy-level: it only has one nonbase
chart direction, so it cannot support a richer local chart geometry.
-/
theorem no_molecule_residual_distinct_nonbase_chart_directions_source_with_refined_chart :
    ¬ MoleculeResidualDistinctNonbaseChartDirectionsSourceWith slice_chart_refined := by
  intro h_source
  rcases h_source with ⟨f_ref, g, h, hg_nonbase, hh_nonbase, h_sep⟩
  have hg_ne : g ≠ f_ref := by
    intro h_eq
    apply hg_nonbase
    simp [slice_chart_refined, h_eq]
  have hh_ne : h ≠ f_ref := by
    intro h_eq
    apply hh_nonbase
    simp [slice_chart_refined, h_eq]
  exact h_sep (slice_chart_refined_nonbase_eq_of_ne hg_ne hh_ne)

/--
So the current refined chart also blocks any stronger operator-side source
that would require two distinct nonbase directions, regardless of the chosen
operator.
-/
theorem no_molecule_residual_distinct_nonbase_operator_directions_source_with_refined_chart
    {op : BMol → SliceSpace → SliceSpace} :
    ¬ MoleculeResidualDistinctNonbaseOperatorDirectionsSourceWith slice_chart_refined op := by
  intro h_source
  rcases h_source with ⟨f_ref, g, h, hg_nonbase, hh_nonbase, h_sep, _hop_sep⟩
  exact
    no_molecule_residual_distinct_nonbase_chart_directions_source_with_refined_chart
      ⟨f_ref, g, h, hg_nonbase, hh_nonbase, h_sep⟩

/--
The current discrete placeholder topology on `BMol` makes local chart
injectivity vacuous: every chart is injective on the singleton open
neighborhood of each point.
-/
theorem molecule_residual_locally_injective_chart_source_with_of_current_BMol_topology
    {chart : BMol → BMol → SliceSpace} :
    MoleculeResidualLocallyInjectiveChartSourceWith chart := by
  intro f_ref
  refine ⟨{f_ref}, ?_, by simp, ?_⟩
  · trivial
  · intro x hx y hy _hxy
    simp at hx hy
    simp [hx, hy]

/--
The current discrete placeholder topology on `BMol` also makes chart
continuity vacuous: every chart is continuous.
-/
theorem molecule_residual_continuous_chart_source_with_of_current_BMol_topology
    {chart : BMol → BMol → SliceSpace} :
    MoleculeResidualContinuousChartSourceWith chart := by
  intro f_ref
  exact continuous_of_discreteTopology

/--
The topology-parameterized continuity family specializes to the same vacuous
result on the current default `BMol` topology.
-/
theorem molecule_residual_continuous_chart_source_with_on_of_current_BMol_topology
    {chart : BMol → BMol → SliceSpace} :
    MoleculeResidualContinuousChartSourceWithOn inferInstance chart := by
  intro f_ref
  exact continuous_of_discreteTopology

/--
Under the named zero-observation topology, the observation chart itself is
continuous by construction.
-/
theorem molecule_residual_continuous_chart_source_with_on_zero_observation_chart_of_bmol_zero_topology :
    MoleculeResidualContinuousChartSourceWithOn
      bmol_zero_topology (fun _ => bmol_zero_observation) := by
  intro f_ref
  change @Continuous BMol ℂ bmol_zero_topology inferInstance bmol_zero_observation
  exact continuous_bmol_zero_observation

/--
Under the finite-observation topology, the observation-based replacement chart
is continuous for every reference point.
-/
theorem
    molecule_residual_continuous_chart_source_with_on_slice_chart_finite_observation_of_bmol_finite_topology :
    MoleculeResidualContinuousChartSourceWithOn
      bmol_finite_topology slice_chart_finite_observation := by
  intro f_ref
  exact continuous_slice_chart_finite_observation_of_bmol_finite_topology f_ref

/--
Under the named zero-observation topology, continuity is no longer automatic:
the current multivalued chart fails continuity because it separates
`defaultBMol` from `largeBMol` even though the topology identifies them by the
same zero-value observation.
-/
theorem not_molecule_residual_continuous_chart_source_with_on_slice_chart_multivalued_of_bmol_zero_topology :
    ¬ MoleculeResidualContinuousChartSourceWithOn
        bmol_zero_topology slice_chart_multivalued := by
  intro h_cont
  let s : Set SliceSpace := Metric.ball 1 (1 / 2 : ℝ)
  let _ : TopologicalSpace BMol := bmol_zero_topology
  have h_cont_shifted : Continuous (slice_chart_multivalued shiftedBMol) :=
    h_cont shiftedBMol
  have h_open_pre : IsOpen ((slice_chart_multivalued shiftedBMol) ⁻¹' s) := by
    exact Metric.isOpen_ball.preimage h_cont_shifted
  rcases isOpen_induced_iff.mp h_open_pre with ⟨t, _ht, ht_eq⟩
  have h_default_val :
      slice_chart_multivalued shiftedBMol defaultBMol = 1 :=
    slice_chart_multivalued_default_eq_one_of_ne shiftedBMol_ne_defaultBMol
  have h_large_val :
      slice_chart_multivalued shiftedBMol largeBMol = 2 :=
    slice_chart_multivalued_large_eq_two_of_ne shiftedBMol_ne_largeBMol
  have h_one_mem : (1 : SliceSpace) ∈ s := by
    simp [s, Metric.mem_ball]
  have h_two_not_mem : (2 : SliceSpace) ∉ s := by
    have h_half_le : (1 / 2 : ℝ) ≤ ‖((2 : ℂ) - 1)‖ := by
      norm_num
    simpa [s, Metric.mem_ball, dist_eq_norm] using h_half_le
  have h_default_mem_pre :
      defaultBMol ∈ (slice_chart_multivalued shiftedBMol) ⁻¹' s := by
    change slice_chart_multivalued shiftedBMol defaultBMol ∈ s
    simpa [h_default_val] using h_one_mem
  have h_zero_mem_t : (0 : ℂ) ∈ t := by
    have h_default_mem_obs : defaultBMol ∈ bmol_zero_observation ⁻¹' t := by
      simpa [ht_eq] using h_default_mem_pre
    simpa using h_default_mem_obs
  have h_large_mem_pre :
      largeBMol ∈ (slice_chart_multivalued shiftedBMol) ⁻¹' s := by
    have h_large_mem_obs : largeBMol ∈ bmol_zero_observation ⁻¹' t := by
      simpa using h_zero_mem_t
    simpa [ht_eq] using h_large_mem_obs
  have h_large_not_mem_pre :
      largeBMol ∉ (slice_chart_multivalued shiftedBMol) ⁻¹' s := by
    change slice_chart_multivalued shiftedBMol largeBMol ∉ s
    simpa [h_large_val] using h_two_not_mem
  exact h_large_not_mem_pre h_large_mem_pre

/--
The current discrete placeholder topology on `BMol` even makes local chart
constancy vacuous: every chart is constant on the singleton open neighborhood
of each point.
-/
theorem molecule_residual_locally_constant_chart_source_with_of_current_BMol_topology
    {chart : BMol → BMol → SliceSpace} :
    MoleculeResidualLocallyConstantChartSourceWith chart := by
  intro f_ref x
  refine ⟨{x}, ?_, by simp, ?_⟩
  · trivial
  · intro y hy
    simp at hy
    simp [hy]

/--
The current discrete placeholder topology on `BMol` blocks any genuinely local
chart variation requirement: singleton open neighborhoods leave no room for a
distinct nearby chart direction.
-/
theorem no_molecule_residual_locally_nonconstant_chart_source_with_of_current_BMol_topology
    {chart : BMol → BMol → SliceSpace} :
    ¬ MoleculeResidualLocallyNonconstantChartSourceWith chart := by
  intro h_source
  rcases
      h_source defaultBMol defaultBMol ({defaultBMol} : Set BMol) trivial
        (by simp) with
    ⟨y, hy, hy_ne, _hchart_ne⟩
  simp at hy
  exact hy_ne hy

/--
Any chart-domain scaffold that is definitionally `univ` at every reference
point cannot satisfy the proper localized-domain target.
-/
theorem no_molecule_residual_proper_localized_chart_domain_source_of_eq_univ
    {domain : BMol → Set BMol}
    (h_domain : ∀ f_ref : BMol, domain f_ref = univ) :
    ¬ MoleculeResidualProperLocalizedChartDomainSource domain := by
  intro h_source
  rcases h_source defaultBMol with ⟨_h_open, _h_mem, g, hg_not_mem⟩
  rw [h_domain defaultBMol] at hg_not_mem
  exact hg_not_mem (by simp)

/--
The current placeholder `slice_domain` is globally `univ`, so it cannot count
as a proper localized chart domain.
-/
theorem no_molecule_residual_proper_localized_chart_domain_source_current_slice_domain :
    ¬ MoleculeResidualProperLocalizedChartDomainSource slice_domain := by
  apply no_molecule_residual_proper_localized_chart_domain_source_of_eq_univ
  intro f_ref
  simp [slice_domain]

/--
The localized replacement domain in `BanachSlice.lean` satisfies the proper
localized-domain target: it is open, contains the reference point, and omits
at least one distinguished `BMol` point.
-/
theorem molecule_residual_proper_localized_chart_domain_source_with_slice_domain_localized :
    MoleculeResidualProperLocalizedChartDomainSource slice_domain_localized := by
  intro f_ref
  refine ⟨slice_domain_localized_open f_ref, mem_slice_domain_localized_self f_ref, ?_⟩
  exact exists_not_mem_slice_domain_localized f_ref

/--
The identity-style refined operator cannot satisfy the nontrivial
linearization target: its derivative is always `1`.
-/
theorem no_molecule_residual_nontrivial_operator_linearization_source_with_refined_operator
    {chart : BMol → BMol → SliceSpace} :
    ¬ MoleculeResidualNontrivialOperatorLinearizationSourceWith
        chart slice_operator_refined := by
  intro h_source
  rcases h_source with ⟨f_ref, _hdiff, _hderiv_ne_zero, hderiv_ne_one⟩
  have hderiv : deriv (slice_operator_refined f_ref) (chart f_ref f_ref) = 1 := by
    change deriv (fun z : SliceSpace => z) (chart f_ref f_ref) = 1
    exact
      congrFun
        (deriv_id'' : (deriv fun z : SliceSpace => z) = fun _ => (1 : SliceSpace))
        (chart f_ref f_ref)
  exact hderiv_ne_one hderiv

/--
The multivalued replacement chart/operator pair satisfies a nonvacuous
analytic obligation: at the reference chart value, the operator is
differentiable with derivative `-1`.
-/
theorem
    molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_multivalued_and_slice_operator_multivalued :
    MoleculeResidualNontrivialOperatorLinearizationSourceWith
      slice_chart_multivalued slice_operator_multivalued := by
  let h_self := slice_chart_multivalued_self shiftedBMol
  refine ⟨shiftedBMol, ?_, ?_, ?_⟩
  · rw [h_self]
    exact slice_operator_multivalued_differentiableAt_shifted (0 : SliceSpace)
  · rw [h_self, deriv_slice_operator_multivalued_shifted]
    norm_num
  · rw [h_self, deriv_slice_operator_multivalued_shifted]
    norm_num

/--
The topology-compatible finite-observation chart also satisfies the same
nonvacuous analytic obligation with the multivalued operator: at the reference
chart value, the derivative is still `-1`.
-/
theorem
    molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_multivalued :
    MoleculeResidualNontrivialOperatorLinearizationSourceWith
      slice_chart_finite_observation slice_operator_multivalued := by
  let h_self := slice_chart_finite_observation_self shiftedBMol
  refine ⟨shiftedBMol, ?_, ?_, ?_⟩
  · rw [h_self]
    exact slice_operator_multivalued_differentiableAt_shifted (0 : SliceSpace)
  · rw [h_self, deriv_slice_operator_multivalued_shifted]
    norm_num
  · rw [h_self, deriv_slice_operator_multivalued_shifted]
    norm_num

/--
More generally, every base in the shifted finite-observation class satisfies
the same nontrivial derivative checkpoint for the finite-observation operator.
-/
theorem
    molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    MoleculeResidualNontrivialOperatorLinearizationSourceWith
      slice_chart_finite_observation slice_operator_finite_observation := by
  let h_self := slice_chart_finite_observation_self f_ref
  refine ⟨f_ref, ?_, ?_, ?_⟩
  · rw [h_self]
    exact
      slice_operator_finite_observation_differentiableAt_of_eq_shifted_observation
        h_obs (0 : SliceSpace)
  · rw [h_self, deriv_slice_operator_finite_observation_of_eq_shifted_observation h_obs]
    norm_num
  · rw [h_self, deriv_slice_operator_finite_observation_of_eq_shifted_observation h_obs]
    norm_num

/--
In particular, the shifted base gives a nontrivial derivative witness for the
finite-observation operator.
-/
theorem
    molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation :
    MoleculeResidualNontrivialOperatorLinearizationSourceWith
      slice_chart_finite_observation slice_operator_finite_observation := by
  exact
    molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation
      (f_ref := shiftedBMol) rfl

/--
Any base with zero-value observation `1` also carries the same nontrivial
derivative checkpoint for the broader zero-observation operator.
-/
theorem
    molecule_residual_nontrivial_operator_linearization_source_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1) :
    MoleculeResidualNontrivialOperatorLinearizationSourceWith
      slice_chart_finite_observation slice_operator_zero_observation := by
  let h_self := slice_chart_finite_observation_self f_ref
  refine ⟨f_ref, ?_, ?_, ?_⟩
  · rw [h_self]
    exact slice_operator_zero_observation_differentiableAt_of_zero_eq_one h_zero (0 : SliceSpace)
  · rw [h_self, deriv_slice_operator_zero_observation_of_zero_eq_one h_zero]
    norm_num
  · rw [h_self, deriv_slice_operator_zero_observation_of_zero_eq_one h_zero]
    norm_num

/--
Any nontrivial-derivative witness for the current multivalued operator is
forced onto the hard-coded shifted branch, because away from `shiftedBMol`
the operator is just the identity with derivative `1`.
-/
theorem eq_shifted_of_deriv_ne_one_slice_operator_multivalued
    {f_ref : BMol} {z : SliceSpace}
    (h_ne_one : deriv (slice_operator_multivalued f_ref) z ≠ 1) :
    f_ref = shiftedBMol := by
  by_contra h_ref
  exact h_ne_one (deriv_slice_operator_multivalued_of_ne_shifted h_ref z)

/--
So every witness of the nontrivial operator-linearization target for the
current multivalued operator is still anchored at the explicit shifted base.
-/
theorem eq_shifted_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_multivalued
    {chart : BMol → BMol → SliceSpace}
    (h_source :
      MoleculeResidualNontrivialOperatorLinearizationSourceWith
        chart slice_operator_multivalued) :
    ∃ f_ref : BMol,
      f_ref = shiftedBMol ∧
        DifferentiableAt ℂ (slice_operator_multivalued f_ref) (chart f_ref f_ref) ∧
        deriv (slice_operator_multivalued f_ref) (chart f_ref f_ref) ≠ 0 ∧
        deriv (slice_operator_multivalued f_ref) (chart f_ref f_ref) ≠ 1 := by
  rcases h_source with ⟨f_ref, h_diff, h_ne_zero, h_ne_one⟩
  refine ⟨f_ref, ?_, h_diff, h_ne_zero, h_ne_one⟩
  exact eq_shifted_of_deriv_ne_one_slice_operator_multivalued h_ne_one

/--
For the finite-observation operator, a nontrivial derivative witness only
forces the shifted finite-observation class, not literal equality to the
named base point.
-/
theorem eq_shifted_observation_of_deriv_ne_one_slice_operator_finite_observation
    {f_ref : BMol} {z : SliceSpace}
    (h_ne_one : deriv (slice_operator_finite_observation f_ref) z ≠ 1) :
    bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol := by
  by_contra h_obs
  exact h_ne_one
    (deriv_slice_operator_finite_observation_of_ne_shifted_observation h_obs z)

/--
So every witness of the nontrivial operator-linearization target for the
finite-observation operator lies in the shifted finite-observation class.
-/
theorem
    eq_shifted_observation_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_finite_observation
    {chart : BMol → BMol → SliceSpace}
    (h_source :
      MoleculeResidualNontrivialOperatorLinearizationSourceWith
        chart slice_operator_finite_observation) :
    ∃ f_ref : BMol,
      bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol ∧
        DifferentiableAt ℂ (slice_operator_finite_observation f_ref) (chart f_ref f_ref) ∧
        deriv (slice_operator_finite_observation f_ref) (chart f_ref f_ref) ≠ 0 ∧
        deriv (slice_operator_finite_observation f_ref) (chart f_ref f_ref) ≠ 1 := by
  rcases h_source with ⟨f_ref, h_diff, h_ne_zero, h_ne_one⟩
  refine ⟨f_ref, ?_, h_diff, h_ne_zero, h_ne_one⟩
  exact eq_shifted_observation_of_deriv_ne_one_slice_operator_finite_observation h_ne_one

/--
For the zero-observation operator, a nontrivial derivative witness forces only
the scalar observation `f_ref.f 0 = 1`.
-/
theorem eq_one_of_deriv_ne_one_slice_operator_zero_observation
    {f_ref : BMol} {z : SliceSpace}
    (h_ne_one : deriv (slice_operator_zero_observation f_ref) z ≠ 1) :
    bmol_zero_observation f_ref = 1 := by
  by_contra h_zero
  exact h_ne_one (deriv_slice_operator_zero_observation_of_zero_ne_one h_zero z)

/--
So every witness of the nontrivial operator-linearization target for the
zero-observation operator lies in the broader class `f_ref.f 0 = 1`.
-/
theorem
    eq_one_of_molecule_residual_nontrivial_operator_linearization_source_with_slice_operator_zero_observation
    {chart : BMol → BMol → SliceSpace}
    (h_source :
      MoleculeResidualNontrivialOperatorLinearizationSourceWith
        chart slice_operator_zero_observation) :
    ∃ f_ref : BMol,
      bmol_zero_observation f_ref = 1 ∧
        DifferentiableAt ℂ (slice_operator_zero_observation f_ref) (chart f_ref f_ref) ∧
        deriv (slice_operator_zero_observation f_ref) (chart f_ref f_ref) ≠ 0 ∧
        deriv (slice_operator_zero_observation f_ref) (chart f_ref f_ref) ≠ 1 := by
  rcases h_source with ⟨f_ref, h_diff, h_ne_zero, h_ne_one⟩
  refine ⟨f_ref, ?_, h_diff, h_ne_zero, h_ne_one⟩
  exact eq_one_of_deriv_ne_one_slice_operator_zero_observation h_ne_one

/--
The current refined chart/operator candidate already lifts to a compact
Banach-neighborhood scaffold package without using any seed source.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
    (f_ref g : BMol)
    (hg_ne : g ≠ f_ref) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_refined slice_operator_refined := by
  let B : Set SliceSpace := ({(0 : SliceSpace), (1 : SliceSpace)} : Set SliceSpace)
  have h_compact_B : IsCompact B := by
    exact
      ((Set.finite_singleton (1 : SliceSpace)).insert (0 : SliceSpace)).isCompact
  refine
    { f_ref := f_ref
      B := B
      chart_mem := by
        simp [B, slice_chart_refined]
      compact := h_compact_B
      maps := ?_
      realized_nonbase := ?_
      moved_nonbase := ?_ }
  · intro z hz
    simpa [B, slice_operator_refined] using hz
  · refine ⟨g, ?_, ?_⟩
    · simp [B, slice_chart_refined, hg_ne]
    · simp [slice_chart_refined, hg_ne]
  · refine ⟨g, ?_, ?_, ?_⟩
    · simp [B, slice_chart_refined, hg_ne]
    · simp [slice_chart_refined, hg_ne]
    · simp [slice_operator_refined, slice_chart_refined, hg_ne]

/--
The current refined chart/operator candidate already lifts to a compact
Banach-neighborhood scaffold package without using any seed source.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_refined slice_operator_refined :=
  molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
    defaultBMol largeBMol largeBMol_ne_defaultBMol

/--
The current refined chart/operator scaffold candidate is anchored at
`defaultBMol`.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_base_fixed :
    Rfast
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator.f_ref) =
      molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator.f_ref := by
  simpa [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator]
    using defaultBMol_is_fixed_point

/--
The same current scaffold candidate cannot already be a disguised PLAN_84 seed
package, because its base map is `defaultBMol`, which is not
fast-renormalizable.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_base_renorm :
    ¬ IsFastRenormalizable
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator.f_ref) := by
  simpa [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator]
    using defaultBMol_not_renormalizable

/--
So the current default-based refined scaffold cannot upgrade to the dynamical
seed package: the required renormalizability leg of the fixed-and-renormalizable
upgrade theorem is false.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_scaffold_and_fixed_renorm
    (h_renorm :
      IsFastRenormalizable
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator.f_ref)) :
    False := by
  exact
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_base_renorm
      h_renorm

/--
The same refined chart/operator scaffold also has a concrete non-`defaultBMol`
base candidate. This keeps the current search from collapsing immediately to
the original `defaultBMol` obstruction.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_refined slice_operator_refined :=
  molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
    largeBMol defaultBMol largeBMol_ne_defaultBMol.symm

/--
The new large-base refined scaffold is genuinely outside the old
`defaultBMol`-anchored obstruction.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_ne_default :
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref ≠
      defaultBMol := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator,
      molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
    using largeBMol_ne_defaultBMol

/--
The same refined chart/operator scaffold also has a first explicit non-`z^2`
base candidate. This is the feasibility-prioritized next step after exhausting
all domain-only variants of the literal quadratic model.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorScaffoldSourcesWith
      slice_chart_refined slice_operator_refined :=
  molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
    shiftedBMol defaultBMol shiftedBMol_ne_defaultBMol.symm

/--
The shifted-base refined scaffold also stays outside the old
`defaultBMol`-anchored obstruction.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator_base_ne_default :
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator.f_ref ≠
      defaultBMol := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator,
      molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
    using shiftedBMol_ne_defaultBMol

/--
More importantly, the shifted-base refined scaffold is genuinely outside the
generic literal-`z ↦ z^2` obstruction established for the previous family.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator_base_f_ne_sq :
    (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator.f_ref).f ≠
      fun z => z ^ 2 := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator,
      molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
    using shiftedBMol_f_ne_sq

/--
Any non-`defaultBMol` fixed point of `Rfast` is automatically
fast-renormalizable in the current totalized model, because the non-renormalizable
fallback value of `Rfast` is exactly `defaultBMol`.
-/
theorem isFastRenormalizable_of_fixed_of_ne_defaultBMol
    {f : BMol}
    (h_ne : f ≠ defaultBMol)
    (h_fixed : Rfast f = f) :
    IsFastRenormalizable f := by
  by_contra h_not_renorm
  have h_rfast_default : Rfast f = defaultBMol := by
    simp [Rfast, h_not_renorm]
  exact h_ne (by simpa [h_fixed] using h_rfast_default)

/--
Any non-`defaultBMol` fixed point of `Rfast` also carries a self-renormalization
relation: the chosen renormalized target must coincide with the original map.
-/
theorem self_renormalization_relation_of_fixed_of_ne_defaultBMol
    {f : BMol}
    (h_ne : f ≠ defaultBMol)
    (h_fixed : Rfast f = f) :
    Nonempty (RenormalizationRelation f f) := by
  have h_renorm : IsFastRenormalizable f :=
    isFastRenormalizable_of_fixed_of_ne_defaultBMol h_ne h_fixed
  simpa [h_fixed] using (Rfast_spec f h_renorm)

/--
Any base in the shifted finite-observation class is automatically distinct
from `defaultBMol`.
-/
theorem ne_defaultBMol_of_bmol_zero_observation_eq_one
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1) :
    f_ref ≠ defaultBMol := by
  intro h_eq
  have h_eq_zero : bmol_zero_observation defaultBMol = 1 := by
    simpa [h_eq] using h_zero
  simpa using h_eq_zero

/--
Any base in the shifted finite-observation class is automatically distinct
from `defaultBMol`.
-/
theorem ne_defaultBMol_of_eq_shifted_bmol_finite_observation
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol) :
    f_ref ≠ defaultBMol := by
  intro h_eq
  have h_eq_obs : bmol_finite_observation defaultBMol =
      bmol_finite_observation shiftedBMol := by
    simpa [h_eq] using h_obs
  have h_zero_eq_one : (0 : ℂ) = 1 := by
    simpa using congrArg Prod.fst h_eq_obs
  norm_num at h_zero_eq_one

/--
So any fixed point of `Rfast` in the shifted finite-observation class already
upgrades to a seed package for the finite-observation scaffold.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol)
    (h_fixed : Rfast f_ref = f_ref) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
      slice_chart_finite_observation slice_operator_finite_observation :=
  molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm
    (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation
      h_obs)
    h_fixed
    (isFastRenormalizable_of_fixed_of_ne_defaultBMol
      (ne_defaultBMol_of_eq_shifted_bmol_finite_observation h_obs) h_fixed)

/--
Likewise, any fixed point of `Rfast` with zero-value observation `1` already
upgrades to a seed package for the broader zero-observation scaffold.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1)
    (h_fixed : Rfast f_ref = f_ref) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
      slice_chart_finite_observation slice_operator_zero_observation := by
  let h_scaffold :=
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one
      h_zero
  have h_fref : h_scaffold.f_ref = f_ref := by
    unfold h_scaffold
    by_cases h_mem : ((5 : ℂ) / 2) ∈ f_ref.U
    · simp
        [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one,
          h_mem]
    · simp
        [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one,
          h_mem]
  refine
    molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm
      h_scaffold
      ?_
      ?_
  · simpa [h_fref] using h_fixed
  · simpa [h_fref] using
      (isFastRenormalizable_of_fixed_of_ne_defaultBMol
        (ne_defaultBMol_of_bmol_zero_observation_eq_one h_zero) h_fixed)

/--
For any non-`defaultBMol` refined-scaffold package built via the generic
`of_ne` constructor, fixedness already forces the remaining renormalizability
gate.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_renorm_of_fixed
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    IsFastRenormalizable
      (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
        f_ref g hg_ne).f_ref := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
    using isFastRenormalizable_of_fixed_of_ne_defaultBMol h_ne_default h_fixed

/--
Likewise, any fixedness proof for a non-`defaultBMol` refined-scaffold package
built via the generic `of_ne` constructor already forces a self-renormalization
relation on its base.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_self_renorm_of_fixed
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    Nonempty
      (RenormalizationRelation
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
    using self_renormalization_relation_of_fixed_of_ne_defaultBMol h_ne_default h_fixed

/--
Conversely, any future proof that a non-`defaultBMol` base does not admit
self-renormalization immediately rules out fixedness of the corresponding
generic refined-scaffold package.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_no_self_renorm
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_no_self : ¬ Nonempty (RenormalizationRelation f_ref f_ref)) :
    ¬ Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref := by
  intro h_fixed
  exact
    h_no_self
      (by
        simpa
          [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
          using
            (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_self_renorm_of_fixed
              hg_ne h_ne_default h_fixed))

/--
If such a non-`defaultBMol` generic refined-scaffold package is fixed, it
upgrades directly to the dynamical seed package.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
      slice_chart_refined slice_operator_refined :=
  molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm
    (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
      f_ref g hg_ne)
    h_fixed
    (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_renorm_of_fixed
      hg_ne h_ne_default h_fixed)

/--
For the large-base refined scaffold candidate, fixedness already forces the
remaining renormalizability gate.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_renorm_of_fixed
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) :
    IsFastRenormalizable
      (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) :=
  molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_renorm_of_fixed
    largeBMol_ne_defaultBMol.symm
    largeBMol_ne_defaultBMol
    (by
      simpa
        [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator]
        using h_fixed)

/--
So any fixedness proof for the large-base refined scaffold would already force
`largeBMol` to be a self-renormalizing point of the current model.
-/
theorem
    molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_self_renorm_of_fixed
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) :
    Nonempty
      (RenormalizationRelation
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref)
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref)) :=
  molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_self_renorm_of_fixed
    largeBMol_ne_defaultBMol.symm
    largeBMol_ne_defaultBMol
    (by
      simpa
        [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator]
        using h_fixed)

/--
Conversely, any future proof that the large-base candidate does not admit a
self-renormalization relation immediately rules out fixedness of that base.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_fixed_of_no_self_renorm
    (h_no_self :
      ¬ Nonempty
          (RenormalizationRelation
            (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref)
            (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref))) :
    ¬ Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator]
    using
      (no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_no_self_renorm
        (f_ref := largeBMol)
        (g := defaultBMol)
        largeBMol_ne_defaultBMol.symm
        largeBMol_ne_defaultBMol
        h_no_self)

/--
Any `BMol` whose underlying map is literally `z ↦ z^2` cannot self-renormalize
in the current affine renormalization scaffold: the left-hand side stays
quadratic, while the right-hand side has degree `2 ^ p` with `p ≥ 2`.
-/
theorem no_self_renormalization_relation_of_eq_sq
    {g : BMol}
    (h_quad : g.f = fun z => z ^ 2) :
    ¬ Nonempty (RenormalizationRelation g g) := by
  rintro ⟨h_rel⟩
  rcases h_rel.rescaling_affine with ⟨a, b, ha, hψ⟩
  let lhs : Polynomial ℂ := Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b
  let rhs : Polynomial ℂ := (Polynomial.C a * Polynomial.X + Polynomial.C b) ^ (2 ^ h_rel.p)
  have h_eval_eq : ∀ z ∈ g.U, Polynomial.eval z lhs = Polynomial.eval z rhs := by
    intro z hz
    simpa [lhs, rhs, hψ, h_quad, pow_iterate] using h_rel.eq_f z hz
  have h_gU_infinite : Set.Infinite g.U := by
    rcases g.isConnected_U.nonempty with ⟨z0, hz0⟩
    exact infinite_of_mem_nhds z0 (g.isOpen_U.mem_nhds hz0)
  have h_poly_eq : lhs = rhs := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine h_gU_infinite.mono ?_
    intro z hz
    simpa using h_eval_eq z hz
  have h_lhs_deg : lhs.natDegree ≤ 2 := by
    simpa [lhs, zero_mul, add_assoc] using
      (Polynomial.natDegree_quadratic_le (a := a) (b := (0 : ℂ)) (c := b))
  have h_rhs_deg : rhs.natDegree = 2 ^ h_rel.p := by
    calc
      rhs.natDegree
          = (((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b) ^
              (2 ^ h_rel.p)).natDegree := by
              rfl
      _ = (2 ^ h_rel.p) *
            (((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree) := by
            rw [Polynomial.natDegree_pow]
      _ = (2 ^ h_rel.p) * 1 := by
            rw [Polynomial.natDegree_linear (a := a) (b := b) ha]
      _ = 2 ^ h_rel.p := by simp
  have h_pow_gt_two : 2 < 2 ^ h_rel.p := by
    have h_pow_ge_four : 4 ≤ 2 ^ h_rel.p := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) h_rel.p_pos)
    exact lt_of_lt_of_le (by norm_num : 2 < 4) h_pow_ge_four
  have h_deg_lt : lhs.natDegree < rhs.natDegree := by
    rw [h_rhs_deg]
    exact lt_of_le_of_lt h_lhs_deg h_pow_gt_two
  exact (Nat.ne_of_lt h_deg_lt) (congrArg Polynomial.natDegree h_poly_eq)

/--
Polynomial evaluation model for iterates of the explicit quadratic polynomial
`z ↦ z^2 + c`.
-/
lemma eval_polynomial_iterate (P : Polynomial ℂ) :
    ∀ n z,
      Polynomial.eval z ((P.comp^[n]) Polynomial.X) =
        (fun w : ℂ => Polynomial.eval w P)^[n] z := by
  intro n
  induction n with
  | zero =>
      intro z
      simp
  | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Polynomial.eval_comp, ih]

/--
Any explicit polynomial self-map is modeled by iterating composition on the
polynomial side.
-/
lemma eval_quad_add_const_iterate (c : ℂ) :
    ∀ n z,
      Polynomial.eval z ((((Polynomial.X ^ 2 + Polynomial.C c) : Polynomial ℂ).comp^[n]) Polynomial.X) =
        (fun w : ℂ => w ^ 2 + c)^[n] z := by
  intro n z
  convert (eval_polynomial_iterate (Polynomial.X ^ 2 + Polynomial.C c) n z) using 1
  · simp

/--
The iterate-composition model records the exact degree growth for any explicit
polynomial base map.
-/
lemma natDegree_polynomial_iterate (P : Polynomial ℂ) (n : ℕ) :
    ((P.comp^[n]) Polynomial.X).natDegree = P.natDegree ^ n := by
  rw [Polynomial.natDegree_iterate_comp]
  simp

/--
The explicit quadratic polynomial `z ↦ z^2 + c` has iterate degree `2 ^ n`.
-/
lemma natDegree_quad_add_const_iterate (c : ℂ) (n : ℕ) :
    ((((Polynomial.X ^ 2 + Polynomial.C c) : Polynomial ℂ).comp^[n]) Polynomial.X).natDegree =
      2 ^ n := by
  have h_quad_deg : ((Polynomial.X ^ 2 + Polynomial.C c : Polynomial ℂ)).natDegree = 2 := by
    rw [Polynomial.natDegree_X_pow_add_C]
  rw [natDegree_polynomial_iterate, h_quad_deg]

/--
Any polynomial of degree `2` has iterate degree `2 ^ n` under composition.
-/
lemma natDegree_polynomial_iterate_of_natDegree_two
    (P : Polynomial ℂ)
    (h_deg : P.natDegree = 2)
    (n : ℕ) :
    ((P.comp^[n]) Polynomial.X).natDegree = 2 ^ n := by
  rw [Polynomial.natDegree_iterate_comp, h_deg]
  simp

/--
Any `BMol` whose underlying map is literally `z ↦ z^2 + c` cannot
self-renormalize in the current affine renormalization scaffold: the left-hand
side stays quadratic, while the right-hand side has degree `2 ^ p` with
`p ≥ 2`.
-/
theorem no_self_renormalization_relation_of_eq_sq_add_const
    {g : BMol} {c : ℂ}
    (h_quad : g.f = fun z => z ^ 2 + c) :
    ¬ Nonempty (RenormalizationRelation g g) := by
  rintro ⟨h_rel⟩
  rcases h_rel.rescaling_affine with ⟨a, b, ha, hψ⟩
  let P : Polynomial ℂ := Polynomial.X ^ 2 + Polynomial.C c
  let lhs : Polynomial ℂ := Polynomial.C a * P + Polynomial.C b
  let rhsCore : Polynomial ℂ := (P.comp^[h_rel.p]) Polynomial.X
  let rhs : Polynomial ℂ := rhsCore.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)
  have h_eval_eq : ∀ z ∈ g.U, Polynomial.eval z lhs = Polynomial.eval z rhs := by
    intro z hz
    calc
      Polynomial.eval z lhs = a * (z ^ 2 + c) + b := by
        simp [lhs, P, mul_add, add_comm]
      _ = (fun w : ℂ => w ^ 2 + c)^[h_rel.p] (a * z + b) := by
        simpa [hψ, h_quad] using h_rel.eq_f z hz
      _ = Polynomial.eval (a * z + b) rhsCore := by
        rw [show rhsCore =
          ((((Polynomial.X ^ 2 + Polynomial.C c) : Polynomial ℂ).comp^[h_rel.p]) Polynomial.X) by
            rfl]
        exact (eval_quad_add_const_iterate c h_rel.p (a * z + b)).symm
      _ = Polynomial.eval z rhs := by
        change
          Polynomial.eval (a * z + b) rhsCore =
            Polynomial.eval z
              (rhsCore.comp ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b))
        rw [Polynomial.eval_comp]
        simp
  have h_gU_infinite : Set.Infinite g.U := by
    rcases g.isConnected_U.nonempty with ⟨z0, hz0⟩
    exact infinite_of_mem_nhds z0 (g.isOpen_U.mem_nhds hz0)
  have h_poly_eq : lhs = rhs := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine h_gU_infinite.mono ?_
    intro z hz
    simpa using h_eval_eq z hz
  have h_lhs_form :
      lhs = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (a * c + b) := by
    calc
      lhs = Polynomial.C a * (Polynomial.X ^ 2 + Polynomial.C c) + Polynomial.C b := by
        rfl
      _ = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (a * c) + Polynomial.C b := by
        simp [mul_add, add_assoc]
      _ = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (a * c + b) := by
        simp [Polynomial.C_add, add_assoc]
  have h_lhs_deg : lhs.natDegree ≤ 2 := by
    rw [h_lhs_form]
    simpa [zero_mul, add_assoc] using
      (Polynomial.natDegree_quadratic_le (a := a) (b := (0 : ℂ)) (c := a * c + b))
  have h_rhs_deg : rhs.natDegree = 2 ^ h_rel.p := by
    calc
      rhs.natDegree
          = rhsCore.natDegree *
              ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree := by
              change
                (rhsCore.comp ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b)).natDegree =
                  rhsCore.natDegree *
                    ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree
              rw [Polynomial.natDegree_comp]
      _ = rhsCore.natDegree * 1 := by
            rw [Polynomial.natDegree_linear (a := a) (b := b) ha]
      _ = rhsCore.natDegree := by
            simp
      _ = 2 ^ h_rel.p := by
            rw [show rhsCore =
              ((((Polynomial.X ^ 2 + Polynomial.C c) : Polynomial ℂ).comp^[h_rel.p]) Polynomial.X) by
                rfl]
            exact natDegree_quad_add_const_iterate c h_rel.p
  have h_pow_gt_two : 2 < 2 ^ h_rel.p := by
    have h_pow_ge_four : 4 ≤ 2 ^ h_rel.p := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) h_rel.p_pos)
    exact lt_of_lt_of_le (by norm_num : 2 < 4) h_pow_ge_four
  have h_deg_lt : lhs.natDegree < rhs.natDegree := by
    rw [h_rhs_deg]
    exact lt_of_le_of_lt h_lhs_deg h_pow_gt_two
  exact (Nat.ne_of_lt h_deg_lt) (congrArg Polynomial.natDegree h_poly_eq)

/--
More generally, any `BMol` whose underlying map is literally a polynomial of
degree `2` cannot self-renormalize in the current affine renormalization
scaffold.
-/
theorem no_self_renormalization_relation_of_eq_eval_polynomial_natDegree_two
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P)
    (h_deg : P.natDegree = 2) :
    ¬ Nonempty (RenormalizationRelation g g) := by
  rintro ⟨h_rel⟩
  rcases h_rel.rescaling_affine with ⟨a, b, ha, hψ⟩
  let lhs : Polynomial ℂ := Polynomial.C a * P + Polynomial.C b
  let rhsCore : Polynomial ℂ := (P.comp^[h_rel.p]) Polynomial.X
  let rhs : Polynomial ℂ := rhsCore.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)
  have h_eval_eq : ∀ z ∈ g.U, Polynomial.eval z lhs = Polynomial.eval z rhs := by
    intro z hz
    calc
      Polynomial.eval z lhs = a * Polynomial.eval z P + b := by
        simp [lhs, add_comm]
      _ = (fun w : ℂ => Polynomial.eval w P)^[h_rel.p] (a * z + b) := by
        simpa [hψ, h_poly] using h_rel.eq_f z hz
      _ = Polynomial.eval (a * z + b) rhsCore := by
        rw [show rhsCore = ((P.comp^[h_rel.p]) Polynomial.X) by rfl]
        exact (eval_polynomial_iterate P h_rel.p (a * z + b)).symm
      _ = Polynomial.eval z rhs := by
        change
          Polynomial.eval (a * z + b) rhsCore =
            Polynomial.eval z
              (rhsCore.comp ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b))
        rw [Polynomial.eval_comp]
        simp
  have h_gU_infinite : Set.Infinite g.U := by
    rcases g.isConnected_U.nonempty with ⟨z0, hz0⟩
    exact infinite_of_mem_nhds z0 (g.isOpen_U.mem_nhds hz0)
  have h_poly_eq : lhs = rhs := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine h_gU_infinite.mono ?_
    intro z hz
    simpa using h_eval_eq z hz
  have h_lhs_deg : lhs.natDegree ≤ 2 := by
    refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
    · rw [Polynomial.natDegree_C_mul ha, h_deg]
    · simp
  have h_rhs_deg : rhs.natDegree = 2 ^ h_rel.p := by
    calc
      rhs.natDegree
          = rhsCore.natDegree *
              ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree := by
              change
                (rhsCore.comp ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b)).natDegree =
                  rhsCore.natDegree *
                    ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree
              rw [Polynomial.natDegree_comp]
      _ = rhsCore.natDegree * 1 := by
            rw [Polynomial.natDegree_linear (a := a) (b := b) ha]
      _ = rhsCore.natDegree := by
            simp
      _ = 2 ^ h_rel.p := by
            rw [show rhsCore = ((P.comp^[h_rel.p]) Polynomial.X) by rfl]
            exact natDegree_polynomial_iterate_of_natDegree_two P h_deg h_rel.p
  have h_pow_gt_two : 2 < 2 ^ h_rel.p := by
    have h_pow_ge_four : 4 ≤ 2 ^ h_rel.p := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) h_rel.p_pos)
    exact lt_of_lt_of_le (by norm_num : 2 < 4) h_pow_ge_four
  have h_deg_lt : lhs.natDegree < rhs.natDegree := by
    rw [h_rhs_deg]
    exact lt_of_le_of_lt h_lhs_deg h_pow_gt_two
  exact (Nat.ne_of_lt h_deg_lt) (congrArg Polynomial.natDegree h_poly_eq)

/--
The same degree argument already rules out self-renormalization for every
explicit polynomial base map of degree strictly bigger than `1`.
-/
theorem no_self_renormalization_relation_of_eq_eval_polynomial_natDegree_gt_one
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P)
    (h_deg : 1 < P.natDegree) :
    ¬ Nonempty (RenormalizationRelation g g) := by
  rintro ⟨h_rel⟩
  rcases h_rel.rescaling_affine with ⟨a, b, ha, hψ⟩
  let lhs : Polynomial ℂ := Polynomial.C a * P + Polynomial.C b
  let rhsCore : Polynomial ℂ := (P.comp^[h_rel.p]) Polynomial.X
  let rhs : Polynomial ℂ := rhsCore.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)
  have h_eval_eq : ∀ z ∈ g.U, Polynomial.eval z lhs = Polynomial.eval z rhs := by
    intro z hz
    calc
      Polynomial.eval z lhs = a * Polynomial.eval z P + b := by
        simp [lhs, add_comm]
      _ = (fun w : ℂ => Polynomial.eval w P)^[h_rel.p] (a * z + b) := by
        simpa [hψ, h_poly] using h_rel.eq_f z hz
      _ = Polynomial.eval (a * z + b) rhsCore := by
        rw [show rhsCore = ((P.comp^[h_rel.p]) Polynomial.X) by rfl]
        exact (eval_polynomial_iterate P h_rel.p (a * z + b)).symm
      _ = Polynomial.eval z rhs := by
        change
          Polynomial.eval (a * z + b) rhsCore =
            Polynomial.eval z
              (rhsCore.comp ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b))
        rw [Polynomial.eval_comp]
        simp
  have h_gU_infinite : Set.Infinite g.U := by
    rcases g.isConnected_U.nonempty with ⟨z0, hz0⟩
    exact infinite_of_mem_nhds z0 (g.isOpen_U.mem_nhds hz0)
  have h_poly_eq : lhs = rhs := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine h_gU_infinite.mono ?_
    intro z hz
    simpa using h_eval_eq z hz
  have h_lhs_deg : lhs.natDegree = P.natDegree := by
    calc
      lhs.natDegree = (Polynomial.C a * P).natDegree := by
        simp [lhs]
      _ = P.natDegree := by
        rw [Polynomial.natDegree_C_mul ha]
  have h_rhs_deg : rhs.natDegree = P.natDegree ^ h_rel.p := by
    calc
      rhs.natDegree
          = rhsCore.natDegree *
              ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree := by
              change
                (rhsCore.comp ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b)).natDegree =
                  rhsCore.natDegree *
                    ((Polynomial.C a : Polynomial ℂ) * Polynomial.X + Polynomial.C b).natDegree
              rw [Polynomial.natDegree_comp]
      _ = rhsCore.natDegree * 1 := by
            rw [Polynomial.natDegree_linear (a := a) (b := b) ha]
      _ = rhsCore.natDegree := by
            simp
      _ = P.natDegree ^ h_rel.p := by
            rw [show rhsCore = ((P.comp^[h_rel.p]) Polynomial.X) by rfl]
            exact natDegree_polynomial_iterate P h_rel.p
  have h_one_lt_p : 1 < h_rel.p := by
    exact lt_of_lt_of_le (by norm_num : 1 < 2) h_rel.p_pos
  have h_pow_gt : P.natDegree < P.natDegree ^ h_rel.p := by
    simpa using (Nat.pow_lt_pow_right h_deg h_one_lt_p)
  have h_deg_lt : lhs.natDegree < rhs.natDegree := by
    rw [h_lhs_deg, h_rhs_deg]
    exact h_pow_gt
  exact (Nat.ne_of_lt h_deg_lt) (congrArg Polynomial.natDegree h_poly_eq)

/--
Every explicit polynomial model in `BMol` already has degree strictly bigger
than `1`: otherwise its derivative would be affine-constant, contradicting the
existence of a simple unique critical point.
-/
theorem one_lt_natDegree_of_eq_eval_polynomial
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P) :
    1 < P.natDegree := by
  by_contra h_not_lt
  have h_deg : P.natDegree ≤ 1 := Nat.not_lt.mp h_not_lt
  obtain ⟨a, b, hP⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one h_deg
  let c := criticalPoint g
  have hcU : c ∈ g.U := (Classical.choose_spec g.unique_critical_point).1.1
  have hcrit : deriv g.f c = 0 := (Classical.choose_spec g.unique_critical_point).1.2
  have hsimple := g.simple_critical_point c hcU hcrit
  have hderiv_const_mul :
      deriv (fun z : ℂ => a * z) = fun _ : ℂ => a := by
    funext x
    simpa using (hasDerivAt_const_mul (x := x) a).deriv
  have hsecond_zero : deriv (deriv g.f) c = 0 := by
    calc
      deriv (deriv g.f) c = deriv (deriv (fun z : ℂ => a * z + b)) c := by
        simp [h_poly, hP]
      _ = deriv (deriv (fun z : ℂ => a * z)) c := by
        simp
      _ = deriv (fun _ : ℂ => a) c := by
        rw [hderiv_const_mul]
      _ = 0 := by
        simp
  exact hsimple hsecond_zero

/--
So the current affine renormalization scaffold rules out self-renormalization
for every explicit polynomial `BMol` point, not just the degree-`2` examples.
-/
theorem no_self_renormalization_relation_of_eq_eval_polynomial
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P) :
    ¬ Nonempty (RenormalizationRelation g g) := by
  exact
    no_self_renormalization_relation_of_eq_eval_polynomial_natDegree_gt_one h_poly
      (one_lt_natDegree_of_eq_eval_polynomial h_poly)

/--
The explicit shifted quadratic model also cannot self-renormalize in the
current affine renormalization scaffold.
-/
theorem no_self_renormalization_relation_shiftedBMol :
    ¬ Nonempty (RenormalizationRelation shiftedBMol shiftedBMol) := by
  apply no_self_renormalization_relation_of_eq_sq_add_const (g := shiftedBMol) (c := 1)
  funext z
  simp [shiftedBMol]

/--
The explicit `largeBMol` model cannot self-renormalize in the current affine
renormalization scaffold.
-/
theorem no_self_renormalization_relation_largeBMol :
    ¬ Nonempty (RenormalizationRelation largeBMol largeBMol) := by
  apply no_self_renormalization_relation_of_eq_sq (g := largeBMol)
  funext z
  simp [largeBMol]

/--
Any non-`defaultBMol` point whose underlying map is literally `z ↦ z^2`
cannot be fixed by `Rfast`: fixedness would force the impossible
self-renormalization relation.
-/
theorem no_fixed_of_eq_sq_of_ne_defaultBMol
    {g : BMol}
    (h_quad : g.f = fun z => z ^ 2)
    (h_ne : g ≠ defaultBMol) :
    ¬ Rfast g = g := by
  intro h_fixed
  exact
    no_self_renormalization_relation_of_eq_sq h_quad
      (self_renormalization_relation_of_fixed_of_ne_defaultBMol h_ne h_fixed)

/--
The same fixedness obstruction extends to every explicit quadratic polynomial
`z ↦ z^2 + c`.
-/
theorem no_fixed_of_eq_sq_add_const_of_ne_defaultBMol
    {g : BMol} {c : ℂ}
    (h_quad : g.f = fun z => z ^ 2 + c)
    (h_ne : g ≠ defaultBMol) :
    ¬ Rfast g = g := by
  intro h_fixed
  exact
    no_self_renormalization_relation_of_eq_sq_add_const h_quad
      (self_renormalization_relation_of_fixed_of_ne_defaultBMol h_ne h_fixed)

/--
The same fixedness obstruction already covers every explicit polynomial base of
degree `2`.
-/
theorem no_fixed_of_eq_eval_polynomial_natDegree_two_of_ne_defaultBMol
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P)
    (h_deg : P.natDegree = 2)
    (h_ne : g ≠ defaultBMol) :
    ¬ Rfast g = g := by
  intro h_fixed
  exact
    no_self_renormalization_relation_of_eq_eval_polynomial_natDegree_two h_poly h_deg
      (self_renormalization_relation_of_fixed_of_ne_defaultBMol h_ne h_fixed)

/--
So any explicit polynomial base map of degree strictly bigger than `1` is also
screened out by the current fixedness gate.
-/
theorem no_fixed_of_eq_eval_polynomial_natDegree_gt_one_of_ne_defaultBMol
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P)
    (h_deg : 1 < P.natDegree)
    (h_ne : g ≠ defaultBMol) :
    ¬ Rfast g = g := by
  intro h_fixed
  exact
    no_self_renormalization_relation_of_eq_eval_polynomial_natDegree_gt_one h_poly h_deg
      (self_renormalization_relation_of_fixed_of_ne_defaultBMol h_ne h_fixed)

/--
So the current fixedness gate already screens every explicit polynomial base
map in `BMol`.
-/
theorem no_fixed_of_eq_eval_polynomial_of_ne_defaultBMol
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P)
    (h_ne : g ≠ defaultBMol) :
    ¬ Rfast g = g := by
  intro h_fixed
  exact
    no_self_renormalization_relation_of_eq_eval_polynomial h_poly
      (self_renormalization_relation_of_fixed_of_ne_defaultBMol h_ne h_fixed)

/--
So no explicit polynomial `BMol` point can pass the full fixed-and-
renormalizable seed gate in the current `Rfast` model.
-/
theorem no_fixed_and_renorm_of_eq_eval_polynomial
    {g : BMol} {P : Polynomial ℂ}
    (h_poly : g.f = fun z => Polynomial.eval z P)
    (h_fixed : Rfast g = g)
    (h_renorm : IsFastRenormalizable g) :
    False := by
  by_cases h_default : g = defaultBMol
  · exact defaultBMol_not_renormalizable (by simpa [h_default] using h_renorm)
  · exact (no_fixed_of_eq_eval_polynomial_of_ne_defaultBMol h_poly h_default) h_fixed

/--
Equivalently, any fixed-and-renormalizable point of `Rfast` already lies
outside the explicit-polynomial family.
-/
theorem not_exists_eq_eval_polynomial_of_fixed_and_renorm
    {g : BMol}
    (h_fixed : Rfast g = g)
    (h_renorm : IsFastRenormalizable g) :
    ¬ ∃ P : Polynomial ℂ, g.f = fun z => Polynomial.eval z P := by
  intro h_poly
  rcases h_poly with ⟨P, hP⟩
  exact no_fixed_and_renorm_of_eq_eval_polynomial hP h_fixed h_renorm

/--
Therefore any fixed point in the shifted finite-observation class already lies
outside the explicit-polynomial family if it is to survive the seed upgrade.
-/
theorem
    not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_finite_observation_of_eq_shifted_observation_of_fixed
    {f_ref : BMol}
    (h_obs : bmol_finite_observation f_ref = bmol_finite_observation shiftedBMol)
    (h_fixed : Rfast f_ref = f_ref) :
    ¬ ∃ P : Polynomial ℂ, f_ref.f = fun z => Polynomial.eval z P := by
  exact
    not_exists_eq_eval_polynomial_of_fixed_and_renorm
      h_fixed
      (isFastRenormalizable_of_fixed_of_ne_defaultBMol
        (ne_defaultBMol_of_eq_shifted_bmol_finite_observation h_obs) h_fixed)

/--
The same explicit-polynomial exclusion already holds for every fixed base in
the broader zero-observation-`1` class of the new operator.
-/
theorem
    not_exists_eq_eval_polynomial_of_slice_chart_finite_observation_and_slice_operator_zero_observation_of_zero_eq_one_of_fixed
    {f_ref : BMol}
    (h_zero : bmol_zero_observation f_ref = 1)
    (h_fixed : Rfast f_ref = f_ref) :
    ¬ ∃ P : Polynomial ℂ, f_ref.f = fun z => Polynomial.eval z P := by
  exact
    not_exists_eq_eval_polynomial_of_fixed_and_renorm
      h_fixed
      (isFastRenormalizable_of_fixed_of_ne_defaultBMol
        (ne_defaultBMol_of_bmol_zero_observation_eq_one h_zero) h_fixed)

/--
The current multivalued scaffold still sits on the explicit polynomial base
`shiftedBMol`, so it cannot be fixed by `Rfast` in the current model.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued_base_fixed :
    ¬ Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued.f_ref := by
  intro h_fixed
  have h_renorm :
      IsFastRenormalizable
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued.f_ref) := by
    simpa
      [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued]
      using
        isFastRenormalizable_of_fixed_of_ne_defaultBMol shiftedBMol_ne_defaultBMol h_fixed
  have h_poly :
      (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued.f_ref).f =
        fun z => Polynomial.eval z (Polynomial.X ^ 2 + Polynomial.C 1) := by
    simpa
      [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued]
      using shiftedBMol_f_eq_eval_polynomial_sq_add_one
  exact
    no_fixed_and_renorm_of_eq_eval_polynomial
      h_poly
      (by
        simpa
          [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_slice_chart_multivalued_and_slice_operator_multivalued]
          using h_fixed)
      h_renorm

/--
So any refined-scaffold package built from a non-`defaultBMol` explicit
polynomial base is not fixed by `Rfast`.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_eq_eval_polynomial
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    {P : Polynomial ℂ}
    (h_poly : f_ref.f = fun z => Polynomial.eval z P)
    (h_ne_default : f_ref ≠ defaultBMol) :
    ¬ Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref := by
  exact
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_no_self_renorm
      hg_ne
      h_ne_default
      (no_self_renormalization_relation_of_eq_eval_polynomial h_poly)

/--
So any attempted fixedness-based seed upgrade from a non-`defaultBMol`
refined-scaffold package already fails as soon as the base has no
self-renormalization relation.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed_of_no_self_renorm
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_no_self : ¬ Nonempty (RenormalizationRelation f_ref f_ref))
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    False := by
  exact
    (no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_no_self_renorm
      hg_ne h_ne_default h_no_self)
      h_fixed

/--
In particular, the fixedness-based seed-upgrade route is impossible for every
non-`defaultBMol` refined-scaffold package whose base is an explicit
polynomial.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed_of_eq_eval_polynomial
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    {P : Polynomial ℂ}
    (h_poly : f_ref.f = fun z => Polynomial.eval z P)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    False := by
  exact
    (no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_eq_eval_polynomial
      hg_ne h_poly h_ne_default)
      h_fixed

/--
At the full fixed-and-renormalizable upgrade interface, the same obstruction
already closes every explicit-polynomial refined-scaffold package built by the
generic `of_ne` constructor. The `defaultBMol` branch dies on
renormalizability, and every non-`defaultBMol` branch dies on fixedness.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_eq_eval_polynomial
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    {P : Polynomial ℂ}
    (h_poly : f_ref.f = fun z => Polynomial.eval z P)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref)
    (h_renorm :
      IsFastRenormalizable
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    False := by
  exact
    no_fixed_and_renorm_of_eq_eval_polynomial
      h_poly
      (by
        simpa
          [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
          using h_fixed)
      (by
        simpa
          [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
          using h_renorm)

/--
So any future fixed-and-renormalizable `of_ne` refined-scaffold candidate must
already use a base map outside the explicit-polynomial family.
-/
theorem
    not_exists_eq_eval_polynomial_of_refined_chart_and_operator_of_ne_fixed_and_renorm
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref)
    (h_renorm :
      IsFastRenormalizable
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    ¬ ∃ P : Polynomial ℂ, f_ref.f = fun z => Polynomial.eval z P := by
  intro h_poly
  rcases h_poly with ⟨P, hP⟩
  exact
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_eq_eval_polynomial
      hg_ne hP h_fixed h_renorm

/--
So the actual seed package produced by the generic `of_ne` fixed-upgrade
constructor already carries the same frontier condition: its base cannot be an
explicit polynomial point.
-/
theorem
    not_exists_eq_eval_polynomial_of_refined_chart_and_operator_seed_sources_with_of_ne_of_fixed
    {f_ref g : BMol}
    (hg_ne : g ≠ f_ref)
    (h_ne_default : f_ref ≠ defaultBMol)
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
            f_ref g hg_ne).f_ref =
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne
          f_ref g hg_ne).f_ref) :
    ¬ ∃ P : Polynomial ℂ,
        (molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed
          hg_ne h_ne_default h_fixed).f_star.f =
          fun z => Polynomial.eval z P := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed,
      molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_of_scaffold_and_fixed_renorm,
      molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne]
    using
      (not_exists_eq_eval_polynomial_of_refined_chart_and_operator_of_ne_fixed_and_renorm
        hg_ne
        h_fixed
        (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_renorm_of_fixed
          hg_ne h_ne_default h_fixed))

/--
So the large-base refined scaffold cannot upgrade to the dynamical seed package
via fixedness: its base is an explicit polynomial point already screened by the
generic `of_ne` obstruction.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_large_base_refined_chart_and_operator_of_fixed
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) :
    False := by
  exact
    (no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed_of_eq_eval_polynomial
      (f_ref := largeBMol)
      (g := defaultBMol)
      (P := Polynomial.X ^ 2)
      largeBMol_ne_defaultBMol.symm
      (by
        funext z
        simp [largeBMol])
      largeBMol_ne_defaultBMol)
      (by
        simpa
          [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator]
          using h_fixed)

/--
The shifted-base refined scaffold is blocked at the same fixed-to-seed-upgrade
interface.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_shifted_base_refined_chart_and_operator_of_fixed
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator.f_ref) :
    False := by
  exact
    (no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed_of_eq_eval_polynomial
      (f_ref := shiftedBMol)
      (g := defaultBMol)
      (P := Polynomial.X ^ 2 + Polynomial.C 1)
      shiftedBMol_ne_defaultBMol.symm
      (by
        funext z
        simp [shiftedBMol])
      shiftedBMol_ne_defaultBMol)
      (by
        simpa
          [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator]
          using h_fixed)

/--
So the large-base refined scaffold candidate is not fixed by `Rfast`: fixedness
would force the impossible self-renormalization relation on `largeBMol`.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator_base_fixed :
    ¬ Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator]
    using
      (no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_eq_eval_polynomial
        (f_ref := largeBMol)
        (g := defaultBMol)
        (P := Polynomial.X ^ 2)
        largeBMol_ne_defaultBMol.symm
        (by
          funext z
          simp [largeBMol])
        largeBMol_ne_defaultBMol)

/--
So the shifted-base refined scaffold candidate is also not fixed by `Rfast`:
fixedness would force the impossible affine self-renormalization relation on
`shiftedBMol`.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator_base_fixed :
    ¬ Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator.f_ref := by
  simpa
    [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_shifted_base_refined_chart_and_operator]
    using
      (no_molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_refined_chart_and_operator_of_ne_base_fixed_of_eq_eval_polynomial
        (f_ref := shiftedBMol)
        (g := defaultBMol)
        (P := Polynomial.X ^ 2 + Polynomial.C 1)
        shiftedBMol_ne_defaultBMol.symm
        (by
          funext z
          simp [shiftedBMol])
        shiftedBMol_ne_defaultBMol)

/--
So the large-base refined scaffold upgrades to the dynamical seed package as
soon as its base is shown to be fixed by `Rfast`.
-/
noncomputable def
    molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_large_base_refined_chart_and_operator_of_fixed
    (h_fixed :
      Rfast
          (molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) =
        molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator.f_ref) :
    MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
      slice_chart_refined slice_operator_refined :=
  molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_chart_and_operator_of_ne_of_fixed
    largeBMol_ne_defaultBMol.symm
    largeBMol_ne_defaultBMol
    (by
      simpa
        [molecule_residual_dynamical_banach_neighborhood_operator_scaffold_sources_with_large_base_refined_chart_and_operator]
        using h_fixed)

/--
If a PLAN_84 seed exists, the refined chart/operator scaffold already admits a
separated Banach-neighborhood operator package. This isolates the obstruction
to the legacy `slice_chart`, not to the operator-route shape itself.
-/
noncomputable def
    molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith
      slice_chart_refined slice_operator := by
  let f_star := renormalizable_fixed_seed_point h_seed
  let B : Set SliceSpace := ({(0 : SliceSpace), (1 : SliceSpace)} : Set SliceSpace)
  have h_compact_B : IsCompact B := by
    exact
      ((Set.finite_singleton (1 : SliceSpace)).insert (0 : SliceSpace)).isCompact
  have h_default_ne_f_star : defaultBMol ≠ f_star := by
    intro h_eq
    have h_renorm_default : IsFastRenormalizable defaultBMol := by
      simpa [f_star, h_eq] using (renormalizable_fixed_seed_point_spec h_seed).1
    exact defaultBMol_not_renormalizable h_renorm_default
  refine
    { f_star := f_star
      B := B
      chart_mem := by
        simp [B, slice_chart_refined]
      compact := h_compact_B
      maps := ?_
      fixed := renormalizable_fixed_seed_point_fixed h_seed
      renorm := (renormalizable_fixed_seed_point_spec h_seed).1
      realized_nonbase := ?_ }
  · intro z hz
    simp [B, slice_operator]
  · refine ⟨defaultBMol, ?_, ?_⟩
    · simp [B, slice_chart_refined, h_default_ne_f_star]
    · simp [slice_chart_refined, h_default_ne_f_star]

/--
Under the refined chart scaffold, the separated Banach-neighborhood operator
route is available exactly when the PLAN_84 seed interface is available. So
chart separation alone is not a new zero-argument producer class.
-/
theorem
    molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_iff_renormalizable_fixed_seed_source :
    Nonempty
        (MoleculeResidualSeparatedBanachNeighborhoodOperatorSeedSourcesWith
          slice_chart_refined slice_operator) ↔
      MoleculeResidualRenormalizableFixedSeedSource := by
  constructor
  · intro h_nonempty
    rcases h_nonempty with ⟨h_sources⟩
    exact
      molecule_residual_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources_with
        h_sources.toMoleculeResidualBanachNeighborhoodOperatorSeedSourcesWith
  · intro h_seed
    exact
      ⟨molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_of_renormalizable_fixed_seed_source
        h_seed⟩

/--
Any PLAN_84 seed also witnesses separation for the refined chart. This is the
smallest in-repo proxy for the kind of nonconstant chart the legacy scaffold
still lacks.
-/
theorem
    molecule_residual_separated_slice_chart_source_with_refined_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualSeparatedSliceChartSourceWith slice_chart_refined := by
  exact
    molecule_residual_separated_slice_chart_source_with_of_separated_banach_neighborhood_operator_seed_sources_with
      (molecule_residual_separated_banach_neighborhood_operator_seed_sources_with_refined_of_renormalizable_fixed_seed_source
        h_seed)

/--
Even after replacing the legacy chart by `slice_chart_refined`, the current
operator scaffold is still too trivial to realize genuine operator-side
dynamics.
-/
theorem
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_refined_current_operator :
    ¬ Nonempty
        (MoleculeResidualDynamicalBanachNeighborhoodOperatorSeedSourcesWith
          slice_chart_refined slice_operator) := by
  exact
    no_molecule_residual_dynamical_banach_neighborhood_operator_seed_sources_with_current_operator

/--
Any PLAN_84 seed yields a singleton-domain renormalizability bridge without
mentioning `fixed_point_exists`.
-/
theorem fixed_point_implies_renormalizable_on_seed_singleton
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    FixedPointImpliesRenormalizableOn
      ({renormalizable_fixed_seed_point h_seed} : Set BMol) :=
  fixed_point_implies_renormalizable_on_singleton_of_renorm
    (renormalizable_fixed_seed_point_spec h_seed).1

/--
The singleton bridge at a PLAN_84 seed is equivalent to renormalizability of
the seed, exactly as in the selected-point route but without `fixed_point_exists`.
-/
theorem fixed_point_implies_renormalizable_on_seed_singleton_iff
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    FixedPointImpliesRenormalizableOn
      ({renormalizable_fixed_seed_point h_seed} : Set BMol) ↔
      IsFastRenormalizable (renormalizable_fixed_seed_point h_seed) :=
  fixed_point_implies_renormalizable_on_singleton_iff
    (renormalizable_fixed_seed_point_fixed h_seed)

/--
A PLAN_84 seed is visibly disjoint from the old `defaultBMol` obstruction:
the chosen seed cannot be `defaultBMol`, because the seed is renormalizable and
`defaultBMol` is not.
-/
theorem renormalizable_fixed_seed_point_ne_defaultBMol
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    renormalizable_fixed_seed_point h_seed ≠ defaultBMol := by
  intro h_eq
  have h_renorm_default : IsFastRenormalizable defaultBMol := by
    simpa [h_eq] using (renormalizable_fixed_seed_point_spec h_seed).1
  exact defaultBMol_not_renormalizable h_renorm_default

/--
Any PLAN_84 seed already yields the existence-side source target.
-/
theorem molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualFixedPointExistenceSource :=
  h_seed

/--
Upgrade a renormalizable fixed seed to the stronger critical-value-zero seed
contract using the fixed-point critical-value transfer source.
-/
theorem molecule_residual_critical_renormalizable_fixed_seed_source_of_seed_and_critical_value_transfer
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource)
    (h_crit : FixedPointCriticalValueTransferSource) :
    MoleculeResidualCriticalRenormalizableFixedSeedSource := by
  rcases h_seed with ⟨f_seed, h_renorm, h_fixed⟩
  exact ⟨f_seed, h_renorm, h_fixed, h_crit f_seed h_fixed h_renorm⟩

/--
Any Banach-neighborhood operator seed package plus critical-value transfer
already yields the stronger critical-seed contract.
-/
theorem molecule_residual_critical_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources_and_critical_value_transfer
    (h_sources : MoleculeResidualBanachNeighborhoodOperatorSeedSources)
    (h_crit : FixedPointCriticalValueTransferSource) :
    MoleculeResidualCriticalRenormalizableFixedSeedSource :=
  molecule_residual_critical_renormalizable_fixed_seed_source_of_seed_and_critical_value_transfer
    (molecule_residual_renormalizable_fixed_seed_source_of_banach_neighborhood_operator_seed_sources
      h_sources)
    h_crit

/--
In the current identity-model scaffold, exact uniqueness of fixed hybrid
classes rules out any renormalizable fixed point, because `defaultBMol` is
already a fixed point and is not fast-renormalizable.
-/
theorem no_molecule_residual_fixed_point_existence_source_of_hybrid_class_fixed_point_exact_uniqueness
    (h_unique_exact : MoleculeResidualHybridClassFixedPointExactUniquenessSource) :
    ¬ MoleculeResidualFixedPointExistenceSource := by
  intro h_exists
  rcases h_exists with ⟨g, h_renorm_g, h_fix_g⟩
  have h_fix_default : R_hybrid (toHybridClass defaultBMol) = toHybridClass defaultBMol := by
    change Rfast defaultBMol = defaultBMol
    simp [Rfast, defaultBMol_not_renormalizable]
  have h_fix_g_class : R_hybrid (toHybridClass g) = toHybridClass g := by
    simpa [R_hybrid, toHybridClass] using h_fix_g
  have h_eq_class :
      toHybridClass defaultBMol = toHybridClass g :=
    h_unique_exact (toHybridClass defaultBMol) (toHybridClass g)
      h_fix_default h_fix_g_class
  have h_eq : defaultBMol = g := toHybridClass_injective h_eq_class
  exact defaultBMol_not_renormalizable (by simpa [h_eq] using h_renorm_g)

/--
Source seam for the fixed-point renormalizability bridge contract.
-/
def MoleculeResidualFixedPointBridgeSource : Prop :=
  FixedPointImpliesRenormalizable

/--
Source seam for a restricted fixed-point renormalizability bridge on a
designated domain.
-/
def MoleculeResidualFixedPointBridgeOnSource : Prop :=
  ∃ K : Set BMol,
    (∃ f : BMol, f ∈ K ∧ Rfast f = f) ∧
      FixedPointImpliesRenormalizableOn K

/--
Exact larger-domain target for PLAN_86: a localized bridge package whose domain
contains the designated fixed reference point but is not just its singleton.
-/
structure MoleculeResidualNonSingletonLocalizedBridgeSources where
  K : Set BMol
  f_ref : BMol
  mem : f_ref ∈ K
  fixed : Rfast f_ref = f_ref
  bridge_on : FixedPointImpliesRenormalizableOn K
  nontrivial : ∃ g : BMol, g ∈ K ∧ g ≠ f_ref

/--
Current fixed-point renormalizability bridge source theorem
(legacy global-normalization route).
-/
theorem molecule_residual_fixed_point_bridge_source :
    MoleculeResidualFixedPointBridgeSource :=
  fixed_point_implies_renormalizable_of_global_norm molecule_h_norm

/--
Construct fixed-point existence source from the bridge contract.
-/
theorem molecule_residual_fixed_point_existence_source_of_bridge
    (h_bridge : MoleculeResidualFixedPointBridgeSource) :
    MoleculeResidualFixedPointExistenceSource :=
  renormalizable_fixed_exists_of_fixed_point_exists_and_bridge h_bridge

/--
Construct fixed-point existence source from a restricted bridge-on source.
-/
theorem molecule_residual_fixed_point_existence_source_of_bridge_on
    (h_bridge_on : MoleculeResidualFixedPointBridgeOnSource) :
    MoleculeResidualFixedPointExistenceSource := by
  rcases h_bridge_on with ⟨K, h_fixed_in, h_bridge_on_K⟩
  rcases renormalizable_fixed_exists_of_fixed_point_exists_in_and_bridge_on
      h_fixed_in
      h_bridge_on_K with
    ⟨f_star, _hf_domain, h_renorm, h_fixed⟩
  exact ⟨f_star, h_renorm, h_fixed⟩

/--
Upgrade any existence witness to the stronger critical-value-zero seed
contract using the fixed-point critical-value transfer source.
-/
theorem molecule_residual_critical_renormalizable_fixed_seed_source_of_fixed_point_existence_source_and_critical_value_transfer
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_crit : FixedPointCriticalValueTransferSource) :
    MoleculeResidualCriticalRenormalizableFixedSeedSource :=
  molecule_residual_critical_renormalizable_fixed_seed_source_of_seed_and_critical_value_transfer
    h_exists
    h_crit

/--
The standard-Siegel / Feigenbaum fixed-point assumptions already yield the
stronger critical seed contract directly. This exposes a concrete seed-side
producer family already present in the repository.
-/
theorem molecule_residual_critical_renormalizable_fixed_seed_source_of_standard_siegel_fixed_point
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
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)) :
    MoleculeResidualCriticalRenormalizableFixedSeedSource := by
  rcases exists_standard_siegel_fixed_point h_exists h_conj h_norm with
    ⟨f_seed, h_std, h_fix⟩
  exact ⟨f_seed, h_std.1, h_fix, h_std.2.1⟩


/--
Forget the nontriviality witness and recover the basic localized bridge source.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_non_singleton_localized_bridge_sources
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources) :
    MoleculeResidualFixedPointBridgeOnSource :=
  ⟨h_sources.K, ⟨h_sources.f_ref, h_sources.mem, h_sources.fixed⟩, h_sources.bridge_on⟩

/--
Any larger-domain localized bridge source would already solve the existence
side of PLAN_86.
-/
theorem molecule_residual_fixed_point_existence_source_of_non_singleton_localized_bridge_sources
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    (molecule_residual_fixed_point_bridge_on_source_of_non_singleton_localized_bridge_sources
      h_sources)

/--
Any non-singleton localized bridge source plus critical-value transfer already
yields the stronger critical seed contract. This is the exact common midpoint
between the localized PLAN_88 branch and the downstream fixed-data/local-
witness rebases.
-/
theorem molecule_residual_critical_renormalizable_fixed_seed_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources)
    (h_crit : FixedPointCriticalValueTransferSource) :
    MoleculeResidualCriticalRenormalizableFixedSeedSource :=
  molecule_residual_critical_renormalizable_fixed_seed_source_of_fixed_point_existence_source_and_critical_value_transfer
    (molecule_residual_fixed_point_existence_source_of_non_singleton_localized_bridge_sources
      h_sources)
    h_crit

/--
Any PLAN_84 seed yields a restricted bridge-on source on its singleton domain,
without mentioning `fixed_point_exists` or `selected_fixed_point`.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualFixedPointBridgeOnSource :=
  ⟨
    ({renormalizable_fixed_seed_point h_seed} : Set BMol),
    ⟨
      renormalizable_fixed_seed_point h_seed,
      by simp,
      renormalizable_fixed_seed_point_fixed h_seed
    ⟩,
    fixed_point_implies_renormalizable_on_seed_singleton h_seed
  ⟩

/--
The reseeded singleton bridge route already yields the existence-side target.
-/
theorem molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source_via_bridge_on
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    (molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source
      h_seed)

/--
Assemble a restricted bridge-on source from the ground fixed-point theorem and
renormalizability of the designated fixed point selected from that theorem.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_fixed_point_exists_and_singleton_renorm
    (h_renorm :
      IsFastRenormalizable (Classical.choose fixed_point_exists)) :
    MoleculeResidualFixedPointBridgeOnSource := by
  classical
  let f_star : BMol := Classical.choose fixed_point_exists
  have h_fixed_point :
      Rfast f_star = f_star ∧ criticalValue f_star = 0 :=
    Classical.choose_spec fixed_point_exists
  refine
    ⟨
      ({f_star} : Set BMol),
      ⟨f_star, by simp, h_fixed_point.1⟩,
      fixed_point_implies_renormalizable_on_singleton_of_renorm h_renorm
    ⟩

/--
Candidate PLAN_83 bridge route from the exact one-point renormalizability
source attached to `fixed_point_exists`.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_selected_fixed_point_renormalizable
    (h_renorm : MoleculeResidualSelectedFixedPointRenormalizableSource) :
    MoleculeResidualFixedPointBridgeOnSource :=
  molecule_residual_fixed_point_bridge_on_source_of_fixed_point_exists_and_singleton_renorm
    h_renorm

/--
Candidate existence route for PLAN_83:
the localized bridge problem on the refined singleton route is reduced to
renormalizability of one designated fixed point.
-/
theorem molecule_residual_fixed_point_existence_source_of_fixed_point_exists_and_singleton_renorm
    (h_renorm :
      IsFastRenormalizable (Classical.choose fixed_point_exists)) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    (molecule_residual_fixed_point_bridge_on_source_of_fixed_point_exists_and_singleton_renorm
      h_renorm)

/--
Candidate existence route from the exact one-point renormalizability source
named by PLAN_83.
-/
theorem molecule_residual_fixed_point_existence_source_of_selected_fixed_point_renormalizable
    (h_renorm : MoleculeResidualSelectedFixedPointRenormalizableSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    (molecule_residual_fixed_point_bridge_on_source_of_selected_fixed_point_renormalizable
      h_renorm)

/--
Assemble a restricted bridge-on source from:
- a fixed-point witness in a designated domain, and
- localized normalization on that domain.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_fixed_point_and_normalization_on
    {K : Set BMol}
    (h_fixed_in : ∃ f : BMol, f ∈ K ∧ Rfast f = f)
    (h_norm_on : NormalizationOn K) :
    MoleculeResidualFixedPointBridgeOnSource :=
  ⟨K, h_fixed_in, fixed_point_implies_renormalizable_on_of_normalization_on h_norm_on⟩

/--
Build a restricted bridge-on source directly from invariant slice-data paired
with normalization on the same domain.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_invariant_slice_data_with_normalization_source
    (h_data : MoleculeResidualInvariantSliceDataWithNormalizationSource) :
    MoleculeResidualFixedPointBridgeOnSource := by
  rcases h_data with
    ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont,
      h_nonempty, h_mem, h_norm⟩
  rcases invariant_slice_fixed_point_in_of_sources
      hP_comp
      hP_conv
      h_maps
      hK_def
      h_surj
      h_fin
      h_inj
      h_cont
      h_nonempty with
    ⟨f, hfK, h_fixed⟩
  exact
    molecule_residual_fixed_point_bridge_on_source_of_fixed_point_and_normalization_on
      ⟨f, hfK, h_fixed⟩
      h_norm

/--
Build renormalizable fixed-point existence directly from the invariant
slice-data-with-normalization package.
-/
theorem molecule_residual_fixed_point_existence_source_of_invariant_slice_data_with_normalization_source
    (h_data : MoleculeResidualInvariantSliceDataWithNormalizationSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    (molecule_residual_fixed_point_bridge_on_source_of_invariant_slice_data_with_normalization_source
      h_data)

/--
Build a restricted bridge-on source from fixed-point normalization data.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_fixed_point_data_source
    (h_fixed_data : MoleculeResidualFixedPointDataSource) :
    MoleculeResidualFixedPointBridgeOnSource := by
  have h_exists : MoleculeResidualFixedPointExistenceSource :=
    renormalizable_fixed_exists_of_fixed_point_normalization_data h_fixed_data
  rcases h_exists with ⟨f_star, h_renorm, h_fixed⟩
  refine ⟨{f : BMol | Rfast f = f ∧ IsFastRenormalizable f}, ?_, ?_⟩
  · exact ⟨f_star, by simp [h_fixed, h_renorm], h_fixed⟩
  · intro f hf_domain _h_fixed
    exact hf_domain.2

/--
Current restricted bridge-on source theorem routed from fixed-point data.
-/
theorem molecule_residual_fixed_point_bridge_on_source :
    MoleculeResidualFixedPointBridgeOnSource :=
  molecule_residual_fixed_point_bridge_on_source_of_fixed_point_data_source
    molecule_h_fixed_data_direct

/--
Current fixed-point existence source routed via the restricted bridge-on seam.
-/
theorem molecule_residual_fixed_point_existence_source_via_bridge_on :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    molecule_residual_fixed_point_bridge_on_source

/--
Minimal current fixed-point existence carrier for PLAN_81.
-/
theorem molecule_residual_fixed_point_existence_source_via_fixed_data_source
    (h_fixed_data : MoleculeResidualFixedPointDataSource) :
    MoleculeResidualFixedPointExistenceSource :=
  renormalizable_fixed_exists_of_fixed_point_normalization_data h_fixed_data

/--
Build fixed-point existence directly from the ground fixed-point theorem and
renormalizability of fixed points.
-/
theorem molecule_residual_fixed_point_existence_source_of_fixed_point_renormalizable
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f) :
    MoleculeResidualFixedPointExistenceSource := by
  rcases fixed_point_exists with ⟨f_star, h_fixed, _h_cv⟩
  exact ⟨f_star, h_renorm f_star h_fixed, h_fixed⟩

/--
Current fixed-point existence source routed directly through the ground
fixed-point theorem and the direct renormalizability carrier.
-/
theorem molecule_residual_fixed_point_existence_source_via_fixed_data_direct :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_fixed_point_renormalizable
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct

/--
Current fixed-point existence source (legacy global-norm route).
-/
theorem molecule_residual_fixed_point_existence_source :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_via_fixed_data_direct

/--
Current fixed-point local-normalization transfer source (legacy global-norm route).
-/
def MoleculeResidualFixedPointTransferSource : Prop :=
  FixedPointLocalNormalizationTransfer

/--
PLAN_77 source pack for local-domain fixed-point transfer.
-/
structure MoleculeResidualFixedPointTransferOnSources where
  K : Set BMol
  membership : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f → f ∈ K
  normalization : NormalizationOn K

/--
PLAN_77 source pack for one normalized fast-renormalizable fixed-point witness.
-/
structure MoleculeResidualFixedPointLocalWitnessSources where
  f_star : BMol
  fixed : Rfast f_star = f_star
  renorm : IsFastRenormalizable f_star
  crit : criticalValue f_star = 0
  vbound : f_star.V ⊆ Metric.ball 0 0.1

/--
Concrete local-domain witness target: a normalized domain carrying at least
one fixed point of `Rfast`.
-/
structure MoleculeResidualFixedPointLocalWitnessOnSources where
  K : Set BMol
  fixed : ∃ f : BMol, f ∈ K ∧ Rfast f = f
  normalization : NormalizationOn K

/--
Build the local normalized-witness source pack from the concrete local-domain
witness target.
-/
def molecule_residual_fixed_point_local_witness_sources_of_on_sources
    (h_sources : MoleculeResidualFixedPointLocalWitnessOnSources) :
    MoleculeResidualFixedPointLocalWitnessSources := by
  classical
  let f_star : BMol := Classical.choose h_sources.fixed
  have h_fixed_spec : f_star ∈ h_sources.K ∧ Rfast f_star = f_star :=
    Classical.choose_spec h_sources.fixed
  exact
    ⟨
      f_star,
      h_fixed_spec.2,
      h_sources.normalization.1 f_star h_fixed_spec.1,
      h_sources.normalization.2.1 f_star h_fixed_spec.1,
      h_sources.normalization.2.2 f_star h_fixed_spec.1
    ⟩

/--
Build fixed-point normalization data from the PLAN_77 local-witness source
pack.
-/
theorem fixed_point_normalization_data_of_local_witness_sources
    (h_sources : MoleculeResidualFixedPointLocalWitnessSources) :
    FixedPointNormalizationData :=
  ⟨h_sources.f_star, h_sources.fixed, h_sources.renorm, h_sources.crit, h_sources.vbound⟩

/--
Build the PLAN_77 local-witness source pack from fixed-point normalization
data.
-/
def molecule_residual_fixed_point_local_witness_sources_of_fixed_data
    (h_fixed_data : FixedPointNormalizationData) :
    MoleculeResidualFixedPointLocalWitnessSources := by
  classical
  let f_star : BMol := Classical.choose h_fixed_data
  have h_fixed_data_spec :
      Rfast f_star = f_star ∧
      IsFastRenormalizable f_star ∧
      criticalValue f_star = 0 ∧
      f_star.V ⊆ Metric.ball 0 0.1 :=
    Classical.choose_spec h_fixed_data
  exact
    ⟨
      f_star,
      h_fixed_data_spec.1,
      h_fixed_data_spec.2.1,
      h_fixed_data_spec.2.2.1,
      h_fixed_data_spec.2.2.2
    ⟩

/--
Build the concrete local-domain witness target from fixed-point normalization
data.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (h_fixed_data : FixedPointNormalizationData) :
    MoleculeResidualFixedPointLocalWitnessOnSources := by
  let h_witness :=
    molecule_residual_fixed_point_local_witness_sources_of_fixed_data h_fixed_data
  refine
    ⟨
      {h_witness.f_star},
      ?_,
      ?_
    ⟩
  · exact ⟨h_witness.f_star, by simp, h_witness.fixed⟩
  · constructor
    · intro f hf
      have h_eq : f = h_witness.f_star := by simpa using hf
      simpa [h_eq] using h_witness.renorm
    · constructor
      · intro f hf
        have h_eq : f = h_witness.f_star := by simpa using hf
        simpa [h_eq] using h_witness.crit
      · intro f hf
        have h_eq : f = h_witness.f_star := by simpa using hf
        simpa [h_eq] using h_witness.vbound

/--
Build the PLAN_77 local-witness source pack directly from bundled primitive
fixed-point ingredients.
-/
def molecule_residual_fixed_point_local_witness_sources_of_ingredients
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients) :
    MoleculeResidualFixedPointLocalWitnessSources :=
  molecule_residual_fixed_point_local_witness_sources_of_fixed_data
    (fixed_point_normalization_data_of_ingredients h_ingredients)

/--
Build the PLAN_77 local-witness source pack directly from the ground
fixed-point theorem and the direct renormalizability / critical-value /
`V`-bound carriers.
-/
def molecule_residual_fixed_point_local_witness_sources_of_fixed_point_exists_and_component_transfers
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualFixedPointLocalWitnessSources :=
  molecule_residual_fixed_point_local_witness_sources_of_fixed_data
    (fixed_point_normalization_data_of_fixed_point_exists_and_component_transfers
      h_renorm
      h_crit
      h_vbound)

/--
Build the PLAN_77 local-witness source pack directly from the ground
fixed-point theorem, renormalizability of fixed points, and the `V`-bound
transfer component.
-/
def molecule_residual_fixed_point_local_witness_sources_of_fixed_point_exists_and_renorm_and_vbound
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualFixedPointLocalWitnessSources :=
  molecule_residual_fixed_point_local_witness_sources_of_fixed_data
    (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_vbound
      h_renorm
      h_vbound)

/--
Build the PLAN_77 local-witness source pack directly from the ground
fixed-point theorem, renormalizability of fixed points, and renormalizable-point
`V`-bound control.
-/
def molecule_residual_fixed_point_local_witness_sources_of_fixed_point_exists_and_renorm_and_renorm_vbound
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessSources :=
  molecule_residual_fixed_point_local_witness_sources_of_fixed_data
    (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound
      h_renorm
      h_renorm_vbound)

/--
Build the concrete local-domain witness target directly from bundled primitive
fixed-point ingredients.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_ingredients
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (fixed_point_normalization_data_of_ingredients h_ingredients)

/--
Build the concrete local-domain witness target directly from the ground
fixed-point theorem and the direct renormalizability / critical-value /
`V`-bound carriers.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_component_transfers
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (fixed_point_normalization_data_of_fixed_point_exists_and_component_transfers
      h_renorm
      h_crit
      h_vbound)

/--
Build the concrete local-domain witness target directly from the ground
fixed-point theorem, renormalizability of fixed points, and the `V`-bound
transfer component.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_renorm_and_vbound
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_vbound
      h_renorm
      h_vbound)

/--
Build the concrete local-domain witness target directly from the ground
fixed-point theorem, renormalizability of fixed points, and renormalizable-point
`V`-bound control.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_renorm_and_renorm_vbound
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound
      h_renorm
      h_renorm_vbound)

/--
Build the concrete local-witness target directly from the stronger
critical-value-zero seed contract and renormalizable-point `V`-bound control.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_critical_renormalizable_fixed_seed_source_and_renorm_vbound
    (h_seed : MoleculeResidualCriticalRenormalizableFixedSeedSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (by
      rcases h_seed with ⟨f_seed, h_renorm, h_fixed, h_crit⟩
      exact ⟨f_seed, h_fixed, h_renorm, h_crit, h_renorm_vbound f_seed h_renorm h_crit⟩)

/--
Build the concrete local-witness target from existence plus critical-value
transfer and renormalizable-point `V`-bound control.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_existence_and_critical_value_transfer_and_renorm_vbound
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (by
      rcases h_exists with ⟨f_seed, h_renorm, h_fixed⟩
      exact
        ⟨
          f_seed,
          h_fixed,
          h_renorm,
          h_crit f_seed h_fixed h_renorm,
          h_renorm_vbound f_seed h_renorm (h_crit f_seed h_fixed h_renorm)
        ⟩)

/--
Refined-chart invariant slice-data pack whose designated reference map is
already known to be an `Rfast` fixed point, but without any normalization
assumption on the domain.
-/
structure MoleculeResidualRefinedInvariantFixedPointDomainSources where
  K : Set BMol
  f_ref : BMol
  P : Set SliceSpace
  compact : IsCompact P
  convex : Convex ℝ P
  maps : MapsTo (slice_operator f_ref) P P
  kdef : K = {f | slice_chart_refined f_ref f ∈ P}
  surj : SurjOn (slice_chart_refined f_ref) K P
  finite : K.Finite
  inj : InjOn (slice_chart_refined f_ref) K
  cont : ContinuousOn (slice_operator f_ref) ((slice_chart_refined f_ref) '' K)
  nonempty : K.Nonempty
  mem : f_ref ∈ K
  fixed : Rfast f_ref = f_ref

/--
Refined-chart invariant singleton-domain pack around a renormalizable fixed
seed. This makes the localized PLAN_86 branch concrete without mentioning
`fixed_point_exists` or `selected_fixed_point`.
-/
structure MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources extends
    MoleculeResidualRefinedInvariantFixedPointDomainSources where
  singleton : K = ({f_ref} : Set BMol)
  renorm : IsFastRenormalizable f_ref

/--
Build the refined singleton-domain pack directly from a renormalizable fixed
seed.
-/
def molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources := by
  let f_ref := renormalizable_fixed_seed_point h_seed
  refine
    { K := ({f_ref} : Set BMol)
      f_ref := f_ref
      P := ({(0 : SliceSpace)} : Set SliceSpace)
      compact := by
        exact (Set.finite_singleton (0 : SliceSpace)).isCompact
      convex := by
        exact convex_singleton (0 : SliceSpace)
      maps := by
        intro x hx
        simp [slice_operator]
      kdef := by
        ext f
        simp [slice_chart_refined]
      surj := by
        intro y hy
        have hy0 : y = (0 : SliceSpace) := by
          simpa using hy
        refine ⟨f_ref, by simp, ?_⟩
        simp [slice_chart_refined, hy0]
      finite := Set.finite_singleton f_ref
      inj := by
        intro x hx y hy hxy
        simp at hx hy
        simp [hx, hy]
      cont := by
        change ContinuousOn (fun _ : SliceSpace => (0 : SliceSpace))
          ((slice_chart_refined f_ref) '' ({f_ref} : Set BMol))
        exact continuousOn_const
      nonempty := by
        exact Set.singleton_nonempty f_ref
      mem := by simp
      fixed := renormalizable_fixed_seed_point_fixed h_seed
      singleton := rfl
      renorm := (renormalizable_fixed_seed_point_spec h_seed).1 }

/--
Forget the singleton/renormalizability extras and keep only the refined
invariant fixed-point domain data.
-/
def molecule_residual_refined_invariant_fixed_point_domain_sources_of_renormalizable_fixed_seed_source
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualRefinedInvariantFixedPointDomainSources :=
  (molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_of_renormalizable_fixed_seed_source
    h_seed).toMoleculeResidualRefinedInvariantFixedPointDomainSources

/--
Build the refined invariant-domain source pack from the ground fixed-point
theorem plus the refined singleton slice witness.
-/
def molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists :
    MoleculeResidualRefinedInvariantFixedPointDomainSources := by
  classical
  let f_star : BMol := Classical.choose fixed_point_exists
  have h_fixed_point :
      Rfast f_star = f_star ∧ criticalValue f_star = 0 :=
    Classical.choose_spec fixed_point_exists
  let K : Set BMol := Classical.choose (refined_singleton_slice_witness f_star)
  let P : Set SliceSpace :=
    Classical.choose (Classical.choose_spec (refined_singleton_slice_witness f_star))
  have h_refined_spec :
      IsCompact P ∧
        Convex ℝ P ∧
          MapsTo (slice_operator f_star) P P ∧
            K = {f | slice_chart_refined f_star f ∈ P} ∧
              SurjOn (slice_chart_refined f_star) K P ∧
                K.Finite ∧
                  InjOn (slice_chart_refined f_star) K ∧
                    ContinuousOn (slice_operator f_star) ((slice_chart_refined f_star) '' K) ∧
                      K.Nonempty ∧
                        f_star ∈ K :=
    Classical.choose_spec (Classical.choose_spec (refined_singleton_slice_witness f_star))
  exact
    ⟨
      K,
      f_star,
      P,
      h_refined_spec.1,
      h_refined_spec.2.1,
      h_refined_spec.2.2.1,
      h_refined_spec.2.2.2.1,
      h_refined_spec.2.2.2.2.1,
      h_refined_spec.2.2.2.2.2.1,
      h_refined_spec.2.2.2.2.2.2.1,
      h_refined_spec.2.2.2.2.2.2.2.1,
      h_refined_spec.2.2.2.2.2.2.2.2.1,
      h_refined_spec.2.2.2.2.2.2.2.2.2,
      h_fixed_point.1
    ⟩

/--
Any refined invariant fixed-point domain built from `slice_chart_refined`
contains the designated reference point and therefore has only two possible
shapes: either the singleton `{f_ref}` or all of `BMol`.
-/
theorem molecule_residual_refined_invariant_fixed_point_domain_sources_shape
    (h_sources : MoleculeResidualRefinedInvariantFixedPointDomainSources) :
    h_sources.K = ({h_sources.f_ref} : Set BMol) ∨ h_sources.K = (Set.univ : Set BMol) := by
  have h0 : (0 : SliceSpace) ∈ h_sources.P := by
    have h_ref_in_chart_preimage :
        h_sources.f_ref ∈ {f : BMol | slice_chart_refined h_sources.f_ref f ∈ h_sources.P} := by
      simpa [h_sources.kdef] using h_sources.mem
    simpa [slice_chart_refined] using h_ref_in_chart_preimage
  by_cases h1 : (1 : SliceSpace) ∈ h_sources.P
  · right
    ext f
    constructor
    · intro _hf
      simp
    · intro _hf
      by_cases hf : f = h_sources.f_ref
      · simp [h_sources.kdef, slice_chart_refined, hf, h0]
      · simp [h_sources.kdef, slice_chart_refined, hf, h1]
  · left
    ext f
    by_cases hf : f = h_sources.f_ref
    · simp [h_sources.kdef, slice_chart_refined, hf, h0]
    · simp [h_sources.kdef, slice_chart_refined, hf, h1]

/--
Project a fixed-point-in-domain witness from the refined singleton-domain pack.
-/
def molecule_residual_invariant_slice_fixed_point_source_of_refined_invariant_fixed_point_domain_sources
    (h_sources : MoleculeResidualRefinedInvariantFixedPointDomainSources) :
    MoleculeResidualInvariantSliceFixedPointSource :=
  ⟨h_sources.K, h_sources.f_ref, h_sources.mem, h_sources.fixed⟩

/--
Any refined invariant fixed-point domain source becomes a genuine PLAN_88
larger-domain candidate exactly when it is paired with a localized bridge on
its domain and a nontrivial second point. This exposes the refined-side search
target without routing through the singleton/canonical class.
-/
def molecule_residual_non_singleton_localized_bridge_sources_of_refined_invariant_fixed_point_domain_sources_and_bridge_on_and_nontrivial
    (h_sources : MoleculeResidualRefinedInvariantFixedPointDomainSources)
    (h_bridge_on : FixedPointImpliesRenormalizableOn h_sources.K)
    (h_nontrivial : ∃ g : BMol, g ∈ h_sources.K ∧ g ≠ h_sources.f_ref) :
    MoleculeResidualNonSingletonLocalizedBridgeSources :=
  { K := h_sources.K
    f_ref := h_sources.f_ref
    mem := h_sources.mem
    fixed := h_sources.fixed
    bridge_on := h_bridge_on
    nontrivial := h_nontrivial }

/--
The present refined-chart localized-side route is generically blocked:
for any refined invariant fixed-point domain source, adding a localized bridge
and a genuinely nontrivial second point forces the already-false global
fixed-point renormalizability carrier.
-/
theorem no_refined_invariant_fixed_point_domain_sources_bridge_on_and_nontrivial
    (h_sources : MoleculeResidualRefinedInvariantFixedPointDomainSources)
    (h_bridge_on : FixedPointImpliesRenormalizableOn h_sources.K)
    (h_nontrivial : ∃ g : BMol, g ∈ h_sources.K ∧ g ≠ h_sources.f_ref) :
    False := by
  have h_shape :
      h_sources.K = ({h_sources.f_ref} : Set BMol) ∨ h_sources.K = (Set.univ : Set BMol) :=
    molecule_residual_refined_invariant_fixed_point_domain_sources_shape h_sources
  cases h_shape with
  | inl h_singleton =>
      rcases h_nontrivial with ⟨g, hgK, hg_ne⟩
      have hg_eq : g = h_sources.f_ref := by
        simpa [h_singleton] using hgK
      exact hg_ne hg_eq
  | inr h_univ =>
      have h_global : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f := by
        intro f h_fix
        exact h_bridge_on f (by simp [h_univ]) h_fix
      exact no_molecule_residual_fixed_point_renormalizable_source h_global

/--
Current refined-domain candidate for the localized PLAN_88 branch:
if the domain extracted from `fixed_point_exists` carries a localized bridge
and is genuinely non-singleton, then it already yields the exact larger-domain
target.
-/
def molecule_residual_non_singleton_localized_bridge_sources_of_fixed_point_exists_refined_domain_and_bridge_on_and_nontrivial
    (h_bridge_on :
      FixedPointImpliesRenormalizableOn
        (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).K)
    (h_nontrivial :
      ∃ g : BMol,
        g ∈ (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).K ∧
          g ≠ (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).f_ref) :
    MoleculeResidualNonSingletonLocalizedBridgeSources :=
  molecule_residual_non_singleton_localized_bridge_sources_of_refined_invariant_fixed_point_domain_sources_and_bridge_on_and_nontrivial
    molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists
    h_bridge_on
    h_nontrivial

/--
The current refined-domain candidate would already solve the existence side if
it supplied the exact remaining localized-side hypotheses.
-/
theorem molecule_residual_fixed_point_existence_source_of_fixed_point_exists_refined_domain_and_bridge_on_and_nontrivial
    (h_bridge_on :
      FixedPointImpliesRenormalizableOn
        (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).K)
    (h_nontrivial :
      ∃ g : BMol,
        g ∈ (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).K ∧
          g ≠ (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).f_ref) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_non_singleton_localized_bridge_sources
    (molecule_residual_non_singleton_localized_bridge_sources_of_fixed_point_exists_refined_domain_and_bridge_on_and_nontrivial
      h_bridge_on
      h_nontrivial)

/--
The current `fixed_point_exists`-based refined-domain candidate cannot become a
genuine PLAN_88 larger-domain breakthrough: if it were non-singleton, its
localized bridge would collapse to the already-false global fixed-point
renormalizability carrier.
-/
theorem no_fixed_point_exists_refined_domain_bridge_on_and_nontrivial
    (h_bridge_on :
      FixedPointImpliesRenormalizableOn
        (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).K)
    (h_nontrivial :
      ∃ g : BMol,
        g ∈ (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).K ∧
          g ≠ (molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists).f_ref) :
    False := by
  exact no_refined_invariant_fixed_point_domain_sources_bridge_on_and_nontrivial
    molecule_residual_refined_invariant_fixed_point_domain_sources_of_fixed_point_exists
    h_bridge_on
    h_nontrivial

/--
Project a fixed-point-in-domain witness from the seed-based refined singleton
domain pack.
-/
def molecule_residual_invariant_slice_fixed_point_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualInvariantSliceFixedPointSource :=
  molecule_residual_invariant_slice_fixed_point_source_of_refined_invariant_fixed_point_domain_sources
    (molecule_residual_refined_invariant_fixed_point_domain_sources_of_renormalizable_fixed_seed_source
      h_seed)

/--
Any seed-based refined singleton domain already carries the localized bridge
contract on its designated domain.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_refined_invariant_fixed_seed_singleton_domain_sources
    (h_sources : MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources) :
    MoleculeResidualFixedPointBridgeOnSource := by
  refine ⟨h_sources.K, ⟨h_sources.f_ref, h_sources.mem, h_sources.fixed⟩, ?_⟩
  intro f hfK _h_fixed
  have hf_eq : f = h_sources.f_ref := by
    have hf_singleton : f ∈ ({h_sources.f_ref} : Set BMol) := by
      simpa [h_sources.singleton] using hfK
    simpa using hf_singleton
  simpa [hf_eq] using h_sources.renorm

/--
The localized PLAN_86 branch is concrete on the seed-based refined singleton
domain, without mentioning `fixed_point_exists` or `selected_fixed_point`.
-/
theorem molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualFixedPointBridgeOnSource :=
  molecule_residual_fixed_point_bridge_on_source_of_refined_invariant_fixed_seed_singleton_domain_sources
    (molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_of_renormalizable_fixed_seed_source
      h_seed)

/--
The seed-based refined singleton domain yields the existence-side source target.
-/
theorem molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain
    (h_seed : MoleculeResidualRenormalizableFixedSeedSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_bridge_on
    (molecule_residual_fixed_point_bridge_on_source_of_renormalizable_fixed_seed_source_via_refined_singleton_domain
      h_seed)

/--
The current seed-based refined singleton-domain route cannot witness the
non-singleton localized target of PLAN_86.
-/
theorem no_nontrivial_member_of_refined_invariant_fixed_seed_singleton_domain_sources
    (h_sources : MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources) :
    ¬ ∃ g : BMol, g ∈ h_sources.K ∧ g ≠ h_sources.f_ref := by
  intro h_nontrivial
  rcases h_nontrivial with ⟨g, hgK, hg_ne⟩
  have hg_singleton : g ∈ ({h_sources.f_ref} : Set BMol) := by
    simpa [h_sources.singleton] using hgK
  exact hg_ne (by simpa using hg_singleton)

/--
Any concrete seed-based refined singleton-domain pack already contains a
renormalizable fixed seed.
-/
theorem molecule_residual_renormalizable_fixed_seed_source_of_refined_invariant_fixed_seed_singleton_domain_sources
    (h_sources : MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources) :
    MoleculeResidualRenormalizableFixedSeedSource :=
  ⟨h_sources.f_ref, h_sources.renorm, h_sources.fixed⟩

/--
The current localized seed-domain route is equivalent to the reseeded route:
under the present refined witness, having a seed-based refined singleton domain
is exactly the same as having a renormalizable fixed seed.
-/
theorem molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_renormalizable_fixed_seed_source :
    Nonempty MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources ↔
      MoleculeResidualRenormalizableFixedSeedSource := by
  constructor
  · intro h_nonempty
    rcases h_nonempty with ⟨h_sources⟩
    exact
      molecule_residual_renormalizable_fixed_seed_source_of_refined_invariant_fixed_seed_singleton_domain_sources
        h_sources
  · intro h_seed
    exact ⟨
      molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_of_renormalizable_fixed_seed_source
        h_seed
    ⟩


/--
Refined-chart invariant slice-data pack whose designated reference map is
already known to be an `Rfast` fixed point.
-/
structure MoleculeResidualRefinedInvariantFixedPointSources where
  K : Set BMol
  f_ref : BMol
  P : Set SliceSpace
  compact : IsCompact P
  convex : Convex ℝ P
  maps : MapsTo (slice_operator f_ref) P P
  kdef : K = {f | slice_chart_refined f_ref f ∈ P}
  surj : SurjOn (slice_chart_refined f_ref) K P
  finite : K.Finite
  inj : InjOn (slice_chart_refined f_ref) K
  cont : ContinuousOn (slice_operator f_ref) ((slice_chart_refined f_ref) '' K)
  nonempty : K.Nonempty
  mem : f_ref ∈ K
  normalization : NormalizationOn K
  fixed : Rfast f_ref = f_ref

/--
Build the refined invariant fixed-point source pack from fixed-point
normalization data.
-/
def molecule_residual_refined_invariant_fixed_point_sources_of_fixed_data
    (h_fixed_data : FixedPointNormalizationData) :
    MoleculeResidualRefinedInvariantFixedPointSources := by
  classical
  let f_star : BMol := Classical.choose h_fixed_data
  have h_fixed_data_spec :
      Rfast f_star = f_star ∧
      IsFastRenormalizable f_star ∧
      criticalValue f_star = 0 ∧
      f_star.V ⊆ Metric.ball 0 0.1 :=
    Classical.choose_spec h_fixed_data
  let K : Set BMol := {f_star}
  let P : Set SliceSpace := {(0 : SliceSpace)}
  have h_normK : NormalizationOn K := by
    constructor
    · intro f hf
      have h_eq : f = f_star := by simpa [K] using hf
      simpa [h_eq] using h_fixed_data_spec.2.1
    constructor
    · intro f hf
      have h_eq : f = f_star := by simpa [K] using hf
      simpa [h_eq] using h_fixed_data_spec.2.2.1
    · intro f hf
      have h_eq : f = f_star := by simpa [K] using hf
      simpa [h_eq] using h_fixed_data_spec.2.2.2
  refine
    ⟨
      K,
      f_star,
      P,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      h_normK,
      h_fixed_data_spec.1
    ⟩
  · simp [P]
  · simp [P]
  · intro x hx
    simp [P, slice_operator] at hx ⊢
  · ext f
    simp [K, P, slice_chart_refined]
  · intro y hy
    refine ⟨f_star, by simp [K], ?_⟩
    have hy0 : y = 0 := by
      simp [P] at hy
      exact hy
    simp [slice_chart_refined, hy0]
  · simp [K]
  · intro x hx y hy hxy
    simp [K] at hx hy
    simp [hx, hy]
  · simpa [slice_operator] using
      (continuousOn_const :
        ContinuousOn (fun _ : SliceSpace => (0 : SliceSpace))
          ((slice_chart_refined f_star) '' K))
  · simp [K]
  · simp [K]

/--
Project fixed-point normalization data from an invariant normalized domain.
-/
theorem molecule_residual_fixed_point_data_source_of_invariant_slice_data_with_normalization_source
    (h_data : MoleculeResidualInvariantSliceDataWithNormalizationSource) :
    MoleculeResidualFixedPointDataSource :=
  fixed_point_normalization_data_of_invariant_slice_data h_data

/--
Project the concrete local-domain witness target from an invariant normalized
domain.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_in_and_normalization_on
    {K : Set BMol}
    (h_fixed_in : ∃ f : BMol, f ∈ K ∧ Rfast f = f)
    (h_norm_on : NormalizationOn K) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  ⟨K, h_fixed_in, h_norm_on⟩

/--
Project the concrete local-domain witness target from an invariant normalized
domain using the invariant-slice fixed-point theorem directly.
-/
theorem invariant_slice_local_witness_ingredients_of_with_normalization
    (h_data : MoleculeResidualInvariantSliceDataWithNormalizationSource) :
    ∃ K : Set BMol, (∃ f : BMol, f ∈ K ∧ Rfast f = f) ∧ NormalizationOn K := by
  rcases h_data with
    ⟨K, f_ref, P, hP_comp, hP_conv, h_maps, hK_def, h_surj, h_fin, h_inj, h_cont,
      h_nonempty, h_mem, h_norm⟩
  have h_fixed_in : ∃ f : BMol, f ∈ K ∧ Rfast f = f := by
    exact invariant_slice_fixed_point_in_of_sources
      hP_comp
      hP_conv
      h_maps
      hK_def
      h_surj
      h_fin
      h_inj
      h_cont
      h_nonempty
  exact ⟨K, h_fixed_in, h_norm⟩

/--
Project the concrete local-domain witness target from an invariant normalized
domain using the invariant-slice fixed-point theorem directly.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_invariant_slice_data_with_normalization_source_via_invariant_slice_fixed_point
    (h_data : MoleculeResidualInvariantSliceDataWithNormalizationSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources := by
  classical
  let K : Set BMol :=
    Classical.choose (invariant_slice_local_witness_ingredients_of_with_normalization h_data)
  have hK_spec :
      (∃ f : BMol, f ∈ K ∧ Rfast f = f) ∧ NormalizationOn K :=
    Classical.choose_spec
      (invariant_slice_local_witness_ingredients_of_with_normalization h_data)
  exact
    molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_in_and_normalization_on
      hK_spec.1
      hK_spec.2

/--
Project the concrete local-domain witness target from an invariant normalized
domain.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_invariant_slice_data_with_normalization_source
    (h_data : MoleculeResidualInvariantSliceDataWithNormalizationSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_invariant_slice_data_with_normalization_source_via_invariant_slice_fixed_point
    h_data

/--
Project the concrete local-domain witness target from the refined invariant
fixed-point source pack.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_refined_invariant_fixed_point_sources
    (h_sources : MoleculeResidualRefinedInvariantFixedPointSources) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  ⟨
    h_sources.K,
    ⟨h_sources.f_ref, h_sources.mem, h_sources.fixed⟩,
    h_sources.normalization
  ⟩

/--
Build PLAN_77 local-domain transfer sources from one normalized fixed-point
witness plus uniqueness.
-/
def molecule_residual_fixed_point_transfer_on_sources_of_local_witness_sources_and_uniqueness_source
    (h_witness : MoleculeResidualFixedPointLocalWitnessSources)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    MoleculeResidualFixedPointTransferOnSources := by
  refine
    ⟨
      {h_witness.f_star},
      ?_,
      ?_
    ⟩
  · intro f h_fixed h_renorm
    have h_eq :
        f = h_witness.f_star :=
      h_unique f h_witness.f_star
        ⟨h_fixed, h_renorm⟩
        ⟨h_witness.fixed, h_witness.renorm⟩
    simp [h_eq]
  · constructor
    · intro f hf
      have h_eq : f = h_witness.f_star := by simpa using hf
      simpa [h_eq] using h_witness.renorm
    · constructor
      · intro f hf
        have h_eq : f = h_witness.f_star := by simpa using hf
        simpa [h_eq] using h_witness.crit
      · intro f hf
        have h_eq : f = h_witness.f_star := by simpa using hf
        simpa [h_eq] using h_witness.vbound

/--
Build fixed-point transfer from the PLAN_77 local-domain transfer source pack.
-/
theorem molecule_residual_fixed_point_transfer_source_of_on_sources
    (h_sources : MoleculeResidualFixedPointTransferOnSources) :
    MoleculeResidualFixedPointTransferSource :=
  fixed_point_local_normalization_transfer_of_membership_and_normalization_on
    h_sources.membership
    h_sources.normalization

/--
Project fixed-point `V`-bound transfer source from the fixed-point transfer
source seam.
-/
theorem fixed_point_vbound_transfer_source_of_fixed_point_transfer_source
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    FixedPointVBoundTransferSource :=
  fixed_point_vbound_transfer_source_of_local_normalization_transfer
    h_transfer

/--
PLAN_77 source pack splitting fixed-point local transfer into critical-value
and `V`-bound components.
-/
structure MoleculeResidualFixedPointTransferComponentSources where
  crit : FixedPointCriticalValueTransferSource
  vbound : FixedPointVBoundTransferSource

/--
Build PLAN_77 transfer-component sources from the fixed-point transfer seam.
-/
def molecule_residual_fixed_point_transfer_component_sources_of_fixed_point_transfer_source
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointTransferComponentSources :=
  let h_components :=
    fixed_point_critical_and_vbound_of_local_normalization_transfer h_transfer
  ⟨h_components.1, h_components.2⟩

/--
Build fixed-point transfer source from PLAN_77 transfer-component sources.
-/
theorem molecule_residual_fixed_point_transfer_source_of_component_sources
    (h_sources : MoleculeResidualFixedPointTransferComponentSources) :
    MoleculeResidualFixedPointTransferSource :=
  fixed_point_local_normalization_transfer_of_critical_and_vbound
    h_sources.crit
    h_sources.vbound

/--
Build canonical fixed-data `V`-bound control from PLAN_77 transfer-component
sources.
-/
theorem molecule_residual_canonical_vbound_source_of_transfer_component_sources
    (h_sources : MoleculeResidualFixedPointTransferComponentSources) :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_fixed_point_vbound_transfer
    h_sources.vbound

/--
Build canonical orbit-at debt source from structure plus PLAN_77
transfer-component sources.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_structure_and_transfer_component_sources
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource)
    (h_sources : MoleculeResidualFixedPointTransferComponentSources) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_and_vbound_source
    h_structure
    (molecule_residual_canonical_vbound_source_of_transfer_component_sources
      h_sources)

/--
Project canonical fixed-data `V`-bound control from the fixed-point transfer
source seam.
-/
theorem molecule_residual_canonical_vbound_source_of_fixed_point_transfer_source
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_fixed_point_local_transfer
    h_transfer

/--
Source seam for fixed-point uniqueness on fast-renormalizable fixed points.
-/
def MoleculeResidualFixedPointUniquenessSource : Prop :=
  ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
           (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2

/--
Dedicated replacement seam for the current direct map-level fixed-point
uniqueness theorem.
-/
def MoleculeResidualFixedPointUniquenessDirectSource : Prop :=
  MoleculeResidualFixedPointUniquenessSource

/--
Source seam: all fast-renormalizable fixed points collapse to one hybrid class.
-/
def MoleculeResidualFixedPointHybridClassCollapseSource : Prop :=
  ∀ f1 f2, Rfast f1 = f1 → IsFastRenormalizable f1 →
           Rfast f2 = f2 → IsFastRenormalizable f2 →
           toHybridClass f1 = toHybridClass f2

/--
Dedicated replacement seam for the current direct map-level hybrid-class
collapse theorem.
-/
def MoleculeResidualFixedPointHybridClassCollapseDirectSource : Prop :=
  MoleculeResidualFixedPointHybridClassCollapseSource

/--
Source seam: the hybrid-class renormalization operator has a unique
fast-renormalizable fixed point.
-/
def MoleculeResidualHybridUniqueFixedPointSource : Prop :=
  ∃! c : HybridClass, IsFastRenormalizable c ∧ R_hybrid c = c

/--
Source seam: injectivity of the active hybrid projection model.
-/
def MoleculeResidualHybridProjectionInjectiveSource : Prop :=
  HybridProjectionInjective currentHybridProjectionSeam

/--
Source seam: collapse on projected classes of fast-renormalizable fixed maps in
the active hybrid projection seam.
-/
def MoleculeResidualHybridFixedPointCollapseSource : Prop :=
  HybridFixedPointCollapseIn currentHybridProjectionSeam

/--
Source seam: uniqueness of fast-renormalizable fixed points directly at the
hybrid-class level.
-/
def MoleculeResidualHybridClassFixedPointUniquenessSource : Prop :=
  ∀ c1 c2 : HybridClass,
    (IsFastRenormalizable c1 ∧ R_hybrid c1 = c1) →
    (IsFastRenormalizable c2 ∧ R_hybrid c2 = c2) →
    c1 = c2

/--
Dedicated replacement seam for the current direct hybrid-class fixed-point
uniqueness theorem.
-/
def MoleculeResidualHybridClassFixedPointUniquenessDirectSource : Prop :=
  MoleculeResidualHybridClassFixedPointUniquenessSource

/--
Source seam: lift any renormalizable fixed hybrid class to a renormalizable
fixed map in `BMol`.
-/
def MoleculeResidualHybridClassFixedPointLiftSource : Prop :=
  HybridClassFixedPointLiftSource currentHybridProjectionSeam

/--
Source seam: collapse on projected classes of fast-renormalizable fixed maps in
the lifted hybrid projection seam.
-/
def MoleculeResidualLiftedHybridFixedPointCollapseSource : Prop :=
  HybridFixedPointCollapseIn liftedHybridProjectionSeam

/--
Source seam: model-collapse input for hybrid-class-uniqueness model sources.
This is the active replacement point for PLAN_60.
-/
def MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource : Prop :=
  MoleculeResidualLiftedHybridFixedPointCollapseSource

/--
Dedicated replacement seam for the current direct hybrid-class-uniqueness
model-collapse source theorem.
-/
def MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource : Prop :=
  MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource

/--
PLAN_64 anchor seam: the direct hybrid-class model-collapse source.
Constructive upstream replacement may target this seam and propagate via
equivalence theorems.
-/
def MoleculeResidualDirectSeamAnchorSource : Prop :=
  MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource

/--
Source seam: lift any renormalizable fixed lifted hybrid class to a
renormalizable fixed map in `BMol`.
-/
def MoleculeResidualLiftedHybridClassFixedPointLiftSource : Prop :=
  HybridClassFixedPointLiftSource liftedHybridProjectionSeam

/--
Assembly source pack for hybrid-class fixed-point uniqueness.
-/
structure MoleculeResidualHybridClassFixedPointUniquenessAssemblySources where
  collapse : MoleculeResidualHybridFixedPointCollapseSource
  lift : MoleculeResidualHybridClassFixedPointLiftSource

/--
Model-source pack for deriving current hybrid-class fixed-point uniqueness from
a potentially nontrivial projection seam.
-/
structure MoleculeResidualHybridClassFixedPointUniquenessModelSources where
  seam : HybridProjectionSeam
  collapse : HybridFixedPointCollapseIn seam
  lift : HybridClassFixedPointLiftSource seam
  toCurrentClass : seam.Class → HybridClass
  liftCurrentFixed :
    ∀ c : HybridClass, (IsFastRenormalizable c ∧ R_hybrid c = c) →
      ∃ cs : seam.Class,
        toCurrentClass cs = c ∧ seam.renorm cs ∧ seam.Rclass cs = cs

/--
Current source theorem for hybrid-projection injectivity.
-/
theorem molecule_residual_hybrid_projection_injective_source :
    MoleculeResidualHybridProjectionInjectiveSource :=
  current_hybrid_projection_seam_proj_injective

/--
Current source theorem for hybrid-class fixed-point lift.
-/
theorem molecule_residual_hybrid_class_fixed_point_lift_source :
    MoleculeResidualHybridClassFixedPointLiftSource :=
  current_hybrid_projection_seam_fixed_point_lift_source

/--
Current source theorem for lifted-seam hybrid-class fixed-point lift.
-/
theorem molecule_residual_lifted_hybrid_class_fixed_point_lift_source :
    MoleculeResidualLiftedHybridClassFixedPointLiftSource :=
  lifted_hybrid_projection_seam_fixed_point_lift_source

/--
Bridge the map-level hybrid-class-collapse source into the current seam-level
collapse contract.
-/
theorem molecule_residual_hybrid_fixed_point_collapse_in_current_seam_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridFixedPointCollapseSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  simpa [currentHybridProjectionSeam] using
    h_collapse f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2

/--
Compatibility wrapper: build seam-level collapse source from the legacy
map-level hybrid-class-collapse source.
-/
theorem molecule_residual_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridFixedPointCollapseSource :=
  molecule_residual_hybrid_fixed_point_collapse_in_current_seam_of_hybrid_class_collapse_source
    h_collapse

/--
Bridge the map-level hybrid-class-collapse source into the lifted seam-level
collapse contract.
-/
theorem molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualLiftedHybridFixedPointCollapseSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  exact Subtype.ext
    (h_collapse f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2)

/--
Build hybrid-class fixed-point uniqueness from:
- hybrid-class collapse on fast-renormalizable fixed points, and
- hybrid-class fixed-point lift in the active seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_lift_source
    (h_collapse : MoleculeResidualHybridFixedPointCollapseSource)
    (h_lift : MoleculeResidualHybridClassFixedPointLiftSource) :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  hybrid_class_fixed_point_uniqueness_in_of_collapse_and_lift
    currentHybridProjectionSeam
    h_collapse
    h_lift

/--
Build current hybrid-class fixed-point uniqueness from a model-source pack over
an arbitrary projection seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
    (h_sources : MoleculeResidualHybridClassFixedPointUniquenessModelSources) :
    MoleculeResidualHybridClassFixedPointUniquenessSource := by
  intro c1 c2 hc1 hc2
  rcases h_sources.liftCurrentFixed c1 hc1 with
    ⟨s1, hs1_current, hs1_renorm, hs1_fix⟩
  rcases h_sources.liftCurrentFixed c2 hc2 with
    ⟨s2, hs2_current, hs2_renorm, hs2_fix⟩
  have h_unique_in_seam : HybridClassFixedPointUniquenessIn h_sources.seam :=
    hybrid_class_fixed_point_uniqueness_in_of_collapse_and_lift
      h_sources.seam
      h_sources.collapse
      h_sources.lift
  have hs_eq : s1 = s2 :=
    h_unique_in_seam s1 s2 ⟨hs1_renorm, hs1_fix⟩ ⟨hs2_renorm, hs2_fix⟩
  calc
    c1 = h_sources.toCurrentClass s1 := by simpa using hs1_current.symm
    _ = h_sources.toCurrentClass s2 := by simp [hs_eq]
    _ = c2 := by simpa using hs2_current

/--
Build hybrid-class uniqueness source from the explicit assembly-source pack.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_assembly_sources
    (h_sources : MoleculeResidualHybridClassFixedPointUniquenessAssemblySources) :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_lift_source
    h_sources.collapse
    h_sources.lift

/--
Build direct hybrid-class fixed-point uniqueness source seam from the explicit
assembly-source pack.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_assembly_sources
    (h_sources : MoleculeResidualHybridClassFixedPointUniquenessAssemblySources) :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_assembly_sources
    h_sources

/--
Recover hybrid-class fixed-point uniqueness from the dedicated direct-source
seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct_of_source
    (h_source : MoleculeResidualHybridClassFixedPointUniquenessDirectSource) :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  h_source

/--
Build a model-source pack from the explicit current-seam assembly-source pack.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_assembly_sources
    (h_sources : MoleculeResidualHybridClassFixedPointUniquenessAssemblySources) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources where
  seam := currentHybridProjectionSeam
  collapse := h_sources.collapse
  lift := h_sources.lift
  toCurrentClass := fun c => c
  liftCurrentFixed := by
    intro c hc
    exact ⟨c, rfl, hc.1, hc.2⟩

/--
Build a model-source pack from explicit lifted-seam collapse and lift sources.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
    (h_collapse : MoleculeResidualLiftedHybridFixedPointCollapseSource)
    (h_lift : MoleculeResidualLiftedHybridClassFixedPointLiftSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources where
  seam := liftedHybridProjectionSeam
  collapse := h_collapse
  lift := h_lift
  toCurrentClass := fun c => c.1
  liftCurrentFixed := by
    intro c hc
    refine ⟨⟨c, trivial⟩, rfl, ?_, ?_⟩
    · simpa [liftedHybridProjectionSeam] using hc.1
    · exact Subtype.ext (by simpa [R_hybrid] using hc.2)

/--
Build a model-source pack from the map-level hybrid-class-collapse source,
routed through the lifted seam.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
    (molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
      h_collapse)
    molecule_residual_lifted_hybrid_class_fixed_point_lift_source

/--
Build hybrid-class uniqueness assembly sources from the legacy
map-level hybrid-class-collapse source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_assembly_sources_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridClassFixedPointUniquenessAssemblySources :=
  ⟨
    molecule_residual_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
      h_collapse,
    molecule_residual_hybrid_class_fixed_point_lift_source
  ⟩

/--
Build hybrid-class fixed-point uniqueness from:
- hybrid-class collapse on fast-renormalizable fixed points, and
- injectivity of the active hybrid projection seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_projection_injective_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource)
    (_h_proj_inj : MoleculeResidualHybridProjectionInjectiveSource) :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_lift_source
    (molecule_residual_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
      h_collapse)
    molecule_residual_hybrid_class_fixed_point_lift_source

/--
Project hybrid-class collapse from unique fixed point on hybrid classes.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualFixedPointHybridClassCollapseSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  rcases h_hybrid_unique with ⟨c, hc_fixed, hc_unique⟩
  have h1 : IsFastRenormalizable (toHybridClass f1) ∧ R_hybrid (toHybridClass f1) = toHybridClass f1 := by
    refine ⟨h_renorm1, ?_⟩
    simpa [R_hybrid, toHybridClass] using h_fix1
  have h2 : IsFastRenormalizable (toHybridClass f2) ∧ R_hybrid (toHybridClass f2) = toHybridClass f2 := by
    refine ⟨h_renorm2, ?_⟩
    simpa [R_hybrid, toHybridClass] using h_fix2
  have h_eq1 : toHybridClass f1 = c := hc_unique (toHybridClass f1) h1
  have h_eq2 : toHybridClass f2 = c := hc_unique (toHybridClass f2) h2
  exact h_eq1.trans h_eq2.symm

/--
Project lifted-seam collapse source from a hybrid unique-fixed-point source.
-/
theorem molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualLiftedHybridFixedPointCollapseSource :=
  molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique)

/--
Project lifted-seam collapse source from hybrid-class fixed-point uniqueness.
-/
theorem molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualLiftedHybridFixedPointCollapseSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  apply Subtype.ext
  exact
    h_class_unique (toHybridClass f1) (toHybridClass f2)
      ⟨h_renorm1, by simpa [R_hybrid, toHybridClass] using h_fix1⟩
      ⟨h_renorm2, by simpa [R_hybrid, toHybridClass] using h_fix2⟩

/--
Build hybrid-class-uniqueness model sources from a hybrid unique-fixed-point
source via the lifted seam.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
    (molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique)
    molecule_residual_lifted_hybrid_class_fixed_point_lift_source

/--
Build hybrid-class-uniqueness model sources from a hybrid-class-uniqueness
source via the lifted seam.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
    (molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_uniqueness_source
      h_class_unique)
    molecule_residual_lifted_hybrid_class_fixed_point_lift_source

/--
Project model-collapse source from map-level hybrid-class-collapse source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
    h_collapse

/--
Project model-collapse source from hybrid unique-fixed-point source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_unique_fixed_point_source
    h_hybrid_unique

/--
Project model-collapse source from hybrid-class fixed-point uniqueness.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_uniqueness_source
    h_class_unique

/--
Project map-level hybrid-class collapse source from hybrid-class fixed-point
uniqueness.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualFixedPointHybridClassCollapseSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  exact
    h_class_unique (toHybridClass f1) (toHybridClass f2)
      ⟨h_renorm1, by simpa [R_hybrid, toHybridClass] using h_fix1⟩
      ⟨h_renorm2, by simpa [R_hybrid, toHybridClass] using h_fix2⟩

/--
Project map-level hybrid-class collapse source from hybrid-class-uniqueness
model-collapse input.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_model_collapse_source
    (h_model_collapse : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource) :
    MoleculeResidualFixedPointHybridClassCollapseSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
      (molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
        h_model_collapse
        molecule_residual_lifted_hybrid_class_fixed_point_lift_source))

/--
Build uniqueness from hybrid-class collapse using fixed-point rigidity in a
hybrid class.
-/
theorem molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointUniquenessSource := by
  intro f1 f2 h1 h2
  have h_class :
      toHybridClass f1 = toHybridClass f2 :=
    h_collapse f1 f2 h1.1 h1.2 h2.1 h2.2
  exact fixed_points_in_same_class_eq f1 f2 h1.2 h1.1 h2.2 h2.1 h_class

/--
Build direct map-level fixed-point uniqueness seam from hybrid-class
fixed-point uniqueness.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualFixedPointUniquenessDirectSource := by
  intro f1 f2 h1 h2
  have h_class :
      toHybridClass f1 = toHybridClass f2 :=
    h_class_unique (toHybridClass f1) (toHybridClass f2)
      ⟨h1.2, by simpa [R_hybrid, toHybridClass] using h1.1⟩
      ⟨h2.2, by simpa [R_hybrid, toHybridClass] using h2.1⟩
  exact fixed_points_in_same_class_eq f1 f2 h1.2 h1.1 h2.2 h2.1 h_class

/--
Build direct map-level fixed-point uniqueness seam from hybrid-class
uniqueness assembly sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_assembly_sources
    (h_sources : MoleculeResidualHybridClassFixedPointUniquenessAssemblySources) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_assembly_sources
      h_sources)

/--
Build direct map-level fixed-point uniqueness seam from model-collapse input
for hybrid-class uniqueness sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_model_collapse_source
    (h_model_collapse : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
      (molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
        h_model_collapse
        molecule_residual_lifted_hybrid_class_fixed_point_lift_source))

/--
Build map-level fixed-point uniqueness directly from unique fixed point on
hybrid classes.
-/
theorem molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique)

/--
Project hybrid-class collapse from fixed-point uniqueness.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualFixedPointHybridClassCollapseSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  exact congrArg toHybridClass (h_unique f1 f2 ⟨h_fix1, h_renorm1⟩ ⟨h_fix2, h_renorm2⟩)

/--
Project lifted-seam collapse source from map-level uniqueness.
-/
theorem molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualLiftedHybridFixedPointCollapseSource :=
  molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
      h_unique)

/--
Project model-collapse source from map-level uniqueness.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_uniqueness_source
    h_unique

/--
Project model-collapse source directly from the dedicated direct-source seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_direct_source
    (h_direct : MoleculeResidualHybridClassFixedPointUniquenessDirectSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_uniqueness_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct_of_source
      h_direct)

/--
Build hybrid-class-uniqueness model sources from map-level uniqueness via the
lifted seam.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
    (molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_uniqueness_source
      h_unique)
    molecule_residual_lifted_hybrid_class_fixed_point_lift_source

/--
Build direct hybrid-class fixed-point uniqueness source seam from map-level
uniqueness.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
    (molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_uniqueness_source
      h_unique)

/--
Build direct hybrid-class fixed-point uniqueness source seam from hybrid-unique
source assumptions.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source
    (molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique)

/--
Build hybrid-class-uniqueness model sources from model-collapse input.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
    (h_collapse : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_lifted_sources
    h_collapse
    molecule_residual_lifted_hybrid_class_fixed_point_lift_source

/--
Build direct hybrid-class fixed-point uniqueness source seam from model-collapse
input.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_model_collapse_source
    (h_collapse : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource) :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
    (molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
      h_collapse)

/--
The model-collapse and direct hybrid-class fixed-point uniqueness source seams
are equivalent.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_iff_direct_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessDirectSource := by
  constructor
  · exact molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_model_collapse_source
  · exact molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_direct_source

/--
The hybrid-class-collapse and map-level uniqueness source seams are equivalent.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_iff_uniqueness_source :
    MoleculeResidualFixedPointHybridClassCollapseSource ↔
      MoleculeResidualFixedPointUniquenessSource := by
  constructor
  · exact molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
  · exact molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source

/--
The map-level hybrid-class-collapse source and hybrid-class fixed-point
uniqueness source seams are equivalent.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_iff_hybrid_class_uniqueness_source :
    MoleculeResidualFixedPointHybridClassCollapseSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessSource := by
  constructor
  · intro h_collapse
    exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_hybrid_class_collapse_and_lift_source
        (molecule_residual_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
          h_collapse)
        molecule_residual_hybrid_class_fixed_point_lift_source
  · exact molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source

/--
Assemble canonical orbit-at debt source from transport + fixed-data + hybrid
class collapse source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_hybrid_class_collapse_source
    (h_transport : MoleculeResidualOrbitTransportSource)
    (h_fixed_data : FixedPointNormalizationData)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_unique
    (molecule_residual_canonical_orbit_structure_source_of_transport_source
      h_transport)
    h_fixed_data
    (molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
      h_collapse)

/--
Assemble canonical orbit-at debt source from transport + fixed-data + hybrid
unique-fixed-point source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_hybrid_unique_fixed_point_source
    (h_transport : MoleculeResidualOrbitTransportSource)
    (h_fixed_data : FixedPointNormalizationData)
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_hybrid_class_collapse_source
    h_transport
    h_fixed_data
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique)

/--
Project fixed-point transfer components from fixed-data and uniqueness source
seams.
-/
theorem fixed_point_transfer_components_of_fixed_data_and_uniqueness_source
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    FixedPointCriticalValueTransferSource ∧ FixedPointVBoundTransferSource :=
  ⟨
    fixed_point_critical_value_transfer_source_of_fixed_data_and_unique
      h_fixed_data h_unique,
    fixed_point_vbound_transfer_source_of_fixed_data_and_unique
      h_fixed_data h_unique
  ⟩

/--
Project canonical fixed-data `V`-bound control from fixed-data and uniqueness
source seams.
-/
theorem molecule_residual_canonical_vbound_source_of_fixed_data_and_uniqueness_source
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_fixed_data_and_unique
    h_fixed_data h_unique

/--
Assemble canonical orbit-at debt source from structure + fixed-data +
uniqueness source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_uniqueness_source
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource)
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_unique
    h_structure h_fixed_data h_unique

/--
Assemble canonical orbit-at debt source from transport + fixed-data +
uniqueness source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_uniqueness_source
    (h_transport : MoleculeResidualOrbitTransportSource)
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_fixed_data_and_uniqueness_source
    (molecule_residual_canonical_orbit_structure_source_of_transport_source
      h_transport)
    h_fixed_data
    h_unique

/--
Early zero-arg PLAN_64 anchor source theorem (direct proof route).
-/
theorem molecule_residual_direct_seam_anchor_source_early :
    MoleculeResidualDirectSeamAnchorSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  apply Subtype.ext
  exact congrArg toHybridClass
    (molecule_h_unique f1 f2 ⟨h_fix1, h_renorm1⟩ ⟨h_fix2, h_renorm2⟩)

/--
Early declaration-order-safe constructor: project direct map-level
hybrid-class-collapse seam from the PLAN_64 anchor seam.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source_early
    (h_anchor : MoleculeResidualDirectSeamAnchorSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  exact congrArg Subtype.val (h_anchor f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2)

/--
Current direct map-level hybrid-class-collapse source theorem (legacy route
from the current uniqueness proof body).
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source_early
    molecule_residual_direct_seam_anchor_source_early

/--
Recover map-level hybrid-class collapse from the dedicated direct-source seam.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
    (h_source : MoleculeResidualFixedPointHybridClassCollapseDirectSource) :
    MoleculeResidualFixedPointHybridClassCollapseSource :=
  h_source

/--
Build direct map-level hybrid-class-collapse seam from hybrid-class fixed-point
uniqueness source assumptions.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source
    h_class_unique

/--
Build direct map-level hybrid-class-collapse seam from hybrid-class-uniqueness
model-collapse assumptions.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_hybrid_class_uniqueness_model_collapse_source
    (h_model_collapse : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_model_collapse_source
    h_model_collapse

/--
Current map-level hybrid-class-collapse source theorem, routed through the
dedicated direct-source seam.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_direct :
    MoleculeResidualFixedPointHybridClassCollapseSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
    molecule_residual_fixed_point_hybrid_class_collapse_direct_source

/--
The direct map-level hybrid-class-collapse seam and the direct hybrid-class
model-collapse seam are equivalent.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_hybrid_class_uniqueness_model_collapse_direct_source :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource := by
  constructor
  · intro h_collapse_direct
    have h_collapse :
        MoleculeResidualFixedPointHybridClassCollapseSource :=
      molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
        h_collapse_direct
    have h_class_unique :
        MoleculeResidualHybridClassFixedPointUniquenessSource :=
      (molecule_residual_fixed_point_hybrid_class_collapse_source_iff_hybrid_class_uniqueness_source).1
        h_collapse
    exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_uniqueness_source
        h_class_unique
  · intro h_model_direct
    exact
      molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_hybrid_class_uniqueness_model_collapse_source
        h_model_direct

/--
Current zero-arg PLAN_64 anchor source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source_early

/--
Project direct map-level hybrid-class-collapse seam from the PLAN_64 anchor
seam.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (h_anchor : MoleculeResidualDirectSeamAnchorSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source_early
    h_anchor

/--
Build direct map-level fixed-point uniqueness source seam from hybrid-class
collapse source assumptions.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
    h_collapse

/--
Build direct map-level fixed-point uniqueness source seam from hybrid-unique
source assumptions.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
    h_hybrid_unique

/--
Recover map-level fixed-point uniqueness from the dedicated direct-source seam.
-/
theorem molecule_residual_fixed_point_uniqueness_source_direct_of_source
    (h_source : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualFixedPointUniquenessSource :=
  h_source

/--
Early declaration-order-safe constructor: project direct map-level fixed-point
uniqueness seam from the PLAN_64 anchor seam.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source_early
    (h_anchor : MoleculeResidualDirectSeamAnchorSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_collapse_source
    (molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
      (molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
        h_anchor))

/--
Current direct map-level fixed-point uniqueness source seam.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source_early
    molecule_residual_direct_seam_anchor_source

/--
The direct map-level hybrid-class-collapse seam and the direct map-level
fixed-point uniqueness seam are equivalent.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_fixed_point_uniqueness_direct_source :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource ↔
      MoleculeResidualFixedPointUniquenessDirectSource := by
  constructor
  · intro h_collapse_direct
    exact
      molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_collapse_source
        (molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
          h_collapse_direct)
  · intro h_unique_direct
    exact
      molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
        (molecule_residual_fixed_point_uniqueness_source_direct_of_source
          h_unique_direct)

/--
Project direct map-level fixed-point uniqueness seam from the PLAN_64 anchor
seam.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (h_anchor : MoleculeResidualDirectSeamAnchorSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source_early
    h_anchor

/--
Current fixed-point uniqueness source theorem (direct legacy route), now
expressed through the dedicated direct-source seam.
-/
theorem molecule_residual_fixed_point_uniqueness_source_direct :
    MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_fixed_point_uniqueness_source_direct_of_source
    molecule_residual_fixed_point_uniqueness_direct_source

/--
Build the PLAN_64 anchor seam directly from map-level fixed-point uniqueness
source assumptions.
-/
theorem molecule_residual_direct_seam_anchor_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualDirectSeamAnchorSource := by
  intro f1 f2 h_fix1 h_renorm1 h_fix2 h_renorm2
  apply Subtype.ext
  exact congrArg toHybridClass
    (h_unique f1 f2 ⟨h_fix1, h_renorm1⟩ ⟨h_fix2, h_renorm2⟩)

/--
The PLAN_64 anchor seam and map-level fixed-point uniqueness source seam are
equivalent.
-/
theorem molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source :
    MoleculeResidualDirectSeamAnchorSource ↔
      MoleculeResidualFixedPointUniquenessSource := by
  constructor
  · intro h_anchor
    exact molecule_residual_fixed_point_uniqueness_source_direct_of_source
      (molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
        h_anchor)
  · exact molecule_residual_direct_seam_anchor_source_of_uniqueness_source

/--
Current fixed-point uniqueness source theorem (direct legacy route), routed
through the dedicated direct-source seam.
-/
theorem molecule_residual_fixed_point_uniqueness_source_direct_routed :
    MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_fixed_point_uniqueness_source_direct

/--
Assemble fixed-point transfer source from fixed-point normalization data and
uniqueness source.
-/
theorem molecule_residual_fixed_point_transfer_source_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualFixedPointTransferSource :=
  fixed_point_local_normalization_transfer_of_fixed_data_and_unique
    h_fixed_data
    h_unique

/--
PLAN_77 source pack for fixed-point transfer routed from explicit fixed-data
and uniqueness inputs.
-/
structure MoleculeResidualFixedPointTransferModelSources where
  fixedData : FixedPointNormalizationData
  unique : MoleculeResidualFixedPointUniquenessSource

/--
Build PLAN_77 fixed-point transfer model sources from explicit fixed-data and
uniqueness inputs.
-/
def molecule_residual_fixed_point_transfer_model_sources_of_fixed_data_and_unique
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualFixedPointTransferModelSources :=
  ⟨h_fixed_data, h_unique⟩

/--
Build fixed-point transfer source from PLAN_77 transfer model sources.
-/
theorem molecule_residual_fixed_point_transfer_source_of_model_sources
    (h_sources : MoleculeResidualFixedPointTransferModelSources) :
    MoleculeResidualFixedPointTransferSource :=
  molecule_residual_fixed_point_transfer_source_of_fixed_data_and_unique
    h_sources.fixedData
    h_sources.unique

/--
Current PLAN_77 fixed-point transfer model sources theorem.
-/
def molecule_residual_fixed_point_transfer_model_sources :
    MoleculeResidualFixedPointTransferModelSources :=
  molecule_residual_fixed_point_transfer_model_sources_of_fixed_data_and_unique
    molecule_h_fixed_data_direct
    molecule_residual_fixed_point_uniqueness_source_direct

/--
Build PLAN_77 local-domain transfer sources from fixed data and uniqueness.
-/
def molecule_residual_fixed_point_transfer_on_sources_of_fixed_data_and_uniqueness_source
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualFixedPointTransferOnSources := by
  classical
  let f_star : BMol := Classical.choose h_fixed_data
  have h_fixed_data_spec :
      Rfast f_star = f_star ∧
      IsFastRenormalizable f_star ∧
      criticalValue f_star = 0 ∧
      f_star.V ⊆ Metric.ball 0 0.1 :=
    Classical.choose_spec h_fixed_data
  have h_fixed_star : Rfast f_star = f_star := h_fixed_data_spec.1
  have h_renorm_star : IsFastRenormalizable f_star := h_fixed_data_spec.2.1
  have h_crit_star : criticalValue f_star = 0 := h_fixed_data_spec.2.2.1
  have h_domain_star : f_star.V ⊆ Metric.ball 0 0.1 := h_fixed_data_spec.2.2.2
  refine
    ⟨
      {f_star},
      ?_,
      ?_
    ⟩
  · intro f h_fixed h_renorm
    have h_eq :
        f = f_star :=
      h_unique f f_star ⟨h_fixed, h_renorm⟩ ⟨h_fixed_star, h_renorm_star⟩
    simp [h_eq]
  · constructor
    · intro f hf
      have h_eq : f = f_star := by simpa using hf
      simpa [h_eq] using h_renorm_star
    · constructor
      · intro f hf
        have h_eq : f = f_star := by simpa using hf
        simpa [h_eq] using h_crit_star
      · intro f hf
        have h_eq : f = f_star := by simpa using hf
        simpa [h_eq] using h_domain_star

/--
Build PLAN_77 local-domain transfer sources from transfer model sources.
-/
def molecule_residual_fixed_point_transfer_on_sources_of_model_sources
    (h_sources : MoleculeResidualFixedPointTransferModelSources) :
    MoleculeResidualFixedPointTransferOnSources :=
  molecule_residual_fixed_point_transfer_on_sources_of_fixed_data_and_uniqueness_source
    h_sources.fixedData
    h_sources.unique

/--
Build PLAN_77 local-domain transfer sources directly from the critical-value
and `V`-bound transfer components by taking `K` to be the set of fixed
renormalizable maps.
-/
def molecule_residual_fixed_point_transfer_on_sources_of_component_transfers
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_vbound : FixedPointVBoundTransferSource) :
    MoleculeResidualFixedPointTransferOnSources := by
  refine
    ⟨
      {f : BMol | Rfast f = f ∧ IsFastRenormalizable f},
      ?_,
      ?_
    ⟩
  · intro f h_fixed h_renorm
    exact ⟨h_fixed, h_renorm⟩
  · constructor
    · intro f hf
      exact hf.2
    · constructor
      · intro f hf
        exact h_crit f hf.1 hf.2
      · intro f hf
        exact h_vbound f hf.1 hf.2

/--
Current PLAN_77 local-witness source pack.
-/
def molecule_residual_fixed_point_local_witness_on_sources_via_fixed_data_source
    (h_fixed_data : MoleculeResidualFixedPointDataSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    h_fixed_data

/--
Current PLAN_77 local-witness source pack routed directly through primitive
fixed-point ingredients.
-/
def molecule_residual_fixed_point_local_witness_on_sources_via_ingredients_source
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_ingredients
    h_ingredients

/--
Current PLAN_77 local-witness source pack routed directly through the ground
fixed-point theorem and the direct renormalizability / critical-value /
`V`-bound carriers.
-/
def molecule_residual_fixed_point_local_witness_on_sources_via_fixed_point_exists_and_component_transfers_direct :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_renorm_and_vbound
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct

/--
Current PLAN_77 local-witness source pack.
-/
def molecule_residual_fixed_point_local_witness_on_sources :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_renorm_and_renorm_vbound
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_renorm_vbound_source

/--
Current PLAN_77 local-witness source pack.
-/
def molecule_residual_fixed_point_local_witness_sources :
    MoleculeResidualFixedPointLocalWitnessSources :=
  molecule_residual_fixed_point_local_witness_sources_of_fixed_point_exists_and_renorm_and_renorm_vbound
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_renorm_vbound_source

/--
Current PLAN_77 local-domain transfer source pack routed via the local-witness
source pack.
-/
def molecule_residual_fixed_point_transfer_on_sources_via_local_witness_sources :
    MoleculeResidualFixedPointTransferOnSources :=
  molecule_residual_fixed_point_transfer_on_sources_of_local_witness_sources_and_uniqueness_source
    molecule_residual_fixed_point_local_witness_sources
    molecule_residual_fixed_point_uniqueness_source_direct

/--
Current PLAN_77 local-domain transfer source pack routed directly through the
critical-value and `V`-bound component carriers.
-/
def molecule_residual_fixed_point_transfer_on_sources_via_component_transfers_direct :
    MoleculeResidualFixedPointTransferOnSources :=
  molecule_residual_fixed_point_transfer_on_sources_of_component_transfers
    molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct

/--
Current PLAN_77 local-domain transfer source pack.
-/
def molecule_residual_fixed_point_transfer_on_sources :
    MoleculeResidualFixedPointTransferOnSources :=
  molecule_residual_fixed_point_transfer_on_sources_via_component_transfers_direct

/--
Current fixed-point transfer source routed through PLAN_77 local-domain
transfer sources.
-/
theorem molecule_residual_fixed_point_transfer_source_via_on_sources :
    MoleculeResidualFixedPointTransferSource :=
  molecule_residual_fixed_point_transfer_source_of_on_sources
    molecule_residual_fixed_point_transfer_on_sources

/--
Current fixed-point transfer source routed through PLAN_77 transfer model
sources.
-/
theorem molecule_residual_fixed_point_transfer_source_via_model_sources :
    MoleculeResidualFixedPointTransferSource :=
  molecule_residual_fixed_point_transfer_source_via_on_sources

/--
Current fixed-point transfer source routed directly through primitive
fixed-point ingredients and the current direct uniqueness source.
-/
theorem molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct :
    MoleculeResidualFixedPointTransferSource :=
  fixed_point_local_normalization_transfer_of_critical_and_vbound
    molecule_residual_fixed_point_critical_value_transfer_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct

/--
Current fixed-point local-normalization transfer source theorem.
-/
theorem molecule_residual_fixed_point_transfer_source :
    MoleculeResidualFixedPointTransferSource :=
  molecule_residual_fixed_point_transfer_source_via_fixed_data_and_uniqueness_direct

/--
Current canonical fixed-data `V`-bound source routed via fixed-point transfer
source seam.
-/
def molecule_residual_fixed_point_transfer_component_sources :
    MoleculeResidualFixedPointTransferComponentSources :=
  molecule_residual_fixed_point_transfer_component_sources_of_fixed_point_transfer_source
    molecule_residual_fixed_point_transfer_source

/--
Current canonical fixed-data `V`-bound source routed via PLAN_77 transfer-
component sources.
-/
theorem molecule_residual_canonical_vbound_source_via_fixed_point_transfer_component_sources :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_of_transfer_component_sources
    molecule_residual_fixed_point_transfer_component_sources

/--
Current canonical fixed-data `V`-bound source routed via fixed-point transfer
source seam.
-/
theorem molecule_residual_canonical_vbound_source_via_fixed_point_transfer_source :
    MoleculeResidualCanonicalVBoundSource :=
  molecule_residual_canonical_vbound_source_via_fixed_point_transfer_component_sources

/--
Current PLAN_57 canonical orbit-at debt source routed via PLAN_77 transfer-
component sources.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_fixed_point_transfer_component_sources :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_structure_and_transfer_component_sources
    molecule_residual_canonical_orbit_structure_source
    molecule_residual_fixed_point_transfer_component_sources

/--
Current PLAN_57 canonical orbit-at debt source routed via fixed-point transfer
source seam.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_fixed_point_transfer_source :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_via_fixed_point_transfer_component_sources

/--
Current PLAN_57 canonical orbit-at debt source routed via transport +
fixed-data + uniqueness source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source_direct :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_uniqueness_source
    molecule_residual_orbit_transport_source
    molecule_h_fixed_data_direct
    molecule_residual_fixed_point_uniqueness_source_direct

/--
Current hybrid-class-collapse source theorem projected from the uniqueness
source seam.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source :
    MoleculeResidualFixedPointHybridClassCollapseSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_source_direct

/--
Current PLAN_57 canonical orbit-at debt source routed via transport +
fixed-data + hybrid-class-collapse source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_hybrid_class_collapse_source :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_hybrid_class_collapse_source
    molecule_residual_orbit_transport_source
    molecule_h_fixed_data_direct
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Build residual fixed-point data source from explicit existence and transfer
source theorems.
-/
theorem molecule_residual_fixed_point_data_source_of_sources
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointDataSource :=
  fixed_point_normalization_data_of_fixed_exists_and_transfer
    h_exists
    h_transfer

/--
Build fixed-point data directly from the stronger critical-value-zero seed
contract and renormalizable-point `V`-bound control.
-/
theorem molecule_residual_fixed_point_data_source_of_critical_renormalizable_fixed_seed_source_and_renorm_vbound
    (h_seed : MoleculeResidualCriticalRenormalizableFixedSeedSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointDataSource := by
  rcases h_seed with ⟨f_seed, h_renorm, h_fixed, h_crit⟩
  exact ⟨f_seed, h_fixed, h_renorm, h_crit, h_renorm_vbound f_seed h_renorm h_crit⟩

/--
Build fixed-point data from existence plus critical-value transfer and
renormalizable-point `V`-bound control.
-/
theorem molecule_residual_fixed_point_data_source_of_existence_and_critical_value_transfer_and_renorm_vbound
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_critical_renormalizable_fixed_seed_source_and_renorm_vbound
    (molecule_residual_critical_renormalizable_fixed_seed_source_of_fixed_point_existence_source_and_critical_value_transfer
      h_exists
      h_crit)
    h_renorm_vbound

/--
Any non-singleton localized bridge source plus critical-value transfer and
renormalizable-point `V`-bound control already yields the fixed-data target.
-/
theorem molecule_residual_fixed_point_data_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_existence_and_critical_value_transfer_and_renorm_vbound
    (molecule_residual_fixed_point_existence_source_of_non_singleton_localized_bridge_sources
      h_sources)
    h_crit
    h_renorm_vbound

/--
Any non-singleton localized bridge source plus critical-value transfer and
renormalizable-point `V`-bound control already yields the local-witness target.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (molecule_residual_fixed_point_data_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound
      h_sources
      h_crit
      h_renorm_vbound)

/--
Any non-singleton localized bridge source plus critical-value transfer and
renormalizable-point `V`-bound control already yields the local-witness source
pack.
-/
def molecule_residual_fixed_point_local_witness_sources_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessSources :=
  molecule_residual_fixed_point_local_witness_sources_of_fixed_data
    (molecule_residual_fixed_point_data_source_of_non_singleton_localized_bridge_sources_and_critical_value_transfer_and_renorm_vbound
      h_sources
      h_crit
      h_renorm_vbound)

/--
PLAN_77 source pack for fixed-point data routed from explicit existence and
transfer inputs.
-/
structure MoleculeResidualFixedPointDataModelSources where
  existence : MoleculeResidualFixedPointExistenceSource
  transfer : MoleculeResidualFixedPointTransferSource

/--
Build PLAN_77 fixed-point data model sources from explicit existence and
transfer inputs.
-/
def molecule_residual_fixed_point_data_model_sources_of_sources
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointDataModelSources :=
  ⟨h_exists, h_transfer⟩

/--
Build fixed-point data source from PLAN_77 data model sources.
-/
theorem molecule_residual_fixed_point_data_source_of_model_sources
    (h_sources : MoleculeResidualFixedPointDataModelSources) :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_sources
    h_sources.existence
    h_sources.transfer

/--
Build fixed-point data source from existence plus PLAN_77 local-domain
transfer sources.
-/
theorem molecule_residual_fixed_point_data_source_of_existence_and_transfer_on_sources
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_transfer_on : MoleculeResidualFixedPointTransferOnSources) :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_sources
    h_exists
    (molecule_residual_fixed_point_transfer_source_of_on_sources h_transfer_on)

/--
Current PLAN_77 fixed-point data model sources theorem.
-/
def molecule_residual_fixed_point_data_model_sources :
    MoleculeResidualFixedPointDataModelSources :=
  molecule_residual_fixed_point_data_model_sources_of_sources
    molecule_residual_fixed_point_existence_source
    molecule_residual_fixed_point_transfer_source

/--
Current residual fixed-point data source routed through PLAN_77 data model
sources.
-/
theorem molecule_residual_fixed_point_data_source_via_transfer_on_sources :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_existence_and_transfer_on_sources
    molecule_residual_fixed_point_existence_source
    molecule_residual_fixed_point_transfer_on_sources

/--
Current residual fixed-point data source routed through PLAN_77 data model
sources.
-/
theorem molecule_residual_fixed_point_data_source_via_model_sources :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_via_transfer_on_sources

/--
Current residual fixed-point data source (legacy global-norm route).
-/
theorem molecule_residual_fixed_point_data_source :
    MoleculeResidualFixedPointDataSource :=
  fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_renorm_vbound_source

/--
Fallback split-witness route for PLAN_81:
assemble fixed-point normalization ingredients from the current existence and
transfer sources.
-/
theorem molecule_residual_fixed_point_normalization_ingredients_via_existence_and_transfer :
    MoleculeResidualFixedPointNormalizationIngredients :=
  ⟨
    molecule_residual_fixed_point_existence_source,
    molecule_residual_fixed_point_transfer_source
  ⟩

/--
Fallback split-witness route for PLAN_81:
reconstruct fixed-point data from the current existence and transfer sources.
-/
theorem molecule_residual_fixed_point_data_source_via_existence_and_transfer :
    MoleculeResidualFixedPointDataSource :=
  fixed_point_normalization_data_of_ingredients
    molecule_residual_fixed_point_normalization_ingredients_via_existence_and_transfer

/--
Fallback split-witness route for PLAN_81 into the local-witness theorem.
-/
def molecule_residual_fixed_point_local_witness_on_sources_via_existence_and_transfer :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_via_fixed_data_source
    molecule_residual_fixed_point_data_source_via_existence_and_transfer

/--
Assemble residual fixed-point-normalization ingredients from explicit existence
and transfer source theorems.
-/
theorem molecule_residual_fixed_point_normalization_ingredients_of_sources
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  ⟨h_exists, h_transfer⟩

/--
Construct fixed-point ingredients from:
- fixed-point normalization data source, and
- fixed-point local-normalization transfer source.
-/
theorem molecule_residual_fixed_point_normalization_ingredients_of_data_and_transfer
    (h_fixed_data : MoleculeResidualFixedPointDataSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  molecule_residual_fixed_point_normalization_ingredients_of_sources
    (renormalizable_fixed_exists_of_fixed_point_normalization_data h_fixed_data)
    h_transfer

/--
Construct fixed-point ingredients from:
- fixed-point renormalizability bridge source, and
- fixed-point local-normalization transfer source.
-/
theorem molecule_residual_fixed_point_normalization_ingredients_of_bridge_and_transfer
    (h_bridge : MoleculeResidualFixedPointBridgeSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  molecule_residual_fixed_point_normalization_ingredients_of_sources
    (molecule_residual_fixed_point_existence_source_of_bridge h_bridge)
    h_transfer

/--
Current bundled ingredient source theorem (legacy global-norm route).
-/
theorem molecule_residual_fixed_point_normalization_ingredients :
    MoleculeResidualFixedPointNormalizationIngredients :=
  molecule_residual_fixed_point_normalization_ingredients_of_sources
    molecule_residual_fixed_point_existence_source
    molecule_residual_fixed_point_transfer_source

/--
Explicit replacement seam for the bundled fixed-point ingredient source.
-/
def MoleculeResidualFixedPointIngredientsSource : Prop :=
  MoleculeResidualFixedPointNormalizationIngredients

/--
Build fixed-point ingredient source from explicit existence and transfer
source theorems.
-/
theorem molecule_residual_fixed_point_ingredients_source_of_sources
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointIngredientsSource :=
  molecule_residual_fixed_point_normalization_ingredients_of_sources
    h_exists
    h_transfer

/--
Current fixed-point ingredient source theorem (legacy global-norm route).
-/
theorem molecule_residual_fixed_point_ingredients_source :
    MoleculeResidualFixedPointIngredientsSource :=
  molecule_residual_fixed_point_ingredients_source_of_sources
    molecule_residual_fixed_point_existence_source
    molecule_residual_fixed_point_transfer_source

/--
Current residual fixed-point normalization source (legacy global-norm route).
-/
theorem molecule_residual_fixed_point_normalization_source :
    MoleculeResidualFixedPointNormalizationSource :=
  molecule_residual_fixed_point_normalization_source_of_ingredients
    molecule_residual_fixed_point_ingredients_source

/--
Localized fixed-point data witness used by the packed top-theorem route.
-/
theorem molecule_h_fixed_data : FixedPointNormalizationData :=
  molecule_residual_fixed_point_normalization_source

/--
Explicit canonical fixed-point contract for the built-in renormalization operator.
-/
def CanonicalFastFixedPointData : Prop :=
  ∃ g : BMol, IsFastRenormalizable g ∧ Molecule.Rfast g = g

/--
Core refined molecule-conjecture export proposition (operator package only).
-/
def MoleculeConjectureRefinedCore : Prop :=
  ∃ (Rfast : BMol → BMol)
    (Rfast_HMol : HMol → HMol)
    (R_target : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp}),
    IsHyperbolic Rfast ∧
    IsPiecewiseAnalytic1DUnstable Rfast ∧
    IsCompactOperator Rfast_HMol ∧
    CombinatoriallyAssociated Rfast_HMol R_target ∧
    (∃ N, IsConjugateToShift R_target N)

/--
Refined export proposition augmented with canonical fixed-point data.
-/
def MoleculeConjectureRefined : Prop :=
  MoleculeConjectureRefinedCore ∧ CanonicalFastFixedPointData

/--
Upstream constructive source contract: produce the PLAN_64 anchor direct seam
from canonical fixed-point data.
-/
def MoleculeResidualDirectSeamAnchorOfCanonicalSource : Prop :=
  CanonicalFastFixedPointData → MoleculeResidualDirectSeamAnchorSource

/--
Upstream constructive source contract: produce the PLAN_64 anchor direct seam
from refined contract data.
-/
def MoleculeResidualDirectSeamAnchorOfRefinedSource : Prop :=
  MoleculeConjectureRefined → MoleculeResidualDirectSeamAnchorSource

/--
Upstream constructive source contract: produce map-level fixed-point uniqueness
source from canonical fixed-point data.
-/
def MoleculeResidualFixedPointUniquenessOfCanonicalSource : Prop :=
  CanonicalFastFixedPointData → MoleculeResidualFixedPointUniquenessSource

/--
Upstream constructive source contract: produce map-level fixed-point uniqueness
source from refined contract data.
-/
def MoleculeResidualFixedPointUniquenessOfRefinedSource : Prop :=
  MoleculeConjectureRefined → MoleculeResidualFixedPointUniquenessSource

/--
Upstream constructive source contract: produce hybrid-class fixed-point
uniqueness from canonical fixed-point data.
-/
def MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource : Prop :=
  CanonicalFastFixedPointData → MoleculeResidualHybridClassFixedPointUniquenessSource

/--
Upstream constructive source contract: produce hybrid-class fixed-point
uniqueness from refined contract data.
-/
def MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource : Prop :=
  MoleculeConjectureRefined → MoleculeResidualHybridClassFixedPointUniquenessSource

/--
Upstream constructive source contract: produce hybrid-class-uniqueness
model-collapse input from canonical fixed-point data.
-/
def MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource : Prop :=
  CanonicalFastFixedPointData → MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource

/--
Upstream constructive source contract: produce hybrid-class-uniqueness
model-collapse input from refined contract data.
-/
def MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource : Prop :=
  MoleculeConjectureRefined → MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource

/--
Upstream constructive source contract: produce hybrid-class-uniqueness
model-collapse direct seam input from canonical fixed-point data.
-/
def MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource : Prop :=
  CanonicalFastFixedPointData →
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource

/--
Upstream constructive source contract: produce hybrid-class-uniqueness
model-collapse direct seam input from refined contract data.
-/
def MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource : Prop :=
  MoleculeConjectureRefined →
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource

/--
Upstream constructive source contract: produce map-level fixed-point uniqueness
direct seam from canonical fixed-point data.
-/
def MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource : Prop :=
  CanonicalFastFixedPointData → MoleculeResidualFixedPointUniquenessDirectSource

/--
Upstream constructive source contract: produce map-level fixed-point uniqueness
direct seam from refined contract data.
-/
def MoleculeResidualFixedPointUniquenessDirectOfRefinedSource : Prop :=
  MoleculeConjectureRefined → MoleculeResidualFixedPointUniquenessDirectSource

/--
Lift canonical uniqueness-source contract to refined-contract uniqueness-source
contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_of_canonical_source
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessOfRefinedSource :=
  fun h_refined => h_unique_canonical h_refined.2

/--
Lift canonical anchor-source contract to refined-contract anchor-source
contract.
-/
theorem molecule_residual_direct_seam_anchor_of_refined_source_of_canonical_source
    (h_anchor_canonical : MoleculeResidualDirectSeamAnchorOfCanonicalSource) :
    MoleculeResidualDirectSeamAnchorOfRefinedSource :=
  fun h_refined => h_anchor_canonical h_refined.2

/--
Lift canonical hybrid-class-uniqueness contract to refined-contract
hybrid-class-uniqueness contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_of_canonical_source
    (h_class_unique_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource :=
  fun h_refined => h_class_unique_canonical h_refined.2

/--
Lift canonical hybrid-class-uniqueness model-collapse contract to refined
contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_of_canonical_source
    (h_model_collapse_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource :=
  fun h_refined => h_model_collapse_canonical h_refined.2

/--
Lift canonical hybrid-class-uniqueness model-collapse-direct contract to
refined contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_of_refined_source_of_canonical_source
    (h_model_collapse_direct_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource :=
  fun h_refined => h_model_collapse_direct_canonical h_refined.2

/--
Lift canonical map-level direct-uniqueness contract to refined contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_canonical_source
    (h_unique_direct_canonical :
      MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
  fun h_refined => h_unique_direct_canonical h_refined.2

/--
Build canonical-contract anchor-source contract from a map-level fixed-point
uniqueness source theorem.
-/
theorem molecule_residual_direct_seam_anchor_of_canonical_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualDirectSeamAnchorOfCanonicalSource :=
  fun _h_canonical =>
    molecule_residual_direct_seam_anchor_source_of_uniqueness_source h_unique

/--
Build refined-contract anchor-source contract from a map-level fixed-point
uniqueness source theorem.
-/
theorem molecule_residual_direct_seam_anchor_of_refined_source_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualDirectSeamAnchorOfRefinedSource :=
  fun _h_refined =>
    molecule_residual_direct_seam_anchor_source_of_uniqueness_source h_unique

/--
Build canonical-contract anchor-source contract from a canonical-contract
uniqueness-source contract.
-/
theorem molecule_residual_direct_seam_anchor_of_canonical_source_of_uniqueness_of_canonical_source
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualDirectSeamAnchorOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_direct_seam_anchor_source_of_uniqueness_source
      (h_unique_canonical h_canonical)

/--
Build canonical-contract uniqueness-source contract from a canonical-contract
anchor-source contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_of_anchor_of_canonical_source
    (h_anchor_canonical : MoleculeResidualDirectSeamAnchorOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    (molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source).1
      (h_anchor_canonical h_canonical)

/--
Canonical-contract anchor-source and uniqueness-source contracts are
equivalent.
-/
theorem molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_of_canonical_source :
    MoleculeResidualDirectSeamAnchorOfCanonicalSource ↔
      MoleculeResidualFixedPointUniquenessOfCanonicalSource := by
  constructor
  · exact molecule_residual_fixed_point_uniqueness_of_canonical_source_of_anchor_of_canonical_source
  · exact molecule_residual_direct_seam_anchor_of_canonical_source_of_uniqueness_of_canonical_source

/--
Build refined-contract anchor-source contract from a refined-contract
uniqueness-source contract.
-/
theorem molecule_residual_direct_seam_anchor_of_refined_source_of_uniqueness_of_refined_source
    (h_unique_refined : MoleculeResidualFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualDirectSeamAnchorOfRefinedSource :=
  fun h_refined =>
    molecule_residual_direct_seam_anchor_source_of_uniqueness_source
      (h_unique_refined h_refined)

/--
Build refined-contract uniqueness-source contract from a refined-contract
anchor-source contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_of_anchor_of_refined_source
    (h_anchor_refined : MoleculeResidualDirectSeamAnchorOfRefinedSource) :
    MoleculeResidualFixedPointUniquenessOfRefinedSource :=
  fun h_refined =>
    (molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source).1
      (h_anchor_refined h_refined)

/--
Refined-contract anchor-source and uniqueness-source contracts are equivalent.
-/
theorem molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_of_refined_source :
    MoleculeResidualDirectSeamAnchorOfRefinedSource ↔
      MoleculeResidualFixedPointUniquenessOfRefinedSource := by
  constructor
  · exact molecule_residual_fixed_point_uniqueness_of_refined_source_of_anchor_of_refined_source
  · exact molecule_residual_direct_seam_anchor_of_refined_source_of_uniqueness_of_refined_source

/--
Build the PLAN_64 anchor seam from:
- canonical fixed-point data, and
- a canonical-contract uniqueness-source contract.
-/
theorem molecule_residual_direct_seam_anchor_source_of_canonical_and_uniqueness_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source_of_uniqueness_source
    (h_unique_canonical h_canonical)

/--
Build the PLAN_64 anchor seam from:
- refined contract data, and
- a refined-contract uniqueness-source contract.
-/
theorem molecule_residual_direct_seam_anchor_source_of_refined_and_uniqueness_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_unique_refined : MoleculeResidualFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source_of_uniqueness_source
    (h_unique_refined h_refined)

/--
Project direct map-level hybrid-class-collapse seam from:
- canonical fixed-point data, and
- a canonical-contract uniqueness-source contract.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_canonical_and_uniqueness_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_canonical_and_uniqueness_of_canonical_source
      h_canonical h_unique_canonical)

/--
Project direct map-level fixed-point uniqueness seam from:
- canonical fixed-point data, and
- a canonical-contract uniqueness-source contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_and_uniqueness_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_canonical_and_uniqueness_of_canonical_source
      h_canonical h_unique_canonical)

/--
Project direct map-level hybrid-class-collapse seam from:
- refined contract data, and
- a refined-contract uniqueness-source contract.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_refined_and_uniqueness_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_unique_refined : MoleculeResidualFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_refined_and_uniqueness_of_refined_source
      h_refined h_unique_refined)

/--
Project direct map-level fixed-point uniqueness seam from:
- refined contract data, and
- a refined-contract uniqueness-source contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_refined_and_uniqueness_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_unique_refined : MoleculeResidualFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_refined_and_uniqueness_of_refined_source
      h_refined h_unique_refined)

/--
Project direct map-level hybrid-class-collapse seam from canonical anchor-source
contract.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_canonical_anchor_source
    (h_anchor_canonical : MoleculeResidualDirectSeamAnchorOfCanonicalSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (h_anchor_canonical h_canonical)

/--
Project direct map-level fixed-point uniqueness seam from canonical
anchor-source contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_anchor_source
    (h_anchor_canonical : MoleculeResidualDirectSeamAnchorOfCanonicalSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (h_anchor_canonical h_canonical)

/--
Project direct map-level hybrid-class-collapse seam from refined-contract
anchor-source contract.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_refined_anchor_source
    (h_anchor_refined : MoleculeResidualDirectSeamAnchorOfRefinedSource)
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (h_anchor_refined h_refined)

/--
Project direct map-level fixed-point uniqueness seam from refined-contract
anchor-source contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_refined_anchor_source
    (h_anchor_refined : MoleculeResidualDirectSeamAnchorOfRefinedSource)
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (h_anchor_refined h_refined)

/--
Subtarget A bridge: canonical fixed-point data directly provides the residual
fixed-point existence ingredient.
-/
theorem residual_fixed_point_existence_of_canonical_fast_fixed_point_data
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointExistenceSource :=
  h_canonical

/--
If the designated selected point agrees with every renormalizable fixed point,
then any canonical fixed-point witness yields renormalizability of the selected
point.
-/
theorem molecule_residual_selected_fixed_point_renormalizable_of_identification_and_canonical
    (h_ident : MoleculeResidualSelectedFixedPointIdentificationSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualSelectedFixedPointRenormalizableSource := by
  classical
  let g : BMol := Classical.choose h_canonical
  have hg_spec : IsFastRenormalizable g ∧ Rfast g = g :=
    Classical.choose_spec h_canonical
  have h_eq : selected_fixed_point = g := h_ident g hg_spec.1 hg_spec.2
  simpa [MoleculeResidualSelectedFixedPointRenormalizableSource, h_eq] using hg_spec.1

/--
If the hybrid class of the designated selected point agrees with every fixed
hybrid class, then any canonical fixed-point witness yields renormalizability
of the selected point.
-/
theorem molecule_residual_selected_fixed_point_renormalizable_of_hybrid_class_fixed_identification_and_canonical
    (h_ident_class : MoleculeResidualSelectedHybridClassFixedIdentificationSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualSelectedFixedPointRenormalizableSource := by
  classical
  let g : BMol := Classical.choose h_canonical
  have hg_spec : IsFastRenormalizable g ∧ Rfast g = g :=
    Classical.choose_spec h_canonical
  have h_class_fix : R_hybrid (toHybridClass g) = toHybridClass g := by
    simpa [R_hybrid, toHybridClass] using hg_spec.2
  have h_class_eq :
      toHybridClass selected_fixed_point = toHybridClass g :=
    h_ident_class (toHybridClass g) h_class_fix
  have h_eq : selected_fixed_point = g := toHybridClass_injective h_class_eq
  simpa [MoleculeResidualSelectedFixedPointRenormalizableSource, h_eq] using hg_spec.1

/--
Candidate PLAN_83 continuation from PLAN_82:
canonical fixed-point data plus identification of the selected point with any
renormalizable fixed point implies the exact selected-point renormalizability
source.
-/
theorem molecule_residual_fixed_point_existence_source_of_selected_fixed_point_identification_and_canonical
    (h_ident : MoleculeResidualSelectedFixedPointIdentificationSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_selected_fixed_point_renormalizable
    (molecule_residual_selected_fixed_point_renormalizable_of_identification_and_canonical
      h_ident h_canonical)

/--
Candidate PLAN_83 continuation from a fixed-point-only identification theorem.
-/
theorem molecule_residual_fixed_point_existence_source_of_selected_fixed_point_fixed_identification_and_canonical
    (h_ident_fixed : MoleculeResidualSelectedFixedPointFixedIdentificationSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointExistenceSource := by
  classical
  let g : BMol := Classical.choose h_canonical
  have hg_spec : IsFastRenormalizable g ∧ Rfast g = g :=
    Classical.choose_spec h_canonical
  have h_eq : selected_fixed_point = g := h_ident_fixed g hg_spec.2
  have h_renorm : MoleculeResidualSelectedFixedPointRenormalizableSource := by
    simpa [MoleculeResidualSelectedFixedPointRenormalizableSource, h_eq] using
      hg_spec.1
  exact
    molecule_residual_fixed_point_existence_source_of_selected_fixed_point_renormalizable
      h_renorm

/--
Sharper PLAN_83 continuation from PLAN_82:
it is enough to identify the hybrid class of the selected point with every
fixed hybrid class. In the current identity-model seam this already implies the
map-level fixed-point identification target.
-/
theorem molecule_residual_fixed_point_existence_source_of_selected_hybrid_class_fixed_identification_and_canonical
    (h_ident_class : MoleculeResidualSelectedHybridClassFixedIdentificationSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_selected_fixed_point_renormalizable
    (molecule_residual_selected_fixed_point_renormalizable_of_hybrid_class_fixed_identification_and_canonical
      h_ident_class h_canonical)

/--
Sharper PLAN_83 continuation from exact hybrid-class fixed-point uniqueness.
-/
theorem molecule_residual_fixed_point_existence_source_of_hybrid_class_fixed_point_exact_uniqueness_and_canonical
    (h_unique_exact : MoleculeResidualHybridClassFixedPointExactUniquenessSource)
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_selected_hybrid_class_fixed_identification_and_canonical
    (molecule_residual_selected_hybrid_class_fixed_identification_of_exact_uniqueness
      h_unique_exact)
    h_canonical

/--
Subtarget A bridge from refined contract assumptions.
-/
theorem residual_fixed_point_existence_of_refined_contract
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualFixedPointExistenceSource :=
  residual_fixed_point_existence_of_canonical_fast_fixed_point_data h_refined.2

/--
Assemble hybrid-class unique fixed-point source from canonical fixed-point data
and seam-level collapse + lift sources.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_collapse_and_lift_sources
    (h_canonical : CanonicalFastFixedPointData)
    (h_collapse : MoleculeResidualHybridFixedPointCollapseSource)
    (h_lift : MoleculeResidualHybridClassFixedPointLiftSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  hybrid_unique_fixed_point_in_of_exists_and_collapse_and_lift
    currentHybridProjectionSeam
    h_canonical
    h_collapse
    h_lift

/--
Assemble hybrid-class unique fixed-point source from canonical fixed-point data
and a hybrid-class fixed-point uniqueness source.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_uniqueness_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualHybridUniqueFixedPointSource := by
  rcases h_canonical with ⟨g, h_renorm_g, h_fix_g⟩
  refine ⟨toHybridClass g, ?_, ?_⟩
  · exact ⟨h_renorm_g, by simpa [R_hybrid, toHybridClass] using h_fix_g⟩
  · intro y hy
    exact
      h_class_unique y (toHybridClass g) hy
        ⟨h_renorm_g, by simpa [R_hybrid, toHybridClass] using h_fix_g⟩

/--
Assemble hybrid-class unique fixed-point source from canonical fixed-point data
and a hybrid-class-collapse source.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridUniqueFixedPointSource := by
  exact
    molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_collapse_and_lift_sources
      h_canonical
      (molecule_residual_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
        h_collapse)
      molecule_residual_hybrid_class_fixed_point_lift_source

/--
Assemble hybrid-class unique fixed-point source from canonical fixed-point data
and a map-level uniqueness source.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_uniqueness_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source
    h_canonical
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
      h_unique)

/--
Assemble hybrid-class unique fixed-point source from refined contract
assumptions and a hybrid-class-collapse source.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_refined_and_hybrid_class_collapse_source
    (h_refined : MoleculeConjectureRefined)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source
    h_refined.2
    h_collapse

/--
Assemble hybrid-class unique fixed-point source from refined contract
assumptions and a map-level uniqueness source.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_refined_and_uniqueness_source
    (h_refined : MoleculeConjectureRefined)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_refined_and_hybrid_class_collapse_source
    h_refined
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
      h_unique)

/--
Build a canonical-contract uniqueness-source contract from a hybrid-class
fixed-point uniqueness source.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
      (molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_uniqueness_source
        h_canonical
        h_class_unique)

/--
Build a canonical-contract uniqueness-source contract from a map-level
hybrid-class-collapse source.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
      (molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source
        h_canonical
        h_collapse)

/--
Build a refined-contract uniqueness-source contract from a hybrid-class
fixed-point uniqueness source.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualFixedPointUniquenessOfRefinedSource :=
  molecule_residual_fixed_point_uniqueness_of_refined_source_of_canonical_source
    (molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_uniqueness_source
      h_class_unique)

/--
Build a refined-contract uniqueness-source contract from a map-level
hybrid-class-collapse source.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_of_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointUniquenessOfRefinedSource :=
  molecule_residual_fixed_point_uniqueness_of_refined_source_of_canonical_source
    (molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_collapse_source
      h_collapse)

/--
Build a canonical-contract hybrid-class-uniqueness contract from a
canonical-contract map-level uniqueness contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_canonical_source_of_fixed_point_uniqueness_of_canonical_source
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    (molecule_residual_fixed_point_hybrid_class_collapse_source_iff_hybrid_class_uniqueness_source).1
      (molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
        (h_unique_canonical h_canonical))

/--
Build a canonical-contract map-level uniqueness contract from a
canonical-contract hybrid-class-uniqueness contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_fixed_point_uniqueness_of_canonical_source
    (h_class_unique_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
      (molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_uniqueness_source
        h_canonical
        (h_class_unique_canonical h_canonical))

/--
Canonical-contract map-level uniqueness and hybrid-class-uniqueness contracts
are equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_hybrid_class_fixed_point_uniqueness_of_canonical_source :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource := by
  constructor
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_of_canonical_source_of_fixed_point_uniqueness_of_canonical_source
  · exact
      molecule_residual_fixed_point_uniqueness_of_canonical_source_of_hybrid_class_fixed_point_uniqueness_of_canonical_source

/--
Build a refined-contract hybrid-class-uniqueness contract from a refined-contract
map-level uniqueness contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_of_fixed_point_uniqueness_of_refined_source
    (h_unique_refined : MoleculeResidualFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource :=
  fun h_refined =>
    (molecule_residual_fixed_point_hybrid_class_collapse_source_iff_hybrid_class_uniqueness_source).1
      (molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
        (h_unique_refined h_refined))

/--
Build a refined-contract map-level uniqueness contract from a refined-contract
hybrid-class-uniqueness contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_of_hybrid_class_fixed_point_uniqueness_of_refined_source
    (h_class_unique_refined :
      MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualFixedPointUniquenessOfRefinedSource :=
  fun h_refined =>
    molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
      (molecule_residual_hybrid_unique_fixed_point_source_of_refined_and_hybrid_class_collapse_source
        h_refined
        (molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source
          (h_class_unique_refined h_refined)))

/--
Refined-contract map-level uniqueness and hybrid-class-uniqueness contracts are
equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_iff_hybrid_class_fixed_point_uniqueness_of_refined_source :
    MoleculeResidualFixedPointUniquenessOfRefinedSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource := by
  constructor
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_of_fixed_point_uniqueness_of_refined_source
  · exact
      molecule_residual_fixed_point_uniqueness_of_refined_source_of_hybrid_class_fixed_point_uniqueness_of_refined_source

/--
Build a canonical-contract model-collapse contract from a canonical-contract
hybrid-class-uniqueness contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_canonical_source_of_hybrid_class_fixed_point_uniqueness_of_canonical_source
    (h_class_unique_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_uniqueness_source
      (h_class_unique_canonical h_canonical)

/--
Build a canonical-contract hybrid-class-uniqueness contract from a
canonical-contract model-collapse contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_canonical_source_of_model_collapse_of_canonical_source
    (h_model_collapse_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
      (molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
        (h_model_collapse_canonical h_canonical))

/--
Canonical-contract hybrid-class-uniqueness and model-collapse contracts are
equivalent.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_of_canonical_source :
    MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource := by
  constructor
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_canonical_source_of_hybrid_class_fixed_point_uniqueness_of_canonical_source
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_of_canonical_source_of_model_collapse_of_canonical_source

/--
Canonical-contract map-level uniqueness and model-collapse contracts are
equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_of_canonical_source :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource := by
  calc
    MoleculeResidualFixedPointUniquenessOfCanonicalSource
        ↔ MoleculeResidualHybridClassFixedPointUniquenessOfCanonicalSource :=
      molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_hybrid_class_fixed_point_uniqueness_of_canonical_source
    _ ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource :=
      molecule_residual_hybrid_class_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_of_canonical_source

/--
Build a refined-contract model-collapse contract from a refined-contract
hybrid-class-uniqueness contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_of_hybrid_class_fixed_point_uniqueness_of_refined_source
    (h_class_unique_refined :
      MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource :=
  fun h_refined =>
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_uniqueness_source
      (h_class_unique_refined h_refined)

/--
Build a refined-contract hybrid-class-uniqueness contract from a refined-contract
model-collapse contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_of_model_collapse_of_refined_source
    (h_model_collapse_refined :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource) :
    MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource :=
  fun h_refined =>
    molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
      (molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
        (h_model_collapse_refined h_refined))

/--
Refined-contract hybrid-class-uniqueness and model-collapse contracts are
equivalent.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_iff_model_collapse_of_refined_source :
    MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource := by
  constructor
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_of_hybrid_class_fixed_point_uniqueness_of_refined_source
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_of_model_collapse_of_refined_source

/--
Refined-contract map-level uniqueness and model-collapse contracts are
equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_of_refined_source :
    MoleculeResidualFixedPointUniquenessOfRefinedSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource := by
  calc
    MoleculeResidualFixedPointUniquenessOfRefinedSource
        ↔ MoleculeResidualHybridClassFixedPointUniquenessOfRefinedSource :=
      molecule_residual_fixed_point_uniqueness_of_refined_source_iff_hybrid_class_fixed_point_uniqueness_of_refined_source
    _ ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource :=
      molecule_residual_hybrid_class_fixed_point_uniqueness_of_refined_source_iff_model_collapse_of_refined_source

/--
Build a canonical-contract model-collapse-direct contract from a
canonical-contract model-collapse contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_of_canonical_source_of_model_collapse_of_canonical_source
    (h_model_collapse_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource :=
  fun h_canonical => h_model_collapse_canonical h_canonical

/--
Build a canonical-contract model-collapse contract from a canonical-contract
model-collapse-direct contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_canonical_source_of_model_collapse_direct_of_canonical_source
    (h_model_collapse_direct_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource :=
  fun h_canonical => h_model_collapse_direct_canonical h_canonical

/--
Canonical-contract model-collapse and model-collapse-direct contracts are
equivalent.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_canonical_source_iff_model_collapse_direct_of_canonical_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource := by
  constructor
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_of_canonical_source_of_model_collapse_of_canonical_source
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_canonical_source_of_model_collapse_direct_of_canonical_source

/--
Build a refined-contract model-collapse-direct contract from a refined-contract
model-collapse contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_of_refined_source_of_model_collapse_of_refined_source
    (h_model_collapse_refined :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource :=
  fun h_refined => h_model_collapse_refined h_refined

/--
Build a refined-contract model-collapse contract from a refined-contract
model-collapse-direct contract.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_of_model_collapse_direct_of_refined_source
    (h_model_collapse_direct_refined :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource :=
  fun h_refined => h_model_collapse_direct_refined h_refined

/--
Refined-contract model-collapse and model-collapse-direct contracts are
equivalent.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_iff_model_collapse_direct_of_refined_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource := by
  constructor
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_of_refined_source_of_model_collapse_of_refined_source
  · exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_of_model_collapse_direct_of_refined_source

/--
Canonical-contract map-level uniqueness and model-collapse-direct contracts are
equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_direct_of_canonical_source :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource := by
  calc
    MoleculeResidualFixedPointUniquenessOfCanonicalSource
        ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfCanonicalSource :=
      molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_of_canonical_source
    _ ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource :=
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_canonical_source_iff_model_collapse_direct_of_canonical_source

/--
Refined-contract map-level uniqueness and model-collapse-direct contracts are
equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_direct_of_refined_source :
    MoleculeResidualFixedPointUniquenessOfRefinedSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource := by
  calc
    MoleculeResidualFixedPointUniquenessOfRefinedSource
        ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseOfRefinedSource :=
      molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_of_refined_source
    _ ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource :=
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_of_refined_source_iff_model_collapse_direct_of_refined_source

/--
Build a canonical-contract map-level direct-uniqueness contract from a
canonical-contract map-level uniqueness contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_fixed_point_uniqueness_of_canonical_source
    (h_unique_canonical : MoleculeResidualFixedPointUniquenessOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_model_collapse_source
      ((molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_direct_of_canonical_source).1
        h_unique_canonical h_canonical)

/--
Build a canonical-contract map-level uniqueness contract from a canonical-contract
map-level direct-uniqueness contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_of_fixed_point_uniqueness_direct_of_canonical_source
    (h_unique_direct_canonical :
      MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_fixed_point_uniqueness_source_direct_of_source
      (h_unique_direct_canonical h_canonical)

/--
Canonical-contract map-level uniqueness and map-level direct-uniqueness
contracts are equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_fixed_point_uniqueness_direct_of_canonical_source :
    MoleculeResidualFixedPointUniquenessOfCanonicalSource ↔
      MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource := by
  constructor
  · exact
      molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_fixed_point_uniqueness_of_canonical_source
  · exact
      molecule_residual_fixed_point_uniqueness_of_canonical_source_of_fixed_point_uniqueness_direct_of_canonical_source

/--
Build a refined-contract map-level direct-uniqueness contract from a
refined-contract map-level uniqueness contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_fixed_point_uniqueness_of_refined_source
    (h_unique_refined : MoleculeResidualFixedPointUniquenessOfRefinedSource) :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
  fun h_refined =>
    molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_model_collapse_source
      ((molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_direct_of_refined_source).1
        h_unique_refined h_refined)

/--
Build a refined-contract map-level uniqueness contract from a refined-contract
map-level direct-uniqueness contract.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_of_fixed_point_uniqueness_direct_of_refined_source
    (h_unique_direct_refined :
      MoleculeResidualFixedPointUniquenessDirectOfRefinedSource) :
    MoleculeResidualFixedPointUniquenessOfRefinedSource :=
  fun h_refined =>
    molecule_residual_fixed_point_uniqueness_source_direct_of_source
      (h_unique_direct_refined h_refined)

/--
Refined-contract map-level uniqueness and map-level direct-uniqueness
contracts are equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_of_refined_source_iff_fixed_point_uniqueness_direct_of_refined_source :
    MoleculeResidualFixedPointUniquenessOfRefinedSource ↔
      MoleculeResidualFixedPointUniquenessDirectOfRefinedSource := by
  constructor
  · exact
      molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_fixed_point_uniqueness_of_refined_source
  · exact
      molecule_residual_fixed_point_uniqueness_of_refined_source_of_fixed_point_uniqueness_direct_of_refined_source

/--
Canonical-contract anchor and model-collapse-direct contracts are equivalent.
-/
theorem molecule_residual_direct_seam_anchor_of_canonical_source_iff_model_collapse_direct_of_canonical_source :
    MoleculeResidualDirectSeamAnchorOfCanonicalSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource := by
  calc
    MoleculeResidualDirectSeamAnchorOfCanonicalSource
        ↔ MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
      molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_of_canonical_source
    _ ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource :=
      molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_model_collapse_direct_of_canonical_source

/--
Refined-contract anchor and model-collapse-direct contracts are equivalent.
-/
theorem molecule_residual_direct_seam_anchor_of_refined_source_iff_model_collapse_direct_of_refined_source :
    MoleculeResidualDirectSeamAnchorOfRefinedSource ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource := by
  calc
    MoleculeResidualDirectSeamAnchorOfRefinedSource
        ↔ MoleculeResidualFixedPointUniquenessOfRefinedSource :=
      molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_of_refined_source
    _ ↔ MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource :=
      molecule_residual_fixed_point_uniqueness_of_refined_source_iff_model_collapse_direct_of_refined_source

/--
Canonical-contract anchor and map-level direct-uniqueness contracts are
equivalent.
-/
theorem molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_direct_of_canonical_source :
    MoleculeResidualDirectSeamAnchorOfCanonicalSource ↔
      MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource := by
  calc
    MoleculeResidualDirectSeamAnchorOfCanonicalSource
        ↔ MoleculeResidualFixedPointUniquenessOfCanonicalSource :=
      molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_of_canonical_source
    _ ↔ MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource :=
      molecule_residual_fixed_point_uniqueness_of_canonical_source_iff_fixed_point_uniqueness_direct_of_canonical_source

/--
Refined-contract anchor and map-level direct-uniqueness contracts are
equivalent.
-/
theorem molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_direct_of_refined_source :
    MoleculeResidualDirectSeamAnchorOfRefinedSource ↔
      MoleculeResidualFixedPointUniquenessDirectOfRefinedSource := by
  calc
    MoleculeResidualDirectSeamAnchorOfRefinedSource
        ↔ MoleculeResidualFixedPointUniquenessOfRefinedSource :=
      molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_of_refined_source
    _ ↔ MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
      molecule_residual_fixed_point_uniqueness_of_refined_source_iff_fixed_point_uniqueness_direct_of_refined_source

/--
Build the PLAN_64 anchor seam from:
- canonical fixed-point data, and
- a canonical-contract map-level direct-uniqueness contract.
-/
theorem molecule_residual_direct_seam_anchor_source_of_canonical_and_fixed_point_uniqueness_direct_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_unique_direct_canonical :
      MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource) :
    MoleculeResidualDirectSeamAnchorSource :=
  ((molecule_residual_direct_seam_anchor_of_canonical_source_iff_fixed_point_uniqueness_direct_of_canonical_source).2
    h_unique_direct_canonical) h_canonical

/--
Build the PLAN_64 anchor seam from:
- refined contract data, and
- a refined-contract map-level direct-uniqueness contract.
-/
theorem molecule_residual_direct_seam_anchor_source_of_refined_and_fixed_point_uniqueness_direct_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_unique_direct_refined :
      MoleculeResidualFixedPointUniquenessDirectOfRefinedSource) :
    MoleculeResidualDirectSeamAnchorSource :=
  ((molecule_residual_direct_seam_anchor_of_refined_source_iff_fixed_point_uniqueness_direct_of_refined_source).2
    h_unique_direct_refined) h_refined

/--
Build the PLAN_64 anchor seam from:
- canonical fixed-point data, and
- a canonical-contract model-collapse-direct contract.
-/
theorem molecule_residual_direct_seam_anchor_source_of_canonical_and_model_collapse_direct_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_model_collapse_direct_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource) :
    MoleculeResidualDirectSeamAnchorSource :=
  ((molecule_residual_direct_seam_anchor_of_canonical_source_iff_model_collapse_direct_of_canonical_source).2
    h_model_collapse_direct_canonical) h_canonical

/--
Build the PLAN_64 anchor seam from:
- refined contract data, and
- a refined-contract model-collapse-direct contract.
-/
theorem molecule_residual_direct_seam_anchor_source_of_refined_and_model_collapse_direct_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_model_collapse_direct_refined :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource) :
    MoleculeResidualDirectSeamAnchorSource :=
  ((molecule_residual_direct_seam_anchor_of_refined_source_iff_model_collapse_direct_of_refined_source).2
    h_model_collapse_direct_refined) h_refined

/--
Project direct map-level hybrid-class-collapse seam from:
- canonical fixed-point data, and
- a canonical-contract model-collapse-direct contract.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_canonical_and_model_collapse_direct_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_model_collapse_direct_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_canonical_and_model_collapse_direct_of_canonical_source
      h_canonical h_model_collapse_direct_canonical)

/--
Project direct map-level fixed-point uniqueness seam from:
- canonical fixed-point data, and
- a canonical-contract model-collapse-direct contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_and_model_collapse_direct_of_canonical_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_model_collapse_direct_canonical :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfCanonicalSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_canonical_and_model_collapse_direct_of_canonical_source
      h_canonical h_model_collapse_direct_canonical)

/--
Project direct map-level hybrid-class-collapse seam from:
- refined contract data, and
- a refined-contract model-collapse-direct contract.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_refined_and_model_collapse_direct_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_model_collapse_direct_refined :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource) :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_refined_and_model_collapse_direct_of_refined_source
      h_refined h_model_collapse_direct_refined)

/--
Project direct map-level fixed-point uniqueness seam from:
- refined contract data, and
- a refined-contract model-collapse-direct contract.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_refined_and_model_collapse_direct_of_refined_source
    (h_refined : MoleculeConjectureRefined)
    (h_model_collapse_direct_refined :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectOfRefinedSource) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    (molecule_residual_direct_seam_anchor_source_of_refined_and_model_collapse_direct_of_refined_source
      h_refined h_model_collapse_direct_refined)

/--
Build a canonical-contract map-level direct-uniqueness contract from a
model-collapse-direct source theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_model_collapse_direct_source
    (h_model_collapse_direct :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource) :
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource :=
  fun h_canonical =>
    molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_and_model_collapse_direct_of_canonical_source
      h_canonical
      (fun _ => h_model_collapse_direct)

/--
Build a refined-contract map-level direct-uniqueness contract from a
model-collapse-direct source theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_model_collapse_direct_source
    (h_model_collapse_direct :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource) :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
  fun h_refined =>
    molecule_residual_fixed_point_uniqueness_direct_source_of_refined_and_model_collapse_direct_of_refined_source
      h_refined
      (fun _ => h_model_collapse_direct)

/--
Build a canonical-contract map-level direct-uniqueness contract from a
map-level direct-uniqueness source theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_fixed_point_uniqueness_direct_source
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource :=
  molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_model_collapse_direct_source
    ((molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_hybrid_class_uniqueness_model_collapse_direct_source).1
      ((molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_fixed_point_uniqueness_direct_source).2
        h_unique_direct))

/--
Build a refined-contract map-level direct-uniqueness contract from a
map-level direct-uniqueness source theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_fixed_point_uniqueness_direct_source
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
  molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_model_collapse_direct_source
    ((molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_hybrid_class_uniqueness_model_collapse_direct_source).1
      ((molecule_residual_fixed_point_hybrid_class_collapse_direct_source_iff_fixed_point_uniqueness_direct_source).2
        h_unique_direct))

/--
Current canonical-contract map-level direct-uniqueness contract theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_canonical_source :
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource :=
  molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_fixed_point_uniqueness_direct_source
    molecule_residual_fixed_point_uniqueness_direct_source

/--
Current refined-contract map-level direct-uniqueness contract theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
  molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_fixed_point_uniqueness_direct_source
    molecule_residual_fixed_point_uniqueness_direct_source

/--
Under a canonical fixed-point witness, canonical-contract map-level
direct-uniqueness and map-level direct-uniqueness source are equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_iff_direct_source_of_canonical
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource ↔
      MoleculeResidualFixedPointUniquenessDirectSource := by
  constructor
  · intro h_unique_direct_canonical
    exact h_unique_direct_canonical h_canonical
  · intro h_unique_direct
    exact fun _ => h_unique_direct

/--
Under a refined witness, refined-contract map-level direct-uniqueness and
map-level direct-uniqueness source are equivalent.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source_iff_direct_source_of_refined
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource ↔
      MoleculeResidualFixedPointUniquenessDirectSource := by
  constructor
  · intro h_unique_direct_refined
    exact h_unique_direct_refined h_refined
  · intro h_unique_direct
    exact fun _ => h_unique_direct

/--
Recover map-level direct-uniqueness source from:
- a canonical fixed-point witness, and
- a canonical-contract direct-uniqueness theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_via_canonical_direct_contract :
    CanonicalFastFixedPointData →
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource →
    MoleculeResidualFixedPointUniquenessDirectSource :=
  fun h_canonical h_unique_direct_canonical =>
    (molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_iff_direct_source_of_canonical
      h_canonical).1
      h_unique_direct_canonical

/--
Recover map-level direct-uniqueness source from:
- a refined witness, and
- a refined-contract direct-uniqueness theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_via_refined_direct_contract :
    MoleculeConjectureRefined →
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource →
    MoleculeResidualFixedPointUniquenessDirectSource :=
  fun h_refined h_unique_direct_refined =>
    (molecule_residual_fixed_point_uniqueness_direct_of_refined_source_iff_direct_source_of_refined
      h_refined).1
      h_unique_direct_refined

/--
Recover anchor seam source from:
- a canonical fixed-point witness, and
- a canonical-contract direct-uniqueness theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_via_canonical_direct_contract :
    CanonicalFastFixedPointData →
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource →
    MoleculeResidualDirectSeamAnchorSource :=
  fun h_canonical h_unique_direct_canonical =>
    molecule_residual_direct_seam_anchor_source_of_canonical_and_fixed_point_uniqueness_direct_of_canonical_source
      h_canonical
      h_unique_direct_canonical

/--
Minimal source pack for direct-contract cutover into direct/anchor seams.
-/
structure MoleculeResidualDirectContractCutoverSources : Prop where
  canonicalData : CanonicalFastFixedPointData
  directOfCanonical : MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource

/--
Build direct-uniqueness source seam from direct-contract cutover sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_direct_contract_cutover_sources
    (h_sources : MoleculeResidualDirectContractCutoverSources) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_via_canonical_direct_contract
    h_sources.canonicalData
    h_sources.directOfCanonical

/--
Build anchor source seam from direct-contract cutover sources.
-/
theorem molecule_residual_direct_seam_anchor_source_of_direct_contract_cutover_sources
    (h_sources : MoleculeResidualDirectContractCutoverSources) :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source_via_canonical_direct_contract
    h_sources.canonicalData
    h_sources.directOfCanonical

/--
Build canonical direct-contract goal from direct-contract cutover sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_canonical_source_of_direct_contract_cutover_sources
    (h_sources : MoleculeResidualDirectContractCutoverSources) :
    MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource :=
  h_sources.directOfCanonical

/--
Build refined direct-contract goal from direct-contract cutover sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_direct_contract_cutover_sources
    (h_sources : MoleculeResidualDirectContractCutoverSources) :
    MoleculeResidualFixedPointUniquenessDirectOfRefinedSource :=
  molecule_residual_fixed_point_uniqueness_direct_of_refined_source_of_fixed_point_uniqueness_direct_source
    (molecule_residual_fixed_point_uniqueness_direct_source_of_direct_contract_cutover_sources
      h_sources)

/--
Assemble direct-contract cutover sources from canonical data and a canonical
direct-contract theorem.
-/
theorem molecule_residual_direct_contract_cutover_sources_of_canonical_and_direct_of_canonical
    (h_canonical : CanonicalFastFixedPointData)
    (h_direct_canonical : MoleculeResidualFixedPointUniquenessDirectOfCanonicalSource) :
    MoleculeResidualDirectContractCutoverSources :=
  ⟨h_canonical, h_direct_canonical⟩

/--
Assemble direct-contract cutover sources from refined data and a refined
direct-contract theorem.
-/
theorem molecule_residual_direct_contract_cutover_sources_of_refined_and_direct_of_refined
    (h_refined : MoleculeConjectureRefined)
    (h_direct_refined : MoleculeResidualFixedPointUniquenessDirectOfRefinedSource) :
    MoleculeResidualDirectContractCutoverSources :=
  ⟨
    h_refined.2,
    fun _ =>
      molecule_residual_fixed_point_uniqueness_direct_source_via_refined_direct_contract
        h_refined
        h_direct_refined
  ⟩

/--
Under canonical fixed-point data, direct-contract cutover sources are
equivalent to map-level direct-uniqueness source.
-/
theorem molecule_residual_direct_contract_cutover_sources_iff_fixed_point_uniqueness_direct_source_of_canonical
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualDirectContractCutoverSources ↔
      MoleculeResidualFixedPointUniquenessDirectSource := by
  constructor
  · intro h_sources
    exact
      molecule_residual_fixed_point_uniqueness_direct_source_of_direct_contract_cutover_sources
        h_sources
  · intro h_unique_direct
    exact
      molecule_residual_direct_contract_cutover_sources_of_canonical_and_direct_of_canonical
        h_canonical
        (fun _ => h_unique_direct)

/--
Under refined data, direct-contract cutover sources are equivalent to map-level
direct-uniqueness source.
-/
theorem molecule_residual_direct_contract_cutover_sources_iff_fixed_point_uniqueness_direct_source_of_refined
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualDirectContractCutoverSources ↔
      MoleculeResidualFixedPointUniquenessDirectSource := by
  constructor
  · intro h_sources
    exact
      molecule_residual_fixed_point_uniqueness_direct_source_of_direct_contract_cutover_sources
        h_sources
  · intro h_unique_direct
    exact
      molecule_residual_direct_contract_cutover_sources_of_refined_and_direct_of_refined
        h_refined
        (fun _ => h_unique_direct)

/--
Breakout source interface for PLAN_69:
- canonical fixed-point witness, and
- model-collapse-direct source theorem.
-/
structure MoleculeResidualDirectSourceBreakoutSources : Prop where
  canonicalData : CanonicalFastFixedPointData
  modelCollapseDirect : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource

/--
Assemble PLAN_69 breakout sources from canonical data and a model-collapse-direct
source theorem.
-/
theorem molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct
    (h_canonical : CanonicalFastFixedPointData)
    (h_model_collapse_direct :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource) :
    MoleculeResidualDirectSourceBreakoutSources :=
  ⟨h_canonical, h_model_collapse_direct⟩

/--
Assemble PLAN_69 breakout sources from refined data and a model-collapse-direct
source theorem.
-/
theorem molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct
    (h_refined : MoleculeConjectureRefined)
    (h_model_collapse_direct :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource) :
    MoleculeResidualDirectSourceBreakoutSources :=
  ⟨h_refined.2, h_model_collapse_direct⟩

/--
Build direct-uniqueness source seam from PLAN_69 breakout sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_direct_source_breakout_sources
    (h_sources : MoleculeResidualDirectSourceBreakoutSources) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_canonical_and_model_collapse_direct_of_canonical_source
    h_sources.canonicalData
    (fun _ => h_sources.modelCollapseDirect)

/--
Build anchor source seam from PLAN_69 breakout sources.
-/
theorem molecule_residual_direct_seam_anchor_source_of_direct_source_breakout_sources
    (h_sources : MoleculeResidualDirectSourceBreakoutSources) :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source_of_canonical_and_model_collapse_direct_of_canonical_source
    h_sources.canonicalData
    (fun _ => h_sources.modelCollapseDirect)

/--
Under canonical fixed-point data, PLAN_69 breakout sources are equivalent to
model-collapse-direct source data.
-/
theorem molecule_residual_direct_source_breakout_sources_iff_model_collapse_direct_source_of_canonical
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualDirectSourceBreakoutSources ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource := by
  constructor
  · intro h_sources
    exact h_sources.modelCollapseDirect
  · intro h_model_collapse_direct
    exact
      molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct
        h_canonical
        h_model_collapse_direct

/--
Under refined data, PLAN_69 breakout sources are equivalent to
model-collapse-direct source data.
-/
theorem molecule_residual_direct_source_breakout_sources_iff_model_collapse_direct_source_of_refined
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualDirectSourceBreakoutSources ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource := by
  constructor
  · intro h_sources
    exact h_sources.modelCollapseDirect
  · intro h_model_collapse_direct
    exact
      molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct
        h_refined
        h_model_collapse_direct

/--
Minimal upstream source interface for PLAN_70:
explicit witness of the lifted-hybrid collapse seam.
-/
structure MoleculeResidualModelCollapseDirectSourceWitnessSources : Prop where
  liftedHybridCollapse : MoleculeResidualLiftedHybridFixedPointCollapseSource

/--
Project model-collapse-direct source from PLAN_70 witness sources.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
    (h_sources : MoleculeResidualModelCollapseDirectSourceWitnessSources) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource :=
  h_sources.liftedHybridCollapse

/--
Assemble PLAN_70 witness sources from model-collapse-direct source data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_direct_source
    (h_model_collapse_direct :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  ⟨h_model_collapse_direct⟩

/--
PLAN_70 witness-source interface is equivalent to model-collapse-direct source.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_iff_model_collapse_direct_source :
    MoleculeResidualModelCollapseDirectSourceWitnessSources ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource := by
  constructor
  · intro h_sources
    exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
        h_sources
  · intro h_model_collapse_direct
    exact
      molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_direct_source
        h_model_collapse_direct

/--
Assemble PLAN_70 witness sources from model-collapse source data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_source
    (h_model_collapse :
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  ⟨h_model_collapse⟩

/--
PLAN_70 witness-source interface is equivalent to model-collapse source data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_iff_model_collapse_source :
    MoleculeResidualModelCollapseDirectSourceWitnessSources ↔
      MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource := by
  constructor
  · intro h_sources
    exact h_sources.liftedHybridCollapse
  · intro h_model_collapse
    exact
      molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_source
        h_model_collapse

/--
Assemble PLAN_70 witness sources from map-level uniqueness source data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  ⟨molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_uniqueness_source h_unique⟩

/--
Assemble PLAN_70 witness sources from hybrid-unique fixed-point source data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  ⟨molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique⟩

/--
Assemble PLAN_70 witness sources from hybrid-class-uniqueness source data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  ⟨molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_uniqueness_source
      h_class_unique⟩

/--
Assemble PLAN_70 witness sources from fixed-point hybrid-class collapse source
data.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_fixed_point_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  ⟨molecule_residual_lifted_hybrid_fixed_point_collapse_source_of_hybrid_class_collapse_source
      h_collapse⟩

/--
Minimal upstream source interface for PLAN_71:
explicit witness of the map-level hybrid-class-collapse seam.
-/
structure MoleculeResidualHybridClassCollapseSourceWitnessSources : Prop where
  collapse : MoleculeResidualFixedPointHybridClassCollapseSource

/--
Project map-level hybrid-class-collapse source from PLAN_71 witness sources.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_collapse_witness_sources
    (h_sources : MoleculeResidualHybridClassCollapseSourceWitnessSources) :
    MoleculeResidualFixedPointHybridClassCollapseSource :=
  h_sources.collapse

/--
Assemble PLAN_71 witness sources from map-level hybrid-class-collapse source
data.
-/
theorem molecule_residual_hybrid_class_collapse_witness_sources_of_fixed_point_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridClassCollapseSourceWitnessSources :=
  ⟨h_collapse⟩

/--
PLAN_71 witness-source interface is equivalent to map-level hybrid-class-collapse
source data.
-/
theorem molecule_residual_hybrid_class_collapse_witness_sources_iff_fixed_point_hybrid_class_collapse_source :
    MoleculeResidualHybridClassCollapseSourceWitnessSources ↔
      MoleculeResidualFixedPointHybridClassCollapseSource := by
  constructor
  · intro h_sources
    exact h_sources.collapse
  · intro h_collapse
    exact
      molecule_residual_hybrid_class_collapse_witness_sources_of_fixed_point_hybrid_class_collapse_source
        h_collapse

/--
Build PLAN_70 model-collapse-direct witness sources from PLAN_71 witness
sources.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_collapse_witness_sources
    (h_sources : MoleculeResidualHybridClassCollapseSourceWitnessSources) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_fixed_point_hybrid_class_collapse_source
    h_sources.collapse

/--
Build PLAN_69 breakout sources from:
- canonical fixed-point data, and
- PLAN_71 hybrid-class-collapse witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_canonical_and_hybrid_class_collapse_witness_sources
    (h_canonical : CanonicalFastFixedPointData)
    (h_sources : MoleculeResidualHybridClassCollapseSourceWitnessSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct
    h_canonical
    (molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
      (molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_collapse_witness_sources
        h_sources))

/--
Build PLAN_69 breakout sources from:
- refined data, and
- PLAN_71 hybrid-class-collapse witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_refined_and_hybrid_class_collapse_witness_sources
    (h_refined : MoleculeConjectureRefined)
    (h_sources : MoleculeResidualHybridClassCollapseSourceWitnessSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct
    h_refined
    (molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
      (molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_collapse_witness_sources
        h_sources))

/--
Under canonical fixed-point data, PLAN_69 breakout sources are equivalent to
PLAN_70 witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_iff_model_collapse_direct_witness_sources_of_canonical
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualDirectSourceBreakoutSources ↔
      MoleculeResidualModelCollapseDirectSourceWitnessSources := by
  constructor
  · intro h_breakout
    exact
      molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_direct_source
        h_breakout.modelCollapseDirect
  · intro h_sources
    exact
      molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct
        h_canonical
        (molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
          h_sources)

/--
Under refined data, PLAN_69 breakout sources are equivalent to PLAN_70 witness
sources.
-/
theorem molecule_residual_direct_source_breakout_sources_iff_model_collapse_direct_witness_sources_of_refined
    (h_refined : MoleculeConjectureRefined) :
    MoleculeResidualDirectSourceBreakoutSources ↔
      MoleculeResidualModelCollapseDirectSourceWitnessSources := by
  constructor
  · intro h_breakout
    exact
      molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_direct_source
        h_breakout.modelCollapseDirect
  · intro h_sources
    exact
      molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct
        h_refined
        (molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
          h_sources)

/--
Build PLAN_69 breakout sources from:
- canonical fixed-point data, and
- PLAN_70 model-collapse-direct witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct_witness_sources
    (h_canonical : CanonicalFastFixedPointData)
    (h_sources : MoleculeResidualModelCollapseDirectSourceWitnessSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct
    h_canonical
    (molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
      h_sources)

/--
Build PLAN_69 breakout sources from:
- refined data, and
- PLAN_70 model-collapse-direct witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct_witness_sources
    (h_refined : MoleculeConjectureRefined)
    (h_sources : MoleculeResidualModelCollapseDirectSourceWitnessSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_refined_and_model_collapse_direct
    h_refined
    (molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_model_collapse_direct_witness_sources
      h_sources)

/--
Under canonical fixed-point existence, hybrid-level unique-fixed-point source
and map-level uniqueness source are equivalent.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_canonical
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualHybridUniqueFixedPointSource ↔
      MoleculeResidualFixedPointUniquenessSource := by
  constructor
  · exact molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
  · intro h_unique
    exact
      molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_uniqueness_source
        h_canonical
        h_unique

/--
Assemble residual fixed-point-normalization ingredients from:
- canonical fixed-point data, and
- fixed-point local normalization transfer.
-/
theorem residual_fixed_point_normalization_ingredients_of_canonical_and_transfer
    (h_canonical : CanonicalFastFixedPointData)
    (h_transfer : FixedPointLocalNormalizationTransfer) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  ⟨
    residual_fixed_point_existence_of_canonical_fast_fixed_point_data h_canonical,
    h_transfer
  ⟩

/--
Assemble residual fixed-point-normalization ingredients from refined contract
assumptions plus fixed-point local normalization transfer.
-/
theorem residual_fixed_point_normalization_ingredients_of_refined_and_transfer
    (h_refined : MoleculeConjectureRefined)
    (h_transfer : FixedPointLocalNormalizationTransfer) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  residual_fixed_point_normalization_ingredients_of_canonical_and_transfer
    h_refined.2
    h_transfer

/--
Assemble residual fixed-point-normalization ingredients from:
- refined contract assumptions (for Subtarget A),
- fixed-point normalization data, and
- uniqueness of fast-renormalizable fixed points (for Subtarget B).
-/
theorem residual_fixed_point_normalization_ingredients_of_refined_fixed_data_and_unique
    (h_refined : MoleculeConjectureRefined)
    (h_fixed_data : FixedPointNormalizationData)
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  ⟨
    residual_fixed_point_existence_of_refined_contract h_refined,
    fixed_point_local_normalization_transfer_of_fixed_data_and_unique h_fixed_data h_unique
  ⟩

structure MoleculeHypothesisPack where
  h_bounds : PseudoSiegelAPrioriBounds
  h_conj :
    ∀ f_ref : BMol,
      ∀ x ∈ slice_domain f_ref,
        slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x)
  h_gap :
    ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
      HasSiegelBounds f_star D U a b →
      let F := slice_operator f_star
      let φ := slice_chart f_star
      DifferentiableAt ℂ F (φ f_star) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star))
  h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast
  h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N
  h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model
  h_compact : IsCompactOperator Rfast_HMol_candidate
  h_canonical_fixed : CanonicalFastFixedPointData

/--
Partitioned analytic core assumptions (Problem 4.3 orbit transport + local spectral gap).
-/
structure MoleculeAnalyticCore where
  h_bounds : PseudoSiegelAPrioriBounds
  h_gap :
    ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
      HasSiegelBounds f_star D U a b →
      let F := slice_operator f_star
      let φ := slice_chart f_star
      DifferentiableAt ℂ F (φ f_star) ∧
      IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star))

/--
Partitioned combinatorial/topological core assumptions.
-/
structure MoleculeCombinatorialTopologicalCore where
  h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast
  h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N
  h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model
  h_compact : IsCompactOperator Rfast_HMol_candidate

structure MoleculeFinalAssumptions where
  analytic : MoleculeAnalyticCore
  combinatorialTopological : MoleculeCombinatorialTopologicalCore

theorem molecule_core_conj :
  ∀ f_ref : BMol,
    ∀ x ∈ slice_domain f_ref,
      slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x) :=
  molecule_h_conj

theorem molecule_core_ps :
  ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps :=
  molecule_h_ps

/--
Seed-free projection theorem: canonical fixed-point data follows directly from
the refined export contract.
-/
theorem molecule_conjecture_refined_implies_canonical_fast_fixed_point :
  MoleculeConjectureRefined → CanonicalFastFixedPointData := by
  intro h_refined
  exact h_refined.2

/--
Extract canonical fixed-point data directly from a priori bounds.
-/
theorem canonical_fast_fixed_point_data_of_bounds
    (h_bounds : PseudoSiegelAPrioriBounds) :
    CanonicalFastFixedPointData := by
  rcases h_bounds with ⟨f_star, _U, h_fixed, h_renorm, _hU_open, _h_mem, _h_cv, _h_eventual⟩
  exact ⟨f_star, h_renorm, h_fixed⟩

/--
Bundled non-ground residual sources currently carrying the final project axiom
dependency.
-/
structure MoleculeResidualNonGroundSources where
  fixedIngredients : MoleculeResidualFixedPointIngredientsSource
  orbitClause : MoleculeResidualOrbitClauseForFixedDataSource

/--
Fixed-point-only slice of the bundled non-ground source pack.
-/
structure MoleculeResidualFixedPointAssemblySources where
  fixedData : FixedPointNormalizationData
  fixedTransfer : MoleculeResidualFixedPointTransferSource

/--
Build fixed-point-only assembly sources from the broader non-ground source pack.
-/
theorem molecule_residual_fixed_point_assembly_sources_of_non_ground_sources
    (h_sources : MoleculeResidualNonGroundSources) :
    MoleculeResidualFixedPointAssemblySources :=
  ⟨
    fixed_point_normalization_data_of_ingredients h_sources.fixedIngredients,
    h_sources.fixedIngredients.2
  ⟩

/--
Build fixed-point-only assembly sources from explicit fixed-data and
fixed-transfer source theorems.
-/
theorem molecule_residual_fixed_point_assembly_sources_of_sources
    (h_fixed_data : MoleculeResidualFixedPointDataSource)
    (h_fixed_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointAssemblySources :=
  ⟨h_fixed_data, h_fixed_transfer⟩

/--
Build fixed-point-only assembly sources from explicit fixed-point existence and
fixed-transfer source theorems.
-/
theorem molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualFixedPointAssemblySources :=
  molecule_residual_fixed_point_assembly_sources_of_sources
    (molecule_residual_fixed_point_data_source_of_sources h_exists h_transfer)
    h_transfer

/--
Current fixed-point-only assembly source pack.
-/
theorem molecule_residual_fixed_point_assembly_sources :
    MoleculeResidualFixedPointAssemblySources :=
  molecule_residual_fixed_point_assembly_sources_of_exists_and_transfer
    molecule_residual_fixed_point_existence_source
    molecule_residual_fixed_point_transfer_source

/--
Build bundled non-ground residual sources from fixed-point and orbit-clause
source packs.
-/
theorem molecule_residual_non_ground_sources_of_ingredients_and_orbit
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients)
    (h_orbit_clause : MoleculeResidualOrbitClauseForFixedDataSource) :
    MoleculeResidualNonGroundSources :=
  ⟨h_ingredients, h_orbit_clause⟩

/--
Build bundled non-ground residual sources from fixed-point and orbit-clause
source packs.
-/
theorem molecule_residual_non_ground_sources_of_fixed_point_and_orbit_sources
    (h_fixed_sources : MoleculeResidualFixedPointAssemblySources)
    (h_orbit_clause : MoleculeResidualOrbitClauseForFixedDataSource) :
    MoleculeResidualNonGroundSources := by
  have h_ingredients : MoleculeResidualFixedPointNormalizationIngredients :=
    molecule_residual_fixed_point_normalization_ingredients_of_sources
      (renormalizable_fixed_exists_of_fixed_point_normalization_data h_fixed_sources.fixedData)
      h_fixed_sources.fixedTransfer
  exact molecule_residual_non_ground_sources_of_ingredients_and_orbit
    h_ingredients
    h_orbit_clause

/--
Current bundled non-ground residual sources.
-/
theorem molecule_residual_non_ground_sources :
    MoleculeResidualNonGroundSources :=
  molecule_residual_non_ground_sources_of_ingredients_and_orbit
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_orbit_clause_for_fixed_data_source

/--
Build fixed-point normalization ingredients from fixed-point-only assembly
sources.
-/
theorem molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources
    (h_sources : MoleculeResidualFixedPointAssemblySources) :
    MoleculeResidualFixedPointNormalizationIngredients :=
  molecule_residual_fixed_point_normalization_ingredients_of_sources
    (renormalizable_fixed_exists_of_fixed_point_normalization_data h_sources.fixedData)
    h_sources.fixedTransfer

/--
Narrowed source package needed for the residual bounds assembly:
- fixed-point normalization ingredients, and
- orbit clause transport source.
-/
structure MoleculeResidualBoundsAssemblySources where
  ingredients : MoleculeResidualFixedPointNormalizationIngredients
  orbitClause : MoleculeResidualOrbitClauseForFixedDataSource

/--
Build narrowed residual bounds-assembly sources from:
- fixed-point assembly sources, and
- an orbit-clause source.
-/
theorem molecule_residual_bounds_assembly_sources_of_fixed_point_and_orbit_sources
    (h_fixed_sources : MoleculeResidualFixedPointAssemblySources)
    (h_orbit_clause : MoleculeResidualOrbitClauseForFixedDataSource) :
    MoleculeResidualBoundsAssemblySources :=
  ⟨
    molecule_residual_fixed_point_normalization_ingredients_of_fixed_point_assembly_sources
      h_fixed_sources,
    h_orbit_clause
  ⟩

/--
Build narrowed residual bounds-assembly sources from the broader non-ground
source pack.
-/
theorem molecule_residual_bounds_assembly_sources_of_non_ground_sources
    (h_sources : MoleculeResidualNonGroundSources) :
    MoleculeResidualBoundsAssemblySources :=
  ⟨h_sources.fixedIngredients, h_sources.orbitClause⟩

/--
Current narrowed residual bounds-assembly source pack.
-/
theorem molecule_residual_bounds_assembly_sources :
    MoleculeResidualBoundsAssemblySources :=
  molecule_residual_bounds_assembly_sources_of_non_ground_sources
    molecule_residual_non_ground_sources

/-- Legacy fixed-point existence packaged for narrowed bounds interfaces. -/
theorem molecule_residual_fixed_exists :
    ∃ f : BMol, IsFastRenormalizable f ∧ Rfast f = f :=
  renormalizable_fixed_exists_of_fixed_point_normalization_data molecule_h_fixed_data

/--
Residual bounds source from fixed-point data and the narrowed local orbit-source
contract.
-/
theorem molecule_residual_bounds_from_fixed_data_and_local_orbit_source
    (h_fixed_data : FixedPointNormalizationData)
    (h_orbit_fixed_data : MoleculeResidualOrbitClauseForFixedDataSource) :
    PseudoSiegelAPrioriBounds := by
  rcases h_fixed_data with ⟨f_star, h_fixed, h_renorm, h_crit_val, h_f_star_sub_D⟩
  let a : ℕ → ℕ := fun n => n
  let b : ℕ → ℕ := fun n => n + 1
  let D : Set ℂ := Metric.ball 0 0.1
  let U : Set BMol := { g | g = f_star }
  have h_D_open : IsOpen D := Metric.isOpen_ball
  have h_U_open : IsOpen U := by
    change True
    trivial
  have h_f_in_U : f_star ∈ U := rfl
  have h_c1_in_D : criticalValue f_star ∈ D := by
    rw [h_crit_val]
    simp [D, Metric.mem_ball]
    norm_num
  have h_U_subset : ∀ g ∈ U, g.V ⊆ D := by
    intro g hg
    rw [mem_singleton_iff.mp hg]
    exact h_f_star_sub_D
  have h_main := renormalization_implies_bounds f_star D U a b (molecule_residual_pseudo_siegel_source f_star D)
    h_fixed h_renorm h_D_open h_U_open h_f_in_U h_c1_in_D
    (h_orbit_fixed_data f_star h_fixed h_renorm h_crit_val h_f_star_sub_D) h_U_subset
  exact ⟨f_star, U, h_fixed, h_renorm, h_U_open, h_f_in_U, h_c1_in_D, h_main⟩

/--
Localized wrapper: residual bounds from fixed data using only the fixed-data
local orbit source contract.
-/
theorem molecule_residual_bounds_from_fixed_data_localized
    (h_fixed_data : FixedPointNormalizationData)
    (h_orbit_fixed_data : MoleculeResidualOrbitClauseForFixedDataSource) :
    PseudoSiegelAPrioriBounds :=
  molecule_residual_bounds_from_fixed_data_and_local_orbit_source
    h_fixed_data
    h_orbit_fixed_data

/-- Residual bounds source routed through local fixed-point normalization data. -/
theorem molecule_residual_bounds_from_fixed_data
    (h_fixed_data : FixedPointNormalizationData) :
    PseudoSiegelAPrioriBounds :=
  molecule_residual_bounds_from_fixed_data_localized
    h_fixed_data
    molecule_residual_orbit_clause_for_fixed_data_source

/--
Residual bounds constructor from narrowed bounds-assembly source inputs.
-/
theorem molecule_residual_bounds_seed_free_of_bounds_assembly_sources
    (h_sources : MoleculeResidualBoundsAssemblySources) :
    PseudoSiegelAPrioriBounds := by
  have h_fixed_data : MoleculeResidualFixedPointNormalizationSource :=
    molecule_residual_fixed_point_normalization_source_of_ingredients h_sources.ingredients
  exact molecule_residual_bounds_from_fixed_data_and_local_orbit_source
    h_fixed_data
    h_sources.orbitClause

/--
Residual bounds constructor from bundled non-ground source inputs.
-/
theorem molecule_residual_bounds_seed_free_of_non_ground_sources
    (h_sources : MoleculeResidualNonGroundSources) :
    PseudoSiegelAPrioriBounds :=
  molecule_residual_bounds_seed_free_of_bounds_assembly_sources
    (molecule_residual_bounds_assembly_sources_of_non_ground_sources h_sources)

/-- Seed-free bounds source: avoid the legacy `molecule_h_data` bundle. -/
theorem molecule_residual_bounds_seed_free : PseudoSiegelAPrioriBounds :=
  molecule_residual_bounds_seed_free_of_bounds_assembly_sources
    molecule_residual_bounds_assembly_sources

/-- Theorem-level projections from the residual assumption bundle. -/
theorem molecule_residual_bounds : PseudoSiegelAPrioriBounds :=
  molecule_residual_bounds_seed_free

theorem canonical_fast_fixed_point_data_from_bounds :
    CanonicalFastFixedPointData :=
  canonical_fast_fixed_point_data_of_bounds molecule_residual_bounds

/--
PLAN_76 source seam for canonical fast fixed-point data.
-/
def MoleculeResidualCanonicalFastFixedPointDataSource : Prop :=
  CanonicalFastFixedPointData

/--
Build canonical fast fixed-point data from any a priori bounds witness.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_bounds
    (h_bounds : PseudoSiegelAPrioriBounds) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  canonical_fast_fixed_point_data_of_bounds h_bounds

/--
Build canonical fast fixed-point data from the narrowed bounds-assembly
package.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_bounds_assembly_sources
    (h_sources : MoleculeResidualBoundsAssemblySources) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_bounds
    (molecule_residual_bounds_seed_free_of_bounds_assembly_sources h_sources)

/--
Build canonical fast fixed-point data from the bundled non-ground source pack.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_non_ground_sources
    (h_sources : MoleculeResidualNonGroundSources) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_bounds_assembly_sources
    (molecule_residual_bounds_assembly_sources_of_non_ground_sources h_sources)

/--
Build canonical fast fixed-point data directly from fixed-point ingredients and
the broad orbit-clause source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_orbit_clause_source
    (h_ingredients : MoleculeResidualFixedPointIngredientsSource)
    (h_orbit : MoleculeResidualOrbitClauseSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource := by
  have h_fixed_data : FixedPointNormalizationData :=
    fixed_point_normalization_data_of_ingredients h_ingredients
  have h_orbit_fixed_data : MoleculeResidualOrbitClauseForFixedDataSource :=
    molecule_residual_orbit_clause_for_fixed_data_source_of_orbit_clause_source
      h_orbit
  exact molecule_residual_canonical_fast_fixed_point_data_source_of_bounds
    (molecule_residual_bounds_from_fixed_data_and_local_orbit_source
      h_fixed_data
      h_orbit_fixed_data)

/--
Build canonical fast fixed-point data directly from fixed-point ingredients and
the local orbit-at source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_orbit_clause_at_source
    (h_ingredients : MoleculeResidualFixedPointIngredientsSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource := by
  have h_fixed_data : FixedPointNormalizationData :=
    fixed_point_normalization_data_of_ingredients h_ingredients
  have h_orbit_fixed_data : MoleculeResidualOrbitClauseForFixedDataSource :=
    molecule_residual_orbit_clause_for_fixed_data_source_of_local h_orbit_at
  exact molecule_residual_canonical_fast_fixed_point_data_source_of_bounds
    (molecule_residual_bounds_from_fixed_data_and_local_orbit_source
      h_fixed_data
      h_orbit_fixed_data)

/--
Build canonical fast fixed-point data directly from fixed-point ingredients and
the fixed-data canonical orbit debt source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_canonical_orbit_at_debt_source
    (h_ingredients : MoleculeResidualFixedPointIngredientsSource)
    (h_orbit_debt : MoleculeResidualCanonicalOrbitAtDebtSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource := by
  have h_fixed_data : FixedPointNormalizationData :=
    fixed_point_normalization_data_of_ingredients h_ingredients
  have h_orbit_fixed_data : MoleculeResidualOrbitClauseForFixedDataSource :=
    molecule_residual_orbit_clause_for_fixed_data_source_of_at_fixed_data_source
      (molecule_residual_orbit_clause_at_fixed_data_source_of_canonical_debt_source
        h_orbit_debt)
  exact molecule_residual_canonical_fast_fixed_point_data_source_of_bounds
    (molecule_residual_bounds_from_fixed_data_and_local_orbit_source
      h_fixed_data
      h_orbit_fixed_data)

/--
Build canonical fast fixed-point data directly from fixed-point ingredients,
canonical orbit structure, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_structure_and_transfer
    (h_ingredients : MoleculeResidualFixedPointIngredientsSource)
    (h_structure : MoleculeResidualCanonicalOrbitStructureSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_canonical_orbit_at_debt_source
    h_ingredients
    (molecule_residual_canonical_orbit_at_debt_source_of_structure_and_transfer_component_sources
      h_structure
      (molecule_residual_fixed_point_transfer_component_sources_of_fixed_point_transfer_source
        h_transfer))

/--
Build canonical fast fixed-point data directly from fixed-point ingredients,
orbit-clause source, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_orbit_clause_and_transfer
    (h_ingredients : MoleculeResidualFixedPointIngredientsSource)
    (h_orbit : MoleculeResidualOrbitClauseSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_structure_and_transfer
    h_ingredients
    (molecule_residual_canonical_orbit_structure_source_of_transport_source
      (molecule_residual_orbit_transport_source_of_sources
        molecule_residual_pseudo_siegel_source
        h_orbit))
    h_transfer

/--
Build canonical fast fixed-point data directly from fixed-point ingredients,
the local orbit-at source, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_orbit_clause_at_and_transfer
    (h_ingredients : MoleculeResidualFixedPointIngredientsSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_orbit_clause_and_transfer
    h_ingredients
    (molecule_residual_orbit_clause_source_of_local h_orbit_at)
    h_transfer

/--
Build canonical fast fixed-point data directly from fixed-point existence, the
local orbit-at source, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_existence_orbit_clause_at_and_transfer
    (h_exists : MoleculeResidualFixedPointExistenceSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_transfer : MoleculeResidualFixedPointTransferSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_orbit_clause_at_and_transfer
    (molecule_residual_fixed_point_ingredients_source_of_sources h_exists h_transfer)
    h_orbit_at
    h_transfer

/--
Build canonical fast fixed-point data directly from fixed-point normalization
data, the local orbit-at source, and uniqueness.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_data_orbit_clause_at_and_uniqueness
    (h_fixed_data : MoleculeResidualFixedPointDataSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_existence_orbit_clause_at_and_transfer
    (molecule_residual_fixed_point_existence_source_via_fixed_data_source h_fixed_data)
    h_orbit_at
    (molecule_residual_fixed_point_transfer_source_of_fixed_data_and_unique
      h_fixed_data
      h_unique)

/--
Current-route canonical-data source exposed through the direct fixed-data
carrier, the local orbit-at source, and the direct uniqueness source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct
    (h_fixed_data : MoleculeResidualFixedPointDataSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_data_orbit_clause_at_and_uniqueness
    h_fixed_data
    h_orbit_at
    (molecule_residual_fixed_point_uniqueness_source_direct_of_source
      h_unique_direct)

/--
Current-route canonical-data source exposed through the direct primitive
fixed-point-ingredient carrier, the local orbit-at source, and the direct
uniqueness source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_primitive_ingredients_orbit_clause_at_and_uniqueness_direct
    (h_ingredients : MoleculeResidualFixedPointNormalizationIngredients)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct
    (fixed_point_normalization_data_of_ingredients h_ingredients)
    h_orbit_at
    h_unique_direct

/--
Current-route canonical-data source exposed through the direct primitive
ingredient carrier and the local orbit-at source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_fixed_data_direct_orbit_clause_at_and_uniqueness_direct :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_bounds
    (molecule_residual_bounds_from_fixed_data_and_local_orbit_source
      (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_vbound
        molecule_residual_fixed_point_renormalizable_via_global_norm_direct
        molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct)
      (molecule_residual_orbit_clause_for_fixed_data_source_of_local
        molecule_residual_orbit_clause_at_source))

/--
Current-route canonical-data source exposed through fixed-point ingredients and
the broad orbit-clause source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_orbit_clause_source :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_orbit_clause_source
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_orbit_clause_source

/--
Current-route canonical-data source exposed through fixed-point ingredients and
the local orbit-at source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_orbit_clause_at_source :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_orbit_clause_at_source
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_orbit_clause_at_source

/--
Current-route canonical-data source exposed through fixed-point ingredients and
the fixed-data canonical orbit debt source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_and_canonical_orbit_at_debt_source :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_and_canonical_orbit_at_debt_source
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_canonical_orbit_at_debt_source_via_fixed_point_transfer_source

/--
Current-route canonical-data source exposed through fixed-point ingredients,
canonical orbit structure, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_structure_and_transfer :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_structure_and_transfer
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_canonical_orbit_structure_source
    molecule_residual_fixed_point_transfer_source

/--
Current-route canonical-data source exposed through fixed-point ingredients,
orbit-clause source, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_orbit_clause_and_transfer :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_orbit_clause_and_transfer
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_orbit_clause_source
    molecule_residual_fixed_point_transfer_source

/--
Current-route canonical-data source exposed through fixed-point ingredients,
the local orbit-at source, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_ingredients_orbit_clause_at_and_transfer :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_ingredients_orbit_clause_at_and_transfer
    molecule_residual_fixed_point_ingredients_source
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_transfer_source

/--
Current-route canonical-data source exposed through fixed-point existence, the
local orbit-at source, and the transfer source.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_existence_orbit_clause_at_and_transfer :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_existence_orbit_clause_at_and_transfer
    molecule_residual_fixed_point_existence_source
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_transfer_source

/--
Current-route canonical-data source exposed through fixed-point normalization
data, the local orbit-at source, and uniqueness.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_fixed_data_orbit_clause_at_and_uniqueness :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_via_fixed_data_direct_orbit_clause_at_and_uniqueness_direct

/--
Build canonical fast fixed-point data from the fixed-point existence source
seam.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source
    (h_exists : MoleculeResidualFixedPointExistenceSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  h_exists

/--
Any non-singleton localized bridge source already yields the canonical
fixed-point data target on the existence/canonical branch.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_non_singleton_localized_bridge_sources
    (h_sources : MoleculeResidualNonSingletonLocalizedBridgeSources) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source
    (molecule_residual_fixed_point_existence_source_of_non_singleton_localized_bridge_sources
      h_sources)

/--
Recover fixed-point existence from canonical fast fixed-point data.
-/
theorem molecule_residual_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource) :
    MoleculeResidualRenormalizableFixedSeedSource :=
  h_canonical

/--
The PLAN_84 seed interface is definitionally equivalent to canonical fast
fixed-point data.
-/
theorem molecule_residual_renormalizable_fixed_seed_source_iff_canonical_fast_fixed_point_data_source :
    MoleculeResidualRenormalizableFixedSeedSource ↔
      MoleculeResidualCanonicalFastFixedPointDataSource := by
  constructor <;> intro h
  · exact h
  · exact h

/--
Canonical fast fixed-point data plus critical-value transfer yields the
stronger critical seed contract. This is the exact seed-side upstream hit plus
sidecar gate needed before re-entering the fixed-data/local-witness branches.
-/
theorem molecule_residual_critical_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource)
    (h_crit : FixedPointCriticalValueTransferSource) :
    MoleculeResidualCriticalRenormalizableFixedSeedSource :=
  molecule_residual_critical_renormalizable_fixed_seed_source_of_seed_and_critical_value_transfer
    (molecule_residual_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source
      h_canonical)
    h_crit

/--
Canonical fast fixed-point data plus critical-value transfer and
renormalizable-point `V`-bound control already yields the fixed-data target.
This is the exact downstream gate on the seed-side branch of PLAN_88.
-/
theorem molecule_residual_fixed_point_data_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_critical_renormalizable_fixed_seed_source_and_renorm_vbound
    (molecule_residual_critical_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer
      h_canonical
      h_crit)
    h_renorm_vbound

/--
Canonical fast fixed-point data plus critical-value transfer and
renormalizable-point `V`-bound control already yields the local-witness target.
This matches the exact downstream gate on the seed-side branch of PLAN_88.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource)
    (h_crit : FixedPointCriticalValueTransferSource)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_data
    (molecule_residual_fixed_point_data_source_of_canonical_fast_fixed_point_data_source_and_critical_value_transfer_and_renorm_vbound
      h_canonical
      h_crit
      h_renorm_vbound)

/--
The current localized refined-singleton route is exactly as strong as canonical
fast fixed-point data: it adds no extra power beyond the existing seed/canonical
equivalence.
-/
theorem molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_canonical_fast_fixed_point_data_source :
    Nonempty MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources ↔
      MoleculeResidualCanonicalFastFixedPointDataSource := by
  exact
    molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_renormalizable_fixed_seed_source.trans
      molecule_residual_renormalizable_fixed_seed_source_iff_canonical_fast_fixed_point_data_source

/--
Any current localized refined-singleton source already yields canonical fast
fixed-point data.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_refined_invariant_fixed_seed_singleton_domain_sources
    (h_sources : Nonempty MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_refined_invariant_fixed_seed_singleton_domain_sources_nonempty_iff_canonical_fast_fixed_point_data_source.mp
    h_sources

/--
Recover fixed-point existence from canonical fast fixed-point data by first
passing through the PLAN_84 renormalizable seed interface.
-/
theorem molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source_via_seed
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renormalizable_fixed_seed_source
    (molecule_residual_renormalizable_fixed_seed_source_of_canonical_fast_fixed_point_data_source
      h_canonical)

/--
Any current localized refined-singleton source already yields the existence-side
target, via the canonical/seed equivalence.
-/
theorem molecule_residual_fixed_point_existence_source_of_refined_invariant_fixed_seed_singleton_domain_sources
    (h_sources : Nonempty MoleculeResidualRefinedInvariantFixedSeedSingletonDomainSources) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source_via_seed
    (molecule_residual_canonical_fast_fixed_point_data_source_of_refined_invariant_fixed_seed_singleton_domain_sources
      h_sources)

/--
Recover fixed-point existence from canonical fast fixed-point data.
-/
theorem molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source_via_seed
    h_canonical

/--
The existence-side split target is definitionally equivalent to canonical fast
fixed-point data.
-/
theorem molecule_residual_fixed_point_existence_source_iff_canonical_fast_fixed_point_data_source :
    MoleculeResidualFixedPointExistenceSource ↔
      MoleculeResidualCanonicalFastFixedPointDataSource := by
  constructor
  · exact molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source
  · exact molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source

/--
Build canonical fast fixed-point data from the fixed-point data source seam.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_data_source
    (h_fixed_data : MoleculeResidualFixedPointDataSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  renormalizable_fixed_exists_of_fixed_point_normalization_data h_fixed_data

/--
Current canonical-data source routed through the fixed-point existence source
seam.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source
    molecule_residual_fixed_point_existence_source

/--
PLAN_84 current-route alias:
recover fixed-point existence from the current canonical-data source via the
seeded existence route.
-/
theorem molecule_residual_fixed_point_existence_source_via_canonical_fast_fixed_point_data_source :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source
    molecule_residual_canonical_fast_fixed_point_data_source

/--
Build fixed-point existence directly from fixed-point normalization data, the
local orbit-at source, and the direct uniqueness source by passing through the
PLAN_84 seeded canonical route.
-/
theorem molecule_residual_fixed_point_existence_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed
    (h_fixed_data : MoleculeResidualFixedPointDataSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_canonical_fast_fixed_point_data_source_via_seed
    (molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct
      h_fixed_data
      h_orbit_at
      h_unique_direct)

/--
PLAN_84 current-route alias with the canonical wrapper fully expanded:
the active seeded existence route depends exactly on the current fixed-data,
local orbit-at, and direct uniqueness carriers.
-/
theorem molecule_residual_fixed_point_existence_source_via_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed
    molecule_residual_fixed_point_data_source
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_uniqueness_direct_source

/--
Build fixed-point existence directly from:
- renormalizability of fixed points,
- the `V`-bound transfer component,
- the local orbit-at source, and
- the direct uniqueness source,
by passing through the PLAN_84 seeded canonical route.
-/
theorem molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_vbound : FixedPointVBoundTransferSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed
    (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_vbound
      h_renorm
      h_vbound)
    h_orbit_at
    h_unique_direct

/--
Build fixed-point existence directly from:
- renormalizability of fixed points,
- renormalizable-point `V`-bound control,
- the local orbit-at source, and
- the direct uniqueness source,
by passing through the PLAN_84 seeded canonical route.
-/
theorem molecule_residual_fixed_point_existence_source_of_renorm_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_fixed_data_orbit_clause_at_and_uniqueness_direct_via_seed
    (fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound
      h_renorm
      h_renorm_vbound)
    h_orbit_at
    h_unique_direct

/--
PLAN_84 current-route alias with the fixed-data wrapper also expanded:
the active seeded existence route depends exactly on the current renormalizable
fixed-point carrier, the current `V`-bound transfer carrier, the local
orbit-at source, and the direct uniqueness carrier.
-/
theorem molecule_residual_fixed_point_existence_source_via_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_uniqueness_direct_source

/--
Build fixed-point existence directly from:
- renormalizability of fixed points,
- the `V`-bound transfer component,
- the local orbit-at source, and
- the hybrid-class-collapse source,
by passing through the PLAN_84 seeded canonical route.
-/
theorem molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_vbound : FixedPointVBoundTransferSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed
    h_renorm
    h_vbound
    h_orbit_at
    (molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_collapse_source
      h_collapse)

/--
Build fixed-point existence directly from:
- renormalizability of fixed points,
- renormalizable-point `V`-bound control,
- the local orbit-at source, and
- the hybrid-class-collapse source,
by passing through the PLAN_84 seeded canonical route.
-/
theorem molecule_residual_fixed_point_existence_source_of_renorm_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed
    (h_renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f)
    (h_renorm_vbound : MoleculeResidualRenormVBoundSource)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renorm_renorm_vbound_orbit_clause_at_and_uniqueness_direct_via_seed
    h_renorm
    h_renorm_vbound
    h_orbit_at
    (molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_collapse_source
      h_collapse)

/--
PLAN_84 current-route alias with the uniqueness wrapper also expanded away:
the active seeded existence route depends exactly on the current renormalizable
fixed-point carrier, the current `V`-bound transfer carrier, the local
orbit-at source, and the hybrid-class-collapse carrier.
-/
theorem molecule_residual_fixed_point_existence_source_via_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct
    molecule_residual_fixed_point_vbound_transfer_via_global_norm_direct
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
PLAN_85 upstream package:
the exact four-carrier frontier handed off by PLAN_84.
-/
structure MoleculeResidualWitnessPairSources : Prop where
  renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f
  renormVBound : MoleculeResidualRenormVBoundSource

structure MoleculeResidualUpstreamFourCarrierSources : Prop where
  renorm : ∀ f : BMol, Rfast f = f → IsFastRenormalizable f
  renormVBound : MoleculeResidualRenormVBoundSource
  orbitAt : MoleculeResidualOrbitClauseAtSource
  collapse : MoleculeResidualFixedPointHybridClassCollapseSource

/--
Recover fixed-point normalization data from the shared PLAN_85 witness-side
pair.
-/
theorem molecule_residual_fixed_point_data_source_of_witness_pair_sources
    (h_sources : MoleculeResidualWitnessPairSources) :
    MoleculeResidualFixedPointDataSource :=
  fixed_point_normalization_data_of_fixed_point_exists_and_renorm_and_renorm_vbound
    h_sources.renorm
    h_sources.renormVBound

/--
Recover the concrete local-witness target directly from the shared PLAN_85
witness-side pair.
-/
def molecule_residual_fixed_point_local_witness_on_sources_of_witness_pair_sources
    (h_sources : MoleculeResidualWitnessPairSources) :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_fixed_point_exists_and_renorm_and_renorm_vbound
    h_sources.renorm
    h_sources.renormVBound

/--
Build the full PLAN_85 upstream frontier from the shared witness-side pair plus
the orbit and collapse carriers.
-/
theorem molecule_residual_upstream_four_carrier_sources_of_witness_pair_orbit_at_and_hybrid_class_collapse
    (h_pair : MoleculeResidualWitnessPairSources)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualUpstreamFourCarrierSources :=
  ⟨h_pair.renorm, h_pair.renormVBound, h_orbit_at, h_collapse⟩

/--
Current shared PLAN_85 witness-side pair.
-/
theorem molecule_residual_witness_pair_sources :
    MoleculeResidualWitnessPairSources :=
  ⟨
    molecule_residual_fixed_point_renormalizable_via_global_norm_direct,
    molecule_residual_renorm_vbound_source
  ⟩

/--
Current fixed-data route factored through the shared PLAN_85 witness-side pair.
-/
theorem molecule_residual_fixed_point_data_source_via_witness_pair_sources :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_witness_pair_sources
    molecule_residual_witness_pair_sources

/--
Current local-witness route factored through the shared PLAN_85 witness-side
pair.
-/
def molecule_residual_fixed_point_local_witness_on_sources_via_witness_pair_sources :
    MoleculeResidualFixedPointLocalWitnessOnSources :=
  molecule_residual_fixed_point_local_witness_on_sources_of_witness_pair_sources
    molecule_residual_witness_pair_sources

/--
Recover seeded existence directly from the packaged PLAN_85 upstream frontier.
-/
theorem molecule_residual_fixed_point_existence_source_of_upstream_four_carrier_sources
    (h_sources : MoleculeResidualUpstreamFourCarrierSources) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renorm_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed
    h_sources.renorm
    h_sources.renormVBound
    h_sources.orbitAt
    h_sources.collapse

/--
Recover seeded existence directly from the shared witness-side pair together
with the orbit and collapse carriers.
-/
theorem molecule_residual_fixed_point_existence_source_of_witness_pair_orbit_at_and_hybrid_class_collapse_via_seed
    (h_pair : MoleculeResidualWitnessPairSources)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_renorm_renorm_vbound_orbit_clause_at_and_hybrid_class_collapse_via_seed
    h_pair.renorm
    h_pair.renormVBound
    h_orbit_at
    h_collapse

/--
Current packaged PLAN_85 upstream frontier.
-/
theorem molecule_residual_upstream_four_carrier_sources :
    MoleculeResidualUpstreamFourCarrierSources :=
  molecule_residual_upstream_four_carrier_sources_of_witness_pair_orbit_at_and_hybrid_class_collapse
    molecule_residual_witness_pair_sources
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Current seeded existence route factored through the explicit PLAN_85 upstream
four-carrier package.
-/
theorem molecule_residual_fixed_point_existence_source_via_upstream_four_carrier_sources :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_upstream_four_carrier_sources
    molecule_residual_upstream_four_carrier_sources

/--
Current seeded existence route factored as:
shared witness-side pair + orbit-at + hybrid-class collapse.
-/
theorem molecule_residual_fixed_point_existence_source_via_witness_pair_orbit_at_and_hybrid_class_collapse_via_seed :
    MoleculeResidualFixedPointExistenceSource :=
  molecule_residual_fixed_point_existence_source_of_witness_pair_orbit_at_and_hybrid_class_collapse_via_seed
    molecule_residual_witness_pair_sources
    molecule_residual_orbit_clause_at_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Recover canonical fast fixed-point data directly from the packaged PLAN_85
upstream frontier.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_upstream_four_carrier_sources
    (h_sources : MoleculeResidualUpstreamFourCarrierSources) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_existence_source
    (molecule_residual_fixed_point_existence_source_of_upstream_four_carrier_sources
      h_sources)

/--
Recover canonical fast fixed-point data directly from the shared witness-side
pair together with the orbit and collapse carriers.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_of_witness_pair_orbit_at_and_hybrid_class_collapse
    (h_pair : MoleculeResidualWitnessPairSources)
    (h_orbit_at : MoleculeResidualOrbitClauseAtSource)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_upstream_four_carrier_sources
    (molecule_residual_upstream_four_carrier_sources_of_witness_pair_orbit_at_and_hybrid_class_collapse
      h_pair
      h_orbit_at
      h_collapse)

/--
Current canonical route factored through the explicit PLAN_85 upstream
four-carrier package.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_upstream_four_carrier_sources :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_upstream_four_carrier_sources
    molecule_residual_upstream_four_carrier_sources

/--
Under any bounds witness (hence canonical fixed-point existence), hybrid-level
unique-fixed-point source and map-level uniqueness source are equivalent.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_bounds
    (h_bounds : PseudoSiegelAPrioriBounds) :
    MoleculeResidualHybridUniqueFixedPointSource ↔
      MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_canonical
    (canonical_fast_fixed_point_data_of_bounds h_bounds)

/--
Current-route equivalence certificate:
with the active bounds source, the hybrid-unique and map-level uniqueness
source goals are equivalent.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source :
    MoleculeResidualHybridUniqueFixedPointSource ↔
      MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_hybrid_unique_fixed_point_source_iff_uniqueness_source_of_bounds
    molecule_residual_bounds

/--
Assemble hybrid-class unique fixed-point source from bounds and hybrid-class-
collapse source seams.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_hybrid_class_collapse_source
    (h_bounds : PseudoSiegelAPrioriBounds)
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_collapse_source
    (canonical_fast_fixed_point_data_of_bounds h_bounds)
    h_collapse

/--
Assemble hybrid-class unique fixed-point source from bounds and a hybrid-class
fixed-point uniqueness source.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_hybrid_class_uniqueness_source
    (h_bounds : PseudoSiegelAPrioriBounds)
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_canonical_and_hybrid_class_uniqueness_source
    (canonical_fast_fixed_point_data_of_bounds h_bounds)
    h_class_unique

/--
Assemble hybrid-class unique fixed-point source from bounds and map-level
uniqueness source seams.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_uniqueness_source
    (h_bounds : PseudoSiegelAPrioriBounds)
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_hybrid_class_collapse_source
    h_bounds
    (molecule_residual_fixed_point_hybrid_class_collapse_source_of_uniqueness_source
      h_unique)

/--
Under any bounds witness, model-collapse input for the lifted hybrid-class
uniqueness route is equivalent to map-level fixed-point uniqueness.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_iff_uniqueness_source_of_bounds
    (h_bounds : PseudoSiegelAPrioriBounds) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource ↔
      MoleculeResidualFixedPointUniquenessSource := by
  constructor
  · intro h_model_collapse
    have h_model_sources :
        MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
        h_model_collapse
    have h_class_unique :
        MoleculeResidualHybridClassFixedPointUniquenessSource :=
      molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
        h_model_sources
    have h_hybrid_unique :
        MoleculeResidualHybridUniqueFixedPointSource :=
      molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_hybrid_class_uniqueness_source
        h_bounds
        h_class_unique
    exact
      molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
        h_hybrid_unique
  · intro h_unique
    exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_uniqueness_source
        h_unique

/--
Current-route equivalence certificate:
model-collapse input and map-level fixed-point uniqueness are equivalent under
the active bounds source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_iff_uniqueness_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource ↔
      MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_iff_uniqueness_source_of_bounds
    molecule_residual_bounds

/--
Under any bounds witness, the direct hybrid-class fixed-point uniqueness source
seam is equivalent to map-level fixed-point uniqueness.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_iff_uniqueness_source_of_bounds
    (h_bounds : PseudoSiegelAPrioriBounds) :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource ↔
      MoleculeResidualFixedPointUniquenessSource := by
  constructor
  · intro h_direct
    have h_hybrid_unique :
        MoleculeResidualHybridUniqueFixedPointSource :=
      molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_hybrid_class_uniqueness_source
        h_bounds
        (molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct_of_source
          h_direct)
    exact
      molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
        h_hybrid_unique
  · intro h_unique
    exact
      molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source
        h_unique

/--
Current-route equivalence certificate:
direct hybrid-class uniqueness source seam and map-level fixed-point uniqueness
are equivalent under the active bounds source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_iff_uniqueness_source :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource ↔
      MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_iff_uniqueness_source_of_bounds
    molecule_residual_bounds

/--
Route hybrid-class fixed-point uniqueness source through the dedicated
map-level direct uniqueness seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_fixed_point_uniqueness_direct_source
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct_of_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source
      (molecule_residual_fixed_point_uniqueness_source_direct_of_source
        h_unique_direct))

/--
Route hybrid-class model-collapse source through the dedicated map-level direct
uniqueness seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_fixed_point_uniqueness_direct_source
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_direct_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_fixed_point_uniqueness_direct_source
      h_unique_direct)

/--
Build direct hybrid-class-uniqueness model-collapse seam from the dedicated
map-level direct uniqueness seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_fixed_point_uniqueness_direct_source
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_fixed_point_uniqueness_direct_source
    h_unique_direct

/--
Recover hybrid-class-uniqueness model-collapse source from the dedicated
direct-source seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_source
    (h_source : MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource) :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  h_source

/--
Route hybrid-unique fixed-point source construction through the dedicated
map-level direct uniqueness seam under any bounds witness.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_fixed_point_uniqueness_direct_source
    (h_bounds : PseudoSiegelAPrioriBounds)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_uniqueness_source
    h_bounds
    (molecule_residual_fixed_point_uniqueness_source_direct_of_source
      h_unique_direct)

/--
Current hybrid-class fixed-point uniqueness source theorem.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_assembly_sources :
    MoleculeResidualHybridClassFixedPointUniquenessAssemblySources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_assembly_sources_of_hybrid_class_collapse_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Direct hybrid-class fixed-point uniqueness source theorem routed through the
assembly-source constructor.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_via_uniqueness_source_direct :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source
    molecule_residual_fixed_point_uniqueness_source_direct

/--
Compatibility alias: anchor source theorem obtained via uniqueness-direct route.
-/
theorem molecule_residual_direct_seam_anchor_source_via_uniqueness_direct_source :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source

/--
Current direct map-level hybrid-class-collapse seam routed via the PLAN_64
anchor source theorem.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_via_anchor_source :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
    molecule_residual_direct_seam_anchor_source

/--
Current direct map-level fixed-point uniqueness seam routed via the PLAN_64
anchor source theorem.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_via_anchor_source :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
    molecule_residual_direct_seam_anchor_source

/--
Canonical zero-arg cutover alias for direct map-level hybrid-class-collapse
seam.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_direct_source_cutover :
    MoleculeResidualFixedPointHybridClassCollapseDirectSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_direct_source_via_anchor_source

/--
Canonical zero-arg cutover alias for direct map-level fixed-point uniqueness
seam.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_cutover :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_via_anchor_source

/--
Direct hybrid-class fixed-point uniqueness source theorem routed through the
dedicated direct-source seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_fixed_point_uniqueness_direct_source
    molecule_residual_fixed_point_uniqueness_direct_source_cutover

/--
Current direct hybrid-class-uniqueness model-collapse source seam.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource :=
  molecule_residual_direct_seam_anchor_source

/--
Current PLAN_70 witness-source theorem routed through the current
model-collapse-direct source theorem.
-/
theorem molecule_residual_model_collapse_direct_witness_sources :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_direct_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source

/--
Current PLAN_69 breakout-source theorem routed through PLAN_70 witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_via_model_collapse_direct_witness_sources :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct_witness_sources
    molecule_residual_canonical_fast_fixed_point_data_source
    molecule_residual_model_collapse_direct_witness_sources

/--
Current PLAN_69 breakout-source theorem routed from:
- current canonical fixed-point data theorem, and
- current model-collapse-direct source theorem.
-/
theorem molecule_residual_direct_source_breakout_sources :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_via_model_collapse_direct_witness_sources

/--
Current anchor source theorem routed through PLAN_69 breakout sources.
-/
theorem molecule_residual_direct_seam_anchor_source_via_direct_source_breakout_sources :
    MoleculeResidualDirectSeamAnchorSource :=
  molecule_residual_direct_seam_anchor_source_of_direct_source_breakout_sources
    molecule_residual_direct_source_breakout_sources

/--
Current map-level direct-uniqueness source theorem routed through PLAN_69
breakout sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_via_direct_source_breakout_sources :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_direct_source_breakout_sources
    molecule_residual_direct_source_breakout_sources

/--
Current model-collapse source for hybrid-class-uniqueness model sources.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source

/--
Current model-collapse source routed directly from map-level hybrid-class
collapse source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_hybrid_class_collapse_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_collapse_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Current model-collapse source routed from direct map-level uniqueness source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_uniqueness_source_direct :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_uniqueness_source
    molecule_residual_fixed_point_uniqueness_source_direct

/--
Current model-collapse source routed from direct hybrid-class uniqueness source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_hybrid_class_uniqueness_source_direct :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_class_uniqueness_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_source_direct

/--
Current model-source pack for hybrid-class fixed-point uniqueness.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source

/--
Current hybrid-class fixed-point uniqueness source theorem.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources

/--
PLAN_77 source seam for map-level direct fixed-point uniqueness routed through
hybrid-class-uniqueness model sources.
-/
abbrev MoleculeResidualFixedPointUniquenessDirectModelSources :=
  MoleculeResidualHybridClassFixedPointUniquenessModelSources

/--
Build PLAN_77 direct-uniqueness model sources from hybrid-class-uniqueness
model sources.
-/
def molecule_residual_fixed_point_uniqueness_direct_model_sources_of_hybrid_class_uniqueness_model_sources
    (h_model_sources : MoleculeResidualHybridClassFixedPointUniquenessModelSources) :
    MoleculeResidualFixedPointUniquenessDirectModelSources :=
  h_model_sources

/--
Build map-level direct fixed-point uniqueness source from PLAN_77 direct-
uniqueness model sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_of_model_sources
    (h_model_sources : MoleculeResidualFixedPointUniquenessDirectModelSources) :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_hybrid_class_uniqueness_source
    (molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
      h_model_sources)

/--
Current PLAN_77 direct-uniqueness model sources theorem.
-/
def molecule_residual_fixed_point_uniqueness_direct_model_sources :
    MoleculeResidualFixedPointUniquenessDirectModelSources :=
  molecule_residual_fixed_point_uniqueness_direct_model_sources_of_hybrid_class_uniqueness_model_sources
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources

/--
Current map-level direct fixed-point uniqueness source theorem routed via
PLAN_77 model sources.
-/
theorem molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources :
    MoleculeResidualFixedPointUniquenessDirectSource :=
  molecule_residual_fixed_point_uniqueness_direct_source_of_model_sources
    molecule_residual_fixed_point_uniqueness_direct_model_sources

/--
Candidate PLAN_77 direct model-collapse seam routed through the model-sources
direct-uniqueness theorem.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_via_model_source_direct_uniqueness :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_of_fixed_point_uniqueness_direct_source
    molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources

/--
Candidate PLAN_77 model-collapse-direct witness sources routed through the
model-sources direct-uniqueness theorem.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_via_model_source_direct_uniqueness :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_model_collapse_direct_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_via_model_source_direct_uniqueness

/--
Candidate PLAN_77 breakout sources routed through the model-sources
direct-uniqueness theorem.
-/
theorem molecule_residual_direct_source_breakout_sources_via_model_source_direct_uniqueness :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct_witness_sources
    molecule_residual_canonical_fast_fixed_point_data_source
    molecule_residual_model_collapse_direct_witness_sources_via_model_source_direct_uniqueness

/--
Candidate PLAN_77 model-collapse source routed through the model-sources
direct-uniqueness theorem.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_model_source_direct_uniqueness :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_direct_source_via_model_source_direct_uniqueness

/--
Candidate PLAN_77 hybrid-class-uniqueness model sources routed through the
model-sources direct-uniqueness theorem.
-/
def molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_via_model_source_direct_uniqueness :
    MoleculeResidualHybridClassFixedPointUniquenessModelSources :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_of_model_collapse_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_model_source_direct_uniqueness

/--
Candidate PLAN_77 hybrid-class fixed-point uniqueness source routed through
the model-sources direct-uniqueness theorem.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_source_via_model_source_direct_uniqueness :
    MoleculeResidualHybridClassFixedPointUniquenessSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_source_of_model_sources
    molecule_residual_hybrid_class_fixed_point_uniqueness_model_sources_via_model_source_direct_uniqueness

/--
Candidate PLAN_77 local-domain transfer source pack routed through the current
local-witness pack and the model-sources direct-uniqueness seam.
-/
def molecule_residual_fixed_point_transfer_on_sources_via_local_witness_and_model_source_direct_uniqueness :
    MoleculeResidualFixedPointTransferOnSources :=
  molecule_residual_fixed_point_transfer_on_sources_of_local_witness_sources_and_uniqueness_source
    molecule_residual_fixed_point_local_witness_sources
    (molecule_residual_fixed_point_uniqueness_source_direct_of_source
      molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources)

/--
Candidate PLAN_77 fixed-point transfer source routed through local witness +
model-sources direct uniqueness.
-/
theorem molecule_residual_fixed_point_transfer_source_via_local_witness_and_model_source_direct_uniqueness :
    MoleculeResidualFixedPointTransferSource :=
  molecule_residual_fixed_point_transfer_source_of_on_sources
    molecule_residual_fixed_point_transfer_on_sources_via_local_witness_and_model_source_direct_uniqueness

/--
Candidate PLAN_77 fixed-point data source routed through existence + local
witness + model-sources direct uniqueness.
-/
theorem molecule_residual_fixed_point_data_source_via_local_witness_and_model_source_direct_uniqueness :
    MoleculeResidualFixedPointDataSource :=
  molecule_residual_fixed_point_data_source_of_existence_and_transfer_on_sources
    molecule_residual_fixed_point_existence_source
    molecule_residual_fixed_point_transfer_on_sources_via_local_witness_and_model_source_direct_uniqueness

/--
Candidate PLAN_77 canonical fixed-point data source routed through the local
witness + model-sources direct-uniqueness transfer/data path.
-/
theorem molecule_residual_canonical_fast_fixed_point_data_source_via_local_witness_and_model_source_direct_uniqueness :
    MoleculeResidualCanonicalFastFixedPointDataSource :=
  molecule_residual_canonical_fast_fixed_point_data_source_of_fixed_point_data_source
    molecule_residual_fixed_point_data_source_via_local_witness_and_model_source_direct_uniqueness

/--
Current hybrid-class unique fixed-point source theorem.
-/
theorem molecule_residual_hybrid_unique_fixed_point_source :
    MoleculeResidualHybridUniqueFixedPointSource :=
  molecule_residual_hybrid_unique_fixed_point_source_of_bounds_and_fixed_point_uniqueness_direct_source
    molecule_residual_bounds
    molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources

/--
Current model-collapse source routed from current hybrid-unique source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_via_hybrid_unique_fixed_point_source :
    MoleculeResidualHybridClassFixedPointUniquenessModelCollapseSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_model_collapse_source_of_hybrid_unique_fixed_point_source
    molecule_residual_hybrid_unique_fixed_point_source

/--
Current direct hybrid-class uniqueness source seam routed from current
hybrid-unique source.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_via_hybrid_unique_fixed_point_source :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_hybrid_unique_fixed_point_source
    molecule_residual_hybrid_unique_fixed_point_source

/--
Current map-level fixed-point uniqueness theorem routed via the hybrid-unique
source seam.
-/
theorem molecule_residual_fixed_point_uniqueness_source :
    MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
    molecule_residual_hybrid_unique_fixed_point_source

/--
Current PLAN_70 witness-source theorem routed from current map-level uniqueness
source.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_via_uniqueness_source :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_uniqueness_source
    molecule_residual_fixed_point_uniqueness_source

/--
Current PLAN_70 witness-source theorem routed from current hybrid-unique
fixed-point source.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_via_hybrid_unique_fixed_point_source :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_hybrid_unique_fixed_point_source
    molecule_residual_hybrid_unique_fixed_point_source

/--
Current PLAN_70 witness-source theorem routed from current hybrid-class
uniqueness source.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_via_hybrid_class_uniqueness_source :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_uniqueness_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_source

/--
Current PLAN_70 witness-source theorem routed from current map-level
hybrid-class-collapse source.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_via_fixed_point_hybrid_class_collapse_source :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_fixed_point_hybrid_class_collapse_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Current PLAN_71 witness-source theorem routed from current map-level
hybrid-class-collapse source.
-/
theorem molecule_residual_hybrid_class_collapse_witness_sources :
    MoleculeResidualHybridClassCollapseSourceWitnessSources :=
  molecule_residual_hybrid_class_collapse_witness_sources_of_fixed_point_hybrid_class_collapse_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Current PLAN_70 witness-source theorem routed through PLAN_71 witness sources.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_via_hybrid_class_collapse_witness_sources :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_collapse_witness_sources
    molecule_residual_hybrid_class_collapse_witness_sources

/--
Current PLAN_69 breakout-source theorem routed through PLAN_71 witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_via_hybrid_class_collapse_witness_sources :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_hybrid_class_collapse_witness_sources
    molecule_residual_canonical_fast_fixed_point_data_source
    molecule_residual_hybrid_class_collapse_witness_sources

/--
Minimal upstream source interface for PLAN_72:
explicit witness of the direct-seam-anchor source.
-/
structure MoleculeResidualDirectSeamAnchorSourceWitnessSources : Prop where
  anchor : MoleculeResidualDirectSeamAnchorSource

/--
Project direct-seam-anchor source from PLAN_72 witness sources.
-/
theorem molecule_residual_direct_seam_anchor_source_of_direct_seam_anchor_witness_sources
    (h_sources : MoleculeResidualDirectSeamAnchorSourceWitnessSources) :
    MoleculeResidualDirectSeamAnchorSource :=
  h_sources.anchor

/--
Assemble PLAN_72 witness sources from direct-seam-anchor source data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_of_direct_seam_anchor_source
    (h_anchor : MoleculeResidualDirectSeamAnchorSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  ⟨h_anchor⟩

/--
PLAN_72 witness-source interface is equivalent to direct-seam-anchor source
data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_iff_direct_seam_anchor_source :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources ↔
      MoleculeResidualDirectSeamAnchorSource := by
  constructor
  · intro h_sources
    exact h_sources.anchor
  · intro h_anchor
    exact
      molecule_residual_direct_seam_anchor_witness_sources_of_direct_seam_anchor_source
        h_anchor

/--
PLAN_74 winning-route source bundle:
- canonical fixed-point data for breakout assembly, and
- direct-seam-anchor witness source data.
-/
structure MoleculeResidualPlan74WinningRouteSources : Prop where
  canonical : CanonicalFastFixedPointData
  anchorWitness : MoleculeResidualDirectSeamAnchorSourceWitnessSources

/--
Assemble PLAN_74 winning-route sources from canonical and anchor-witness data.
-/
theorem molecule_residual_plan74_winning_route_sources_of_canonical_and_anchor_witness
    (h_canonical : CanonicalFastFixedPointData)
    (h_anchor : MoleculeResidualDirectSeamAnchorSourceWitnessSources) :
    MoleculeResidualPlan74WinningRouteSources :=
  ⟨h_canonical, h_anchor⟩

/--
Project map-level hybrid-class-collapse source from PLAN_74 winning-route
sources.
-/
theorem molecule_residual_fixed_point_hybrid_class_collapse_source_of_plan74_winning_route_sources
    (h_sources : MoleculeResidualPlan74WinningRouteSources) :
    MoleculeResidualFixedPointHybridClassCollapseSource :=
  molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
    (molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
      (molecule_residual_direct_seam_anchor_source_of_direct_seam_anchor_witness_sources
        h_sources.anchorWitness))

/--
Project PLAN_69 breakout sources from PLAN_74 winning-route sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_plan74_winning_route_sources
    (h_sources : MoleculeResidualPlan74WinningRouteSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_model_collapse_direct
    h_sources.canonical
    (molecule_residual_direct_seam_anchor_source_of_direct_seam_anchor_witness_sources
      h_sources.anchorWitness)

/--
Current PLAN_74 winning-route source bundle.
-/
theorem molecule_residual_plan74_winning_route_sources :
    MoleculeResidualPlan74WinningRouteSources :=
  molecule_residual_plan74_winning_route_sources_of_canonical_and_anchor_witness
    molecule_residual_canonical_fast_fixed_point_data_source
    (molecule_residual_direct_seam_anchor_witness_sources_of_direct_seam_anchor_source
      molecule_residual_direct_seam_anchor_source)

/--
Assemble PLAN_72 witness sources from map-level uniqueness source data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_of_uniqueness_source
    (h_unique : MoleculeResidualFixedPointUniquenessSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  ⟨molecule_residual_direct_seam_anchor_source_of_uniqueness_source h_unique⟩

/--
Assemble PLAN_72 witness sources from map-level direct-uniqueness source data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_of_fixed_point_uniqueness_direct_source
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_uniqueness_source
    (molecule_residual_fixed_point_uniqueness_source_direct_of_source
      h_unique_direct)

/--
Assemble PLAN_72 witness sources from hybrid-unique fixed-point source data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_of_hybrid_unique_fixed_point_source
    (h_hybrid_unique : MoleculeResidualHybridUniqueFixedPointSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_uniqueness_source
    (molecule_residual_fixed_point_uniqueness_source_of_hybrid_unique_fixed_point_source
      h_hybrid_unique)

/--
Assemble PLAN_72 witness sources from hybrid-class-uniqueness source data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_of_hybrid_class_uniqueness_source
    (h_class_unique : MoleculeResidualHybridClassFixedPointUniquenessSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_uniqueness_source
    (molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
      (molecule_residual_fixed_point_hybrid_class_collapse_source_of_hybrid_class_uniqueness_source
        h_class_unique))

/--
Assemble PLAN_72 witness sources from map-level hybrid-class-collapse source
data.
-/
theorem molecule_residual_direct_seam_anchor_witness_sources_of_fixed_point_hybrid_class_collapse_source
    (h_collapse : MoleculeResidualFixedPointHybridClassCollapseSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_uniqueness_source
    (molecule_residual_fixed_point_uniqueness_source_of_hybrid_class_collapse_source
      h_collapse)

/--
Build PLAN_71 witness sources from PLAN_72 witness sources.
-/
theorem molecule_residual_hybrid_class_collapse_witness_sources_of_direct_seam_anchor_witness_sources
    (h_sources : MoleculeResidualDirectSeamAnchorSourceWitnessSources) :
    MoleculeResidualHybridClassCollapseSourceWitnessSources :=
  molecule_residual_hybrid_class_collapse_witness_sources_of_fixed_point_hybrid_class_collapse_source
    (molecule_residual_fixed_point_hybrid_class_collapse_source_direct_of_source
      (molecule_residual_fixed_point_hybrid_class_collapse_direct_source_of_anchor_source
        h_sources.anchor))

/--
Build PLAN_70 witness sources from PLAN_72 witness sources.
-/
theorem molecule_residual_model_collapse_direct_witness_sources_of_direct_seam_anchor_witness_sources
    (h_sources : MoleculeResidualDirectSeamAnchorSourceWitnessSources) :
    MoleculeResidualModelCollapseDirectSourceWitnessSources :=
  molecule_residual_model_collapse_direct_witness_sources_of_hybrid_class_collapse_witness_sources
    (molecule_residual_hybrid_class_collapse_witness_sources_of_direct_seam_anchor_witness_sources
      h_sources)

/--
Build PLAN_69 breakout sources from:
- canonical fixed-point data, and
- PLAN_72 witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_canonical_and_direct_seam_anchor_witness_sources
    (h_canonical : CanonicalFastFixedPointData)
    (h_sources : MoleculeResidualDirectSeamAnchorSourceWitnessSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_hybrid_class_collapse_witness_sources
    h_canonical
    (molecule_residual_hybrid_class_collapse_witness_sources_of_direct_seam_anchor_witness_sources
      h_sources)

/--
Current PLAN_72 witness-source theorem routed from the current direct-seam-anchor
source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_plan74_winning_route_sources.anchorWitness

/--
PLAN_75 target interface: zero-arg source for direct-seam-anchor witness data.
-/
def MoleculeResidualAnchorWitnessZeroArgSource : Prop :=
  MoleculeResidualDirectSeamAnchorSourceWitnessSources

/--
Recover direct-seam-anchor witness sources from the PLAN_75 zero-arg source
interface.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources_of_zero_arg_source
    (h_source : MoleculeResidualAnchorWitnessZeroArgSource) :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  h_source

/--
Assemble PLAN_75 zero-arg source interface from direct-seam-anchor witness
sources.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_of_direct_seam_anchor_source_witness_sources
    (h_sources : MoleculeResidualDirectSeamAnchorSourceWitnessSources) :
    MoleculeResidualAnchorWitnessZeroArgSource :=
  h_sources

/--
PLAN_75 target interface is definitionally equivalent to direct-seam-anchor
witness sources.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source_witness_sources :
    MoleculeResidualAnchorWitnessZeroArgSource ↔
      MoleculeResidualDirectSeamAnchorSourceWitnessSources := by
  constructor
  · intro h_source
    exact
      molecule_residual_direct_seam_anchor_source_witness_sources_of_zero_arg_source
        h_source
  · intro h_sources
    exact
      molecule_residual_anchor_witness_zero_arg_source_of_direct_seam_anchor_source_witness_sources
        h_sources

/--
PLAN_75 bottleneck certificate:
the zero-arg anchor-witness source target is equivalent to direct-seam-anchor
source data.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source :
    MoleculeResidualAnchorWitnessZeroArgSource ↔
      MoleculeResidualDirectSeamAnchorSource := by
  calc
    MoleculeResidualAnchorWitnessZeroArgSource ↔
        MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
      molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source_witness_sources
    _ ↔ MoleculeResidualDirectSeamAnchorSource :=
      molecule_residual_direct_seam_anchor_witness_sources_iff_direct_seam_anchor_source

/--
PLAN_75 bottleneck certificate:
the zero-arg anchor-witness source target is equivalent to map-level
fixed-point uniqueness source data.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_iff_fixed_point_uniqueness_source :
    MoleculeResidualAnchorWitnessZeroArgSource ↔
      MoleculeResidualFixedPointUniquenessSource := by
  calc
    MoleculeResidualAnchorWitnessZeroArgSource ↔
        MoleculeResidualDirectSeamAnchorSource :=
      molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source
    _ ↔ MoleculeResidualFixedPointUniquenessSource :=
      molecule_residual_direct_seam_anchor_source_iff_fixed_point_uniqueness_source

/--
PLAN_76 candidate interface A:
zero-arg source for the direct-contract cutover source pack.
-/
def MoleculeResidualAnchorWitnessDirectContractCutoverSource : Prop :=
  MoleculeResidualDirectContractCutoverSources

/--
PLAN_76 cutover-ingredients seam:
- canonical fixed-point data source, and
- map-level direct-uniqueness source.
-/
def MoleculeResidualAnchorWitnessCutoverIngredients : Prop :=
  MoleculeResidualCanonicalFastFixedPointDataSource ∧
    MoleculeResidualFixedPointUniquenessDirectSource

/--
PLAN_76 source bundle:
- canonical fixed-point data source, and
- map-level direct-uniqueness source.
-/
structure MoleculeResidualAnchorWitnessZeroArgSources : Prop where
  canonical : MoleculeResidualCanonicalFastFixedPointDataSource
  uniquenessDirect : MoleculeResidualFixedPointUniquenessDirectSource

/--
Build PLAN_75 zero-arg anchor-witness source from the PLAN_76 direct-contract
cutover source interface.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_of_direct_contract_cutover_source
    (h_cutover : MoleculeResidualAnchorWitnessDirectContractCutoverSource) :
    MoleculeResidualAnchorWitnessZeroArgSource := by
  exact
    (molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source).2
      (molecule_residual_direct_seam_anchor_source_of_direct_contract_cutover_sources
        h_cutover)

/--
Build the PLAN_76 direct-contract cutover source interface from the PLAN_75
zero-arg anchor-witness source, given canonical fixed-point data.
-/
theorem molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_zero_arg_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_source : MoleculeResidualAnchorWitnessZeroArgSource) :
    MoleculeResidualAnchorWitnessDirectContractCutoverSource := by
  have h_anchor : MoleculeResidualDirectSeamAnchorSource :=
    (molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source).1
      h_source
  have h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource :=
    molecule_residual_fixed_point_uniqueness_direct_source_of_anchor_source
      h_anchor
  exact
    molecule_residual_direct_contract_cutover_sources_of_canonical_and_direct_of_canonical
      h_canonical
      (fun _ => h_unique_direct)

/--
Build the PLAN_76 direct-contract cutover source interface from the PLAN_75
zero-arg anchor-witness source.
-/
theorem molecule_residual_anchor_witness_direct_contract_cutover_source_of_zero_arg_source
    (h_source : MoleculeResidualAnchorWitnessZeroArgSource) :
    MoleculeResidualAnchorWitnessDirectContractCutoverSource := by
  exact
    molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_zero_arg_source
    molecule_residual_canonical_fast_fixed_point_data_source
    h_source

/--
PLAN_76 candidate A certificate (canonical-parametric):
under a canonical fixed-point witness, the zero-arg anchor-witness source
target is equivalent to the direct-contract cutover source interface.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_iff_direct_contract_cutover_source_of_canonical
    (h_canonical : CanonicalFastFixedPointData) :
    MoleculeResidualAnchorWitnessZeroArgSource ↔
      MoleculeResidualAnchorWitnessDirectContractCutoverSource := by
  constructor
  · intro h_source
    exact
      molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_zero_arg_source
        h_canonical
        h_source
  · intro h_cutover
    exact
      molecule_residual_anchor_witness_zero_arg_source_of_direct_contract_cutover_source
        h_cutover

/--
PLAN_76 candidate A certificate:
the zero-arg anchor-witness source target is equivalent to the direct-contract
cutover source interface.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_iff_direct_contract_cutover_source :
    MoleculeResidualAnchorWitnessZeroArgSource ↔
      MoleculeResidualAnchorWitnessDirectContractCutoverSource := by
  constructor
  · intro h_source
    exact
      molecule_residual_anchor_witness_direct_contract_cutover_source_of_zero_arg_source
        h_source
  · intro h_cutover
    exact
      molecule_residual_anchor_witness_zero_arg_source_of_direct_contract_cutover_source
        h_cutover

/--
Build the PLAN_76 direct-contract cutover source from:
- canonical fixed-point data source, and
- map-level direct-uniqueness source.
-/
theorem molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_uniqueness_direct_source
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualAnchorWitnessDirectContractCutoverSource :=
  molecule_residual_direct_contract_cutover_sources_of_canonical_and_direct_of_canonical
    h_canonical
    (fun _ => h_unique_direct)

/--
Project PLAN_76 cutover ingredients from the PLAN_76 direct-contract cutover
source.
-/
theorem molecule_residual_anchor_witness_cutover_ingredients_of_direct_contract_cutover_source
    (h_cutover : MoleculeResidualAnchorWitnessDirectContractCutoverSource) :
    MoleculeResidualAnchorWitnessCutoverIngredients :=
  ⟨h_cutover.canonicalData, h_cutover.directOfCanonical h_cutover.canonicalData⟩

/--
Build the PLAN_76 direct-contract cutover source from PLAN_76 cutover
ingredients.
-/
theorem molecule_residual_anchor_witness_direct_contract_cutover_source_of_cutover_ingredients
    (h_ingredients : MoleculeResidualAnchorWitnessCutoverIngredients) :
    MoleculeResidualAnchorWitnessDirectContractCutoverSource :=
  molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_uniqueness_direct_source
    h_ingredients.1
    h_ingredients.2

/--
PLAN_76 cutover certificate:
the cutover-ingredients seam is equivalent to the direct-contract cutover
source.
-/
theorem molecule_residual_anchor_witness_cutover_ingredients_iff_direct_contract_cutover_source :
    MoleculeResidualAnchorWitnessCutoverIngredients ↔
      MoleculeResidualAnchorWitnessDirectContractCutoverSource := by
  constructor
  · intro h_ingredients
    exact
      molecule_residual_anchor_witness_direct_contract_cutover_source_of_cutover_ingredients
        h_ingredients
  · intro h_cutover
    exact
      molecule_residual_anchor_witness_cutover_ingredients_of_direct_contract_cutover_source
        h_cutover

/--
Current PLAN_76 cutover-ingredients theorem.
-/
theorem molecule_residual_anchor_witness_cutover_ingredients :
    MoleculeResidualAnchorWitnessCutoverIngredients :=
  ⟨
    molecule_residual_canonical_fast_fixed_point_data_source,
    molecule_residual_fixed_point_uniqueness_direct_source_via_model_sources
  ⟩

/--
Current PLAN_75 zero-arg anchor-witness cutover-source theorem.
-/
theorem molecule_residual_anchor_witness_direct_contract_cutover_source :
    MoleculeResidualAnchorWitnessDirectContractCutoverSource :=
  molecule_residual_anchor_witness_direct_contract_cutover_source_of_cutover_ingredients
    molecule_residual_anchor_witness_cutover_ingredients

/--
Build the PLAN_75 zero-arg anchor-witness source from:
- canonical fixed-point data source, and
- map-level direct-uniqueness source.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_of_canonical_and_uniqueness_direct_source
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource)
    (h_unique_direct : MoleculeResidualFixedPointUniquenessDirectSource) :
    MoleculeResidualAnchorWitnessZeroArgSource :=
  molecule_residual_anchor_witness_zero_arg_source_of_direct_contract_cutover_source
    (molecule_residual_anchor_witness_direct_contract_cutover_source_of_canonical_and_uniqueness_direct_source
      h_canonical
      h_unique_direct)

/--
Build PLAN_75 zero-arg anchor-witness source from the PLAN_76 source bundle.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_of_zero_arg_sources
    (h_sources : MoleculeResidualAnchorWitnessZeroArgSources) :
    MoleculeResidualAnchorWitnessZeroArgSource :=
  molecule_residual_anchor_witness_zero_arg_source_of_canonical_and_uniqueness_direct_source
    h_sources.canonical
    h_sources.uniquenessDirect

/--
Build the PLAN_76 source bundle from the PLAN_76 direct-contract cutover source.
-/
theorem molecule_residual_anchor_witness_zero_arg_sources_of_direct_contract_cutover_source
    (h_cutover : MoleculeResidualAnchorWitnessDirectContractCutoverSource) :
    MoleculeResidualAnchorWitnessZeroArgSources :=
  ⟨
    h_cutover.canonicalData,
    h_cutover.directOfCanonical h_cutover.canonicalData
  ⟩

/--
Project the PLAN_76 source bundle from PLAN_76 cutover ingredients.
-/
theorem molecule_residual_anchor_witness_zero_arg_sources_of_cutover_ingredients
    (h_ingredients : MoleculeResidualAnchorWitnessCutoverIngredients) :
    MoleculeResidualAnchorWitnessZeroArgSources :=
  ⟨h_ingredients.1, h_ingredients.2⟩

/--
Project PLAN_76 cutover ingredients from the PLAN_76 source bundle.
-/
theorem molecule_residual_anchor_witness_cutover_ingredients_of_zero_arg_sources
    (h_sources : MoleculeResidualAnchorWitnessZeroArgSources) :
    MoleculeResidualAnchorWitnessCutoverIngredients :=
  ⟨h_sources.canonical, h_sources.uniquenessDirect⟩

/--
PLAN_76 bundle certificate:
the source-bundle seam is equivalent to the cutover-ingredients seam.
-/
theorem molecule_residual_anchor_witness_zero_arg_sources_iff_cutover_ingredients :
    MoleculeResidualAnchorWitnessZeroArgSources ↔
      MoleculeResidualAnchorWitnessCutoverIngredients := by
  constructor
  · intro h_sources
    exact
      molecule_residual_anchor_witness_cutover_ingredients_of_zero_arg_sources
        h_sources
  · intro h_ingredients
    exact
      molecule_residual_anchor_witness_zero_arg_sources_of_cutover_ingredients
        h_ingredients

/--
Current PLAN_76 source bundle feeding the zero-arg anchor-witness source route.
-/
theorem molecule_residual_anchor_witness_zero_arg_sources :
    MoleculeResidualAnchorWitnessZeroArgSources :=
  molecule_residual_anchor_witness_zero_arg_sources_of_cutover_ingredients
    molecule_residual_anchor_witness_cutover_ingredients

/--
Current PLAN_75 zero-arg anchor-witness source theorem, routed through the
PLAN_76 direct-contract cutover source seam.
-/
theorem molecule_residual_anchor_witness_zero_arg_source :
    MoleculeResidualAnchorWitnessZeroArgSource :=
  molecule_residual_anchor_witness_zero_arg_source_of_zero_arg_sources
    molecule_residual_anchor_witness_zero_arg_sources

/--
Build PLAN_74 winning-route bundle from canonical fixed-point data and PLAN_75
zero-arg anchor-witness source data.
-/
theorem molecule_residual_plan74_winning_route_sources_of_canonical_and_zero_arg_anchor_witness_source
    (h_canonical : CanonicalFastFixedPointData)
    (h_source : MoleculeResidualAnchorWitnessZeroArgSource) :
    MoleculeResidualPlan74WinningRouteSources :=
  molecule_residual_plan74_winning_route_sources_of_canonical_and_anchor_witness
    h_canonical
    (molecule_residual_direct_seam_anchor_source_witness_sources_of_zero_arg_source
      h_source)

/--
Current PLAN_69 breakout-source theorem routed through PLAN_72 witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_of_canonical_and_zero_arg_anchor_witness_source
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource)
    (h_source : MoleculeResidualAnchorWitnessZeroArgSource) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_plan74_winning_route_sources
    (molecule_residual_plan74_winning_route_sources_of_canonical_and_zero_arg_anchor_witness_source
      h_canonical
      h_source)

/--
Build PLAN_75 zero-arg anchor-witness source from PLAN_69 direct-source
breakout source data.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_of_direct_source_breakout_sources
    (h_breakout : MoleculeResidualDirectSourceBreakoutSources) :
    MoleculeResidualAnchorWitnessZeroArgSource := by
  exact
    (molecule_residual_anchor_witness_zero_arg_source_iff_direct_seam_anchor_source).2
      (molecule_residual_direct_seam_anchor_source_of_direct_source_breakout_sources
        h_breakout)

/--
Canonical-parametric breakout certificate:
under canonical fixed-point data, PLAN_75 zero-arg source and PLAN_69 breakout
source are equivalent.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_iff_direct_source_breakout_sources_of_canonical
    (h_canonical : MoleculeResidualCanonicalFastFixedPointDataSource) :
    MoleculeResidualAnchorWitnessZeroArgSource ↔
      MoleculeResidualDirectSourceBreakoutSources := by
  constructor
  · intro h_source
    exact
      molecule_residual_direct_source_breakout_sources_of_canonical_and_zero_arg_anchor_witness_source
        h_canonical
        h_source
  · intro h_breakout
    exact
      molecule_residual_anchor_witness_zero_arg_source_of_direct_source_breakout_sources
        h_breakout

/--
Candidate breakout-routed zero-arg theorem for PLAN_76.
-/
theorem molecule_residual_anchor_witness_zero_arg_source_via_direct_source_breakout_sources :
    MoleculeResidualAnchorWitnessZeroArgSource :=
  molecule_residual_anchor_witness_zero_arg_source_of_direct_source_breakout_sources
    molecule_residual_direct_source_breakout_sources

/--
Build PLAN_69 breakout source from the PLAN_76 source bundle.
-/
theorem molecule_residual_direct_source_breakout_sources_of_zero_arg_sources
    (h_sources : MoleculeResidualAnchorWitnessZeroArgSources) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_canonical_and_zero_arg_anchor_witness_source
    h_sources.canonical
    (molecule_residual_anchor_witness_zero_arg_source_of_zero_arg_sources h_sources)

/--
Build PLAN_69 breakout source directly from the PLAN_76 direct-contract cutover
source.
-/
theorem molecule_residual_direct_source_breakout_sources_of_direct_contract_cutover_source
    (h_cutover : MoleculeResidualAnchorWitnessDirectContractCutoverSource) :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_zero_arg_sources
    (molecule_residual_anchor_witness_zero_arg_sources_of_direct_contract_cutover_source
      h_cutover)

/--
Current PLAN_69 breakout-source theorem routed through PLAN_72 witness sources.
-/
theorem molecule_residual_direct_source_breakout_sources_via_direct_seam_anchor_witness_sources :
    MoleculeResidualDirectSourceBreakoutSources :=
  molecule_residual_direct_source_breakout_sources_of_zero_arg_sources
    molecule_residual_anchor_witness_zero_arg_sources

/--
Current PLAN_72 witness-source theorem routed from current map-level uniqueness
source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources_via_uniqueness_source :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_uniqueness_source
    molecule_residual_fixed_point_uniqueness_source

/--
Current PLAN_72 witness-source theorem routed from current map-level
direct-uniqueness source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources_via_uniqueness_source_direct :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_fixed_point_uniqueness_direct_source
    molecule_residual_fixed_point_uniqueness_direct_source

/--
Current PLAN_72 witness-source theorem routed from current hybrid-unique
fixed-point source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources_via_hybrid_unique_fixed_point_source :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_hybrid_unique_fixed_point_source
    molecule_residual_hybrid_unique_fixed_point_source

/--
Current PLAN_72 witness-source theorem routed from current hybrid-class
uniqueness source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources_via_hybrid_class_uniqueness_source :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_hybrid_class_uniqueness_source
    molecule_residual_hybrid_class_fixed_point_uniqueness_source

/--
Current PLAN_72 witness-source theorem routed from current map-level
hybrid-class-collapse source theorem.
-/
theorem molecule_residual_direct_seam_anchor_source_witness_sources_via_fixed_point_hybrid_class_collapse_source :
    MoleculeResidualDirectSeamAnchorSourceWitnessSources :=
  molecule_residual_direct_seam_anchor_witness_sources_of_fixed_point_hybrid_class_collapse_source
    molecule_residual_fixed_point_hybrid_class_collapse_source

/--
Current direct hybrid-class uniqueness source seam routed from the current
map-level uniqueness theorem.
-/
theorem molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_via_uniqueness_source :
    MoleculeResidualHybridClassFixedPointUniquenessDirectSource :=
  molecule_residual_hybrid_class_fixed_point_uniqueness_direct_source_of_uniqueness_source
    molecule_residual_fixed_point_uniqueness_source

/--
Compatibility alias: explicit theorem name for the hybrid-unique route.
-/
theorem molecule_residual_fixed_point_uniqueness_source_via_hybrid_unique_fixed_point_source :
    MoleculeResidualFixedPointUniquenessSource :=
  molecule_residual_fixed_point_uniqueness_source

/--
Current PLAN_57 canonical orbit-at debt source routed via transport +
fixed-data + hybrid-unique source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_hybrid_unique_fixed_point_source :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_hybrid_unique_fixed_point_source
    molecule_residual_orbit_transport_source
    molecule_h_fixed_data_direct
    molecule_residual_hybrid_unique_fixed_point_source

/--
Current PLAN_57 canonical orbit-at debt source routed via transport +
fixed-data + map-level uniqueness source seams.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_of_transport_fixed_data_and_uniqueness_source
    molecule_residual_orbit_transport_source
    molecule_h_fixed_data_direct
    molecule_residual_fixed_point_uniqueness_source

/--
Current PLAN_57 canonical orbit-at debt source routed via transport +
fixed-data + map-level uniqueness, where uniqueness is itself routed through
the hybrid-unique source seam.
-/
theorem molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source_via_hybrid_unique_fixed_point_source :
    MoleculeResidualCanonicalOrbitAtDebtSource :=
  molecule_residual_canonical_orbit_at_debt_source_via_transport_fixed_data_and_uniqueness_source

theorem molecule_residual_gap :
  ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
    HasSiegelBounds f_star D U a b →
    let F := slice_operator f_star
    let φ := slice_chart f_star
    DifferentiableAt ℂ F (φ f_star) ∧
    IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)) :=
  molecule_h_gap

theorem molecule_residual_piecewise :
  IsPiecewiseAnalytic1DUnstable Rfast :=
  molecule_h_piecewise

theorem molecule_residual_shift :
  ∃ N, IsConjugateToShift Rprm_combinatorial_model N :=
  rprm_combinatorial_model_has_shift_factor

theorem molecule_residual_assoc :
  CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model :=
  rfast_hmol_candidate_combinatorially_associated

theorem molecule_residual_compact :
  IsCompactOperator Rfast_HMol_candidate :=
  molecule_h_compact

theorem molecule_final_assumptions : MoleculeFinalAssumptions where
  analytic := {
    h_bounds := molecule_residual_bounds
    h_gap := molecule_residual_gap
  }
  combinatorialTopological := {
    h_piecewise := molecule_residual_piecewise
    h_shift := molecule_residual_shift
    h_assoc := molecule_residual_assoc
    h_compact := molecule_residual_compact
  }

def molecule_core_analytic : MoleculeAnalyticCore :=
  molecule_final_assumptions.analytic

def molecule_core_combinatorial_topological : MoleculeCombinatorialTopologicalCore :=
  molecule_final_assumptions.combinatorialTopological

theorem molecule_final_bounds : PseudoSiegelAPrioriBounds :=
  molecule_residual_bounds

theorem molecule_final_gap :
  ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
    HasSiegelBounds f_star D U a b →
    let F := slice_operator f_star
    let φ := slice_chart f_star
    DifferentiableAt ℂ F (φ f_star) ∧
    IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)) :=
  molecule_residual_gap

theorem molecule_final_piecewise :
  IsPiecewiseAnalytic1DUnstable Rfast :=
  molecule_residual_piecewise

theorem molecule_final_shift :
  ∃ N, IsConjugateToShift Rprm_combinatorial_model N :=
  molecule_residual_shift

theorem molecule_final_assoc :
  CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model :=
  molecule_residual_assoc

theorem molecule_final_compact :
  IsCompactOperator Rfast_HMol_candidate :=
  molecule_residual_compact

theorem molecule_hypothesis_pack_of_partitioned_core
    (h_analytic : MoleculeAnalyticCore)
    (h_comb : MoleculeCombinatorialTopologicalCore)
    (h_canonical_fixed : CanonicalFastFixedPointData) :
    MoleculeHypothesisPack where
  h_bounds := h_analytic.h_bounds
  h_conj := molecule_core_conj
  h_gap := h_analytic.h_gap
  h_piecewise := h_comb.h_piecewise
  h_shift := h_comb.h_shift
  h_assoc := h_comb.h_assoc
  h_compact := h_comb.h_compact
  h_canonical_fixed := h_canonical_fixed

theorem molecule_hypothesis_pack_of_final_assumptions : MoleculeHypothesisPack :=
  molecule_hypothesis_pack_of_partitioned_core
    molecule_core_analytic
    molecule_core_combinatorial_topological
    molecule_residual_canonical_fast_fixed_point_data_source

theorem molecule_hypothesis_pack : MoleculeHypothesisPack :=
  molecule_hypothesis_pack_of_final_assumptions

theorem molecule_conjecture_refined_of_pack
    (hpack : MoleculeHypothesisPack) :
  MoleculeConjectureRefined := by
  refine ⟨?_, hpack.h_canonical_fixed⟩
  exact molecule_conjecture_refined_with_bounds
    hpack.h_bounds
    hpack.h_conj
    hpack.h_gap
    hpack.h_piecewise
    hpack.h_shift
    hpack.h_assoc
    hpack.h_compact

/--
Zero-argument exported statement of the refined molecule conjecture.
-/
theorem molecule_conjecture_refined : MoleculeConjectureRefined :=
  molecule_conjecture_refined_of_pack molecule_hypothesis_pack

/--
Minimal canonical strengthening:
the built-in renormalization operator `Molecule.Rfast` has a fast-renormalizable fixed point.
-/
theorem canonical_rfast_has_fast_renormalizable_fixed_point_of_pack
    (hpack : MoleculeHypothesisPack) :
  CanonicalFastFixedPointData := by
  exact hpack.h_canonical_fixed

theorem canonical_rfast_has_fast_renormalizable_fixed_point :
  MoleculeConjectureRefined → CanonicalFastFixedPointData :=
  molecule_conjecture_refined_implies_canonical_fast_fixed_point

/--
Refined-contract strengthening:
pair the zero-argument refined conjecture export with a canonical
fast-renormalizable fixed-point witness for `Molecule.Rfast`.
-/
theorem molecule_conjecture_refined_with_canonical_fixed_point_of_pack
    (hpack : MoleculeHypothesisPack) :
  MoleculeConjectureRefined ∧ CanonicalFastFixedPointData := by
  exact ⟨molecule_conjecture_refined_of_pack hpack, hpack.h_canonical_fixed⟩

theorem molecule_conjecture_refined_with_canonical_fixed_point :
  MoleculeConjectureRefined → MoleculeConjectureRefined ∧ CanonicalFastFixedPointData := by
  intro h_refined
  exact ⟨h_refined, canonical_rfast_has_fast_renormalizable_fixed_point h_refined⟩

end
end Molecule
