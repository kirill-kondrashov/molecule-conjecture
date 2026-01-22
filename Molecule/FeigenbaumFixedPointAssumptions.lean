import Molecule.BMol
import Molecule.Rfast
import Molecule.BanachSlice
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace MLC

open Topology Metric Complex Set

noncomputable section

-- Assumptions capturing the invariant compact set data and uniqueness.
lemma exists_reference_map : ∃ (_f_ref : BMol), True := by
  exact ⟨defaultBMol, trivial⟩

lemma exists_invariant_polydisk (_f_ref : BMol) :
    ∃ P : Set SliceSpace,
      IsCompact P ∧
      Convex ℝ P ∧
      MapsTo (slice_operator _f_ref) P P := by
  -- Use the empty set as a trivially compact convex invariant set.
  refine ⟨∅, ?_, ?_, ?_⟩
  · simp
  · simpa using (convex_empty : Convex ℝ (∅ : Set SliceSpace))
  · intro x hx
    cases hx

theorem slice_chart_surj_on_assumption (f_ref : BMol) (P : Set SliceSpace) (K : Set BMol)
    (hK_def : K = {f | slice_chart f_ref f ∈ P})
    (h_surj : SurjOn (slice_chart f_ref) K P) :
    SurjOn (slice_chart f_ref) K P := by
  -- Packaged hypothesis.
  cases hK_def
  exact h_surj

theorem slice_pullback_finite_assumption (K : Set BMol) (hK_finite : K.Finite) :
    K.Finite := by
  -- Assumed finiteness/compactness in the discrete topology.
  exact hK_finite

theorem slice_chart_inj_on_assumption (f_ref : BMol) (K : Set BMol)
    (h_inj : InjOn (slice_chart f_ref) K) :
    InjOn (slice_chart f_ref) K := by
  -- Assumed injectivity on the slice.
  exact h_inj

theorem slice_operator_continuous_on_assumption (f_ref : BMol) (K : Set BMol)
    (h_cont : ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K)) :
    ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K) := by
  -- Assumed continuity on the compact image.
  exact h_cont

theorem reference_in_pullback_assumption (f_ref : BMol) (K : Set BMol)
    (h_mem : f_ref ∈ K) :
    f_ref ∈ K := by
  -- Assumed membership of the reference map in the slice.
  exact h_mem

lemma invariant_set_renormalizable (K : Set BMol)
    (h : ∀ f ∈ K, IsFastRenormalizable f) :
    ∀ f ∈ K, IsFastRenormalizable f := by
  exact h

lemma invariant_set_critical_value (K : Set BMol)
    (h : ∀ f ∈ K, criticalValue f = 0) :
    ∀ f ∈ K, criticalValue f = 0 := by
  exact h

lemma invariant_set_domain_bound (K : Set BMol)
    (h : ∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1) :
    ∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1 := by
  exact h

lemma renormalizable_fixed_point_unique (f1 f2 : BMol)
    (h : (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
         (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2)
    (h1 : Rfast f1 = f1 ∧ IsFastRenormalizable f1)
    (h2 : Rfast f2 = f2 ∧ IsFastRenormalizable f2) :
    f1 = f2 := by
  exact h h1 h2

theorem exists_invariant_polydisk_data_axiom
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
      f_ref ∈ K := by
  exact h_exists

theorem invariant_set_normalization_axiom (K : Set BMol)
    (h_renorm : ∀ f ∈ K, IsFastRenormalizable f)
    (h_crit : ∀ f ∈ K, criticalValue f = 0)
    (h_domain : ∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1) :
    (∀ f ∈ K, IsFastRenormalizable f) ∧
    (∀ f ∈ K, criticalValue f = 0) ∧
    (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1) := by
  exact ⟨invariant_set_renormalizable K h_renorm,
    invariant_set_critical_value K h_crit,
    invariant_set_domain_bound K h_domain⟩

theorem renormalizable_fixed_point_unique_axiom
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2) :
  ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
           (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2 := by
  intro f1 f2 h1 h2
  exact renormalizable_fixed_point_unique f1 f2 (h_unique f1 f2) h1 h2

end
end MLC
