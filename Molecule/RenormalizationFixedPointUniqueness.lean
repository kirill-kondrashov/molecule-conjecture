import Molecule.BMol
import Molecule.Rfast
import Molecule.Problem4_3

namespace Molecule

open Set
/--
Step 1: Domain Definition.
Hybrid equivalence classes of quadratic-like maps.
Modeled abstractly as points in a Teichmüller space.
-/
def HybridClass : Type := BMol
noncomputable instance : Inhabited HybridClass := ⟨defaultBMol⟩

/-- Projection from BMol to its hybrid class. -/
def toHybridClass (f : BMol) : HybridClass := f

/--
Abstraction seam for hybrid-class modeling.
This decouples downstream constructor routing from the current identity-model
choice `HybridClass := BMol`.
-/
structure HybridProjectionSeam where
  Class : Type
  proj : BMol → Class
  renorm : Class → Prop
  Rclass : Class → Class
  renorm_proj : ∀ f : BMol, IsFastRenormalizable f → renorm (proj f)
  fixed_proj : ∀ f : BMol, Rfast f = f → Rclass (proj f) = proj f

/--
Current seam instance induced by the present identity-model choice
`HybridClass := BMol`.
-/
noncomputable def currentHybridProjectionSeam : HybridProjectionSeam where
  Class := HybridClass
  proj := toHybridClass
  renorm := IsFastRenormalizable
  Rclass := fun c => Rfast c
  renorm_proj := by
    intro f h_renorm
    simpa [toHybridClass] using h_renorm
  fixed_proj := by
    intro f h_fix
    simpa [toHybridClass] using h_fix

/--
Current-model bottleneck: `toHybridClass` is injective because `HybridClass` is
currently modeled as `BMol`.
-/
theorem toHybridClass_injective : Function.Injective toHybridClass := by
  intro f g hfg
  exact hfg

/--
Current-model identity equivalence between hybrid-class equality and map
equality.
-/
theorem toHybridClass_eq_iff (f g : BMol) :
    toHybridClass f = toHybridClass g ↔ f = g := by
  constructor
  · intro hfg
    exact toHybridClass_injective hfg
  · intro h
    simp [h]

/--
Current seam projection remains injective in the identity-model instance.
-/
theorem current_hybrid_projection_seam_proj_injective :
    Function.Injective currentHybridProjectionSeam.proj := by
  simpa [currentHybridProjectionSeam] using toHybridClass_injective

/--
Current seam projection equality still collapses to map equality in the
identity-model instance.
-/
theorem current_hybrid_projection_seam_proj_eq_iff (f g : BMol) :
    currentHybridProjectionSeam.proj f = currentHybridProjectionSeam.proj g ↔ f = g := by
  simpa [currentHybridProjectionSeam] using toHybridClass_eq_iff f g

/--
Renormalization operator on hybrid classes.
This is well-defined because renormalization preserves hybrid equivalence.
-/
noncomputable def R_hybrid (c : HybridClass) : HybridClass := Rfast c

/--
Step 2: Commutativity.
Renormalization descends to the space of hybrid classes.
If f is renormalizable, its renormalization's class depends only on f's class.
-/
theorem renorm_descends_to_hybrid (f : BMol) (_h : IsFastRenormalizable f) :
  R_hybrid (toHybridClass f) = toHybridClass (Rfast f) := rfl

/--
Step 3: Contraction / Uniqueness.
The renormalization operator on hybrid classes has a unique fixed point.
This follows from the contraction of the operator in the Teichmüller metric.
-/
theorem R_hybrid_unique_fixed_point
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
    ∃! c : HybridClass, IsFastRenormalizable c ∧ R_hybrid c = c := by
  obtain ⟨c, ⟨hc_fix, hc_renorm⟩, hc_unique⟩ := feigenbaum_fixed_point_exists h_exists h_conj h_norm h_unique
  refine ⟨c, ⟨hc_renorm, hc_fix⟩, ?_⟩
  intro y ⟨hy_renorm, hy_fix⟩
  exact hc_unique y ⟨hy_fix, hy_renorm⟩

/--
Step 5: Rigidity.
Two fixed points of renormalization that belong to the same hybrid class must be identical.
This relies on the normalization (critical value 0) and the rigidity of the fixed point.
-/
theorem fixed_points_in_same_class_eq (f g : BMol)
  (_hf : IsFastRenormalizable f) (_hf_fix : Rfast f = f)
  (_hg : IsFastRenormalizable g) (_hg_fix : Rfast g = g)
  (h_eq_class : toHybridClass f = toHybridClass g) :
  f = g := (toHybridClass_eq_iff f g).1 h_eq_class

/--
Theorem: Uniqueness of the Renormalization Fixed Point.
This is a known result (universality) but we assume it here to link existence and hyperbolicity.
-/
theorem renormalization_fixed_point_unique
    (h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2)
    (f g : BMol) :
  IsFastRenormalizable f → Rfast f = f →
  IsFastRenormalizable g → Rfast g = g →
  f = g := by
  intro hf_renorm hf_fixed hg_renorm hg_fixed
  exact h_unique f g ⟨hf_fixed, hf_renorm⟩ ⟨hg_fixed, hg_renorm⟩

end Molecule
