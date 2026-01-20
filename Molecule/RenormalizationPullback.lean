import Molecule.BMol
import Molecule.Rfast
import Yoccoz.Quadratic.Complex.Basic
import Molecule.FixedPointExistence
import Molecule.PseudoSiegelDisk

namespace MLC

open Quadratic Complex Topology Set Filter

/--
The n-th renormalization of f.
-/
noncomputable def renorm_g (f : BMol) (n : ℕ) : BMol := (Rfast^[n]) f

/--
The rescaling map corresponding to n levels of renormalization.
For this sketch, we use the identity.
-/
noncomputable def renorm_Ψ (_f : BMol) (_n : ℕ) : ℂ → ℂ := λ z => z

/--
The target domain D_target defined by the renormalization.
-/
noncomputable def renorm_D_target (f : BMol) (n : ℕ) : Set ℂ :=
  (renorm_Ψ f n) '' (renorm_g f n).V

/--
The domain D0 defined by the renormalization.
-/
noncomputable def renorm_D0 (f : BMol) (n : ℕ) : Set ℂ :=
  (renorm_Ψ f n) '' (renorm_g f n).U

lemma renorm_D_target_subset (f_star : BMol) (D : Set ℂ) (U : Set BMol) (n : ℕ) (f : BMol)
  (h_f_star_in_U : f_star ∈ U)
  (h_cv_in_D : criticalValue f_star ∈ D)
  (h_f_in_preimage : f ∈ (Rfast^[n]) ⁻¹' U) :
  renorm_D_target f n ⊆ D := by sorry

lemma renorm_maps_to (f : BMol) (n t : ℕ) (a b : ℕ → ℕ)
  (h_t_in_set : t ∈ ({a n, b n} : Set ℕ)) :
  MapsTo (f.f^[t]) (renorm_D0 f n) (renorm_D_target f n) := by sorry

lemma renorm_D0_open (f : BMol) (n : ℕ) : IsOpen (renorm_D0 f n) := by sorry

lemma renorm_D_target_open (f : BMol) (n : ℕ) : IsOpen (renorm_D_target f n) := by sorry

lemma renorm_critical_value_mem (f : BMol) (n : ℕ) :
  criticalValue f ∈ renorm_D0 f n := by sorry

lemma renorm_is_proper (f : BMol) (n t : ℕ) (a b : ℕ → ℕ)
  (h_t_in_set : t ∈ ({a n, b n} : Set ℕ))
  (h_maps : MapsTo (f.f^[t]) (renorm_D0 f n) (renorm_D_target f n)) :
  IsProperMap (MapsTo.restrict (f.f^[t]) (renorm_D0 f n) (renorm_D_target f n) h_maps) := by sorry

lemma renorm_degree (f : BMol) (n t : ℕ) (a b : ℕ → ℕ)
  (h_t_in_set : t ∈ ({a n, b n} : Set ℕ))
  (y : ℂ) (hy : y ∈ renorm_D_target f n) :
  Set.ncard {x ∈ renorm_D0 f n | (f.f^[t]) x = y} = 2 := by sorry

/--
Lemma: Renormalization Pullback Property.
For sufficiently large n, the map has a pullback domain D0 such that it is a proper map of degree 2 onto
some domain D_target contained in D.
-/
lemma renormalization_pullback_property (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ)
  (n t : ℕ) (f : BMol)
  (_h_fixed : Rfast f_star = f_star)
  (_h_renorm : IsFastRenormalizable f_star)
  (_h_open_D : IsOpen D) (_h_open_U : IsOpen U)
  (h_f_star_in_U : f_star ∈ U)
  (h_cv_in_D : criticalValue f_star ∈ D)
  (_h_n_ge_1 : n ≥ 1)
  (h_t_in_set : t ∈ ({a n, b n} : Set ℕ))
  (h_f_in_preimage : f ∈ (Rfast^[n]) ⁻¹' U) :
  ∃ (D0 D_target : Set ℂ) (h_maps : MapsTo (f.f^[t]) D0 D_target),
    IsOpen D0 ∧ IsOpen D_target ∧
    D_target ⊆ D ∧
    (criticalValue f) ∈ D0 ∧
    IsProperMap (MapsTo.restrict (f.f^[t]) D0 D_target h_maps) ∧
    ∀ y ∈ D_target, Set.ncard {x ∈ D0 | (f.f^[t]) x = y} = 2 := by
  
  -- Step 1: Use definitions
  let D0 := renorm_D0 f n
  let D_target := renorm_D_target f n
  
  -- Step 2: Use lemmas
  have h_subset : D_target ⊆ D := renorm_D_target_subset f_star D U n f h_f_star_in_U h_cv_in_D h_f_in_preimage
  have h_maps : MapsTo (f.f^[t]) D0 D_target := renorm_maps_to f n t a b h_t_in_set
  have h_proper : IsProperMap (MapsTo.restrict (f.f^[t]) D0 D_target h_maps) := renorm_is_proper f n t a b h_t_in_set h_maps
  have h_degree : ∀ y ∈ D_target, Set.ncard {x ∈ D0 | (f.f^[t]) x = y} = 2 := renorm_degree f n t a b h_t_in_set
  
  refine ⟨D0, D_target, h_maps, ?_, ?_, h_subset, ?_, h_proper, h_degree⟩
  · exact renorm_D0_open f n
  · exact renorm_D_target_open f n
  · exact renorm_critical_value_mem f n

end MLC
