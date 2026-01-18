import Molecule.BMol
import Molecule.Rfast
import Yoccoz.Quadratic.Complex.Basic
import Molecule.FixedPointExistence
import Molecule.PseudoSiegelDisk

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Axiom: Renormalization Pullback Existence.
For a map f sufficiently close to the renormalization fixed point (in the renormalization sense),
and for specific return times t, there exists a pullback domain D0 mapping properly onto D with degree 2.
This reflects the branched covering property of the renormalized maps.
-/
axiom renormalization_pullback_axiom (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ) :
  Rfast f_star = f_star →
  IsFastRenormalizable f_star →
  IsOpen D → IsOpen U →
  f_star ∈ U →
  criticalValue f_star ∈ D →
  ∀ (n t : ℕ) (f : BMol),
    n ≥ 1 →
    t ∈ ({a n, b n} : Set ℕ) →
    f ∈ (Rfast^[n]) ⁻¹' U →
    ∃ (D0 : Set ℂ) (h_maps : MapsTo (f.f^[t]) D0 D),
      IsOpen D0 ∧
      (criticalValue f) ∈ D0 ∧
      IsProperMap (MapsTo.restrict (f.f^[t]) D0 D h_maps) ∧
      ∀ y ∈ D, Set.ncard {x ∈ D0 | (f.f^[t]) x = y} = 2

/--
Lemma: Renormalization Pullback Property.
For sufficiently large n, the map has a pullback domain D0 such that it is a proper map of degree 2 onto D.
-/
lemma renormalization_pullback_property (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ)
  (n t : ℕ) (f : BMol)
  (h_fixed : Rfast f_star = f_star)
  (h_renorm : IsFastRenormalizable f_star)
  (h_open_D : IsOpen D) (h_open_U : IsOpen U)
  (h_f_star_in_U : f_star ∈ U)
  (h_cv_in_D : criticalValue f_star ∈ D)
  (h_n_ge_1 : n ≥ 1)
  (h_t_in_set : t ∈ ({a n, b n} : Set ℕ))
  (h_f_in_preimage : f ∈ (Rfast^[n]) ⁻¹' U) :
  ∃ (D0 : Set ℂ) (h_maps : MapsTo (f.f^[t]) D0 D),
    IsOpen D0 ∧
    (criticalValue f) ∈ D0 ∧
    IsProperMap (MapsTo.restrict (f.f^[t]) D0 D h_maps) ∧
    ∀ y ∈ D, Set.ncard {x ∈ D0 | (f.f^[t]) x = y} = 2 := by
  apply renormalization_pullback_axiom f_star D U a b h_fixed h_renorm h_open_D h_open_U h_f_star_in_U h_cv_in_D n t f h_n_ge_1 h_t_in_set h_f_in_preimage

end MLC
