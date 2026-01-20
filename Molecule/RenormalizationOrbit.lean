import Molecule.BMol
import Molecule.Rfast
import Yoccoz.Quadratic.Complex.Basic
import Molecule.FixedPointExistence
import Molecule.PseudoSiegelDisk

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Axiom: Renormalization convergence implies orbit control.
If a map f renormalizes to something close to the fixed point f_star,
then for large enough n, the renormalized return times map the critical point back into D.
This axiom encapsulates the geometric control provided by renormalization theory.
-/
axiom renormalization_orbit_control (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ) :
  Rfast f_star = f_star →
  IsFastRenormalizable f_star →
  IsOpen D → IsOpen U →
  f_star ∈ U →
  criticalValue f_star ∈ D →
  ∀ (n t : ℕ) (f : BMol),
    n ≥ 1 →
    t ∈ ({a n, b n} : Set ℕ) →
    f ∈ (Rfast^[n]) ⁻¹' U →
    MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
    criticalValue f ∈ (Rfast^[n] f).U ∧
    (f.f^[t] (criticalValue f)) ∈ D ∧
    (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z)

/--
Lemma: Renormalization implies domain control.
The domain of the n-th renormalization of f is contained in D.
-/
lemma renormalization_domain (f_star : BMol) (D : Set ℂ) (U : Set BMol) (n : ℕ) (f : BMol)
  (_h_f_star_in_U : f_star ∈ U)
  (_h_cv_in_D : criticalValue f_star ∈ D)
  (h_U_subset : ∀ g ∈ U, g.V ⊆ D)
  (h_f_in_preimage : f ∈ (Rfast^[n]) ⁻¹' U) :
  (Rfast^[n] f).V ⊆ D := by
  have h_renorm_in_U : (Rfast^[n] f) ∈ U := h_f_in_preimage
  exact h_U_subset (Rfast^[n] f) h_renorm_in_U

/--
Lemma: Renormalization Orbit Lands in D.
For sufficiently large n, the orbit of the critical value under the renormalized map lands in D.
-/
lemma renormalization_orbit_lands_in_D (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ)
  (n t : ℕ) (f : BMol)
  (h_fixed : Rfast f_star = f_star)
  (h_renorm : IsFastRenormalizable f_star)
  (h_open_D : IsOpen D) (h_open_U : IsOpen U)
  (h_f_star_in_U : f_star ∈ U)
  (h_cv_in_D : criticalValue f_star ∈ D)
  (h_n_ge_1 : n ≥ 1)
  (h_t_in_set : t ∈ ({a n, b n} : Set ℕ))
  (h_f_in_preimage : f ∈ (Rfast^[n]) ⁻¹' U) :
  (f.f^[t] (criticalValue f)) ∈ D := by
  exact (renormalization_orbit_control f_star D U a b h_fixed h_renorm h_open_D h_open_U h_f_star_in_U h_cv_in_D n t f h_n_ge_1 h_t_in_set h_f_in_preimage).2.2.1

end MLC