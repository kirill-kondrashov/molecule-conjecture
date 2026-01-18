import Molecule.BMol
import Molecule.Rfast
import Yoccoz.Quadratic.Complex.Basic
import Molecule.FixedPointExistence

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Axiom: Renormalization Implies Small Orbit Bounds.
If f renormalizes to the fixed point, its critical orbit stays in a small disk at specific times.
This encapsulates the "Key Lemma 4.8" dynamic content.
-/
axiom renormalization_implies_bounds (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ) :
  Rfast f_star = f_star →
  IsOpen D → IsOpen U →
  f_star ∈ U →
  criticalValue f_star ∈ D →
  (∀ᶠ n in atTop, ∀ t ∈ ({a n, b n} : Set ℕ),
      ∀ f, f ∈ (Rfast^[n]) ⁻¹' U →
        let c1 := criticalValue f
        let ft := f.f^[t]
        ft c1 ∈ D ∧
        ∃ (D0 : Set ℂ) (h_maps : MapsTo ft D0 D),
          IsOpen D0 ∧
          c1 ∈ D0 ∧
          IsProperMap (MapsTo.restrict ft D0 D h_maps) ∧
          ∀ y ∈ D, Set.ncard {x ∈ D0 | ft x = y} = 2
  )

end MLC
