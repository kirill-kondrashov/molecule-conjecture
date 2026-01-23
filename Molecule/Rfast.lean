import Molecule.BMol
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic

namespace Molecule

open Complex Topology Set

/--
Relation defining when `g'` is a renormalization of `g` with period `p` and rescaling `ψ`.
This is a general definition for quadratic-like renormalization.
Pacman renormalization is a specific instance of this with particular domain geometries (Pacman shapes).
-/
structure RenormalizationRelation (g g' : BMol) where
  p : ℕ
  p_pos : p ≥ 2
  U' : Set ℂ
  V' : Set ℂ
  ψ : ℂ → ℂ -- Rescaling map
  -- Domains are subsets of the original
  U'_sub : U' ⊆ g.U
  V'_sub : V' ⊆ g.V
  -- Rescaling is an affine isomorphism
  rescaling_affine : ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, ψ z = a * z + b
  -- Rescaling maps the new map's domains to the restriction domains
  maps_U : MapsTo ψ g'.U U'
  maps_V : MapsTo ψ g'.V V'
  surj_U : ψ '' g'.U = U'
  surj_V : ψ '' g'.V = V'
  -- The fundamental renormalization equation: g'.f = ψ⁻¹ ∘ g.f^p ∘ ψ
  eq_f : ∀ z ∈ g'.U, ψ (g'.f z) = (g.f^[p] (ψ z))

/--
Predicate determining if a BMol map `g` is renormalizable in the "fast" (Pacman) sense.
Per Dudko-Lyubich-Selinger (arXiv:1703.01206), the operator Rfast is defined on a suitable
subspace of quadratic-like maps (or Pacman maps).
Here we define it as the existence of *some* valid renormalization.
Ideally, this would include conditions on the rotation number (Siegel parameters) and
the specific choice of "fast" return times (denominators of continued fraction convergents).
-/
def IsFastRenormalizable (g : BMol) : Prop :=
  ∃ g' : BMol, Nonempty (RenormalizationRelation g g')

attribute [local instance] Classical.propDecidable

/--
The Renormalization Operator Rfast.
It maps a BMol map to its renormalization.
If the map is "fast renormalizable", it returns the renormalized map.
Otherwise, it returns the map itself (acting as identity on non-renormalizable maps),
or could return a default value. We choose identity for stability.

In the rigorous construction, Rfast is a partial operator or defined on a specific domain.
Here we totalize it using `Classical.choose`.
-/
noncomputable def Rfast (g : BMol) : BMol :=
  if h : IsFastRenormalizable g then
    Classical.choose h
  else
    defaultBMol

lemma Rfast_spec (g : BMol) (h : IsFastRenormalizable g) :
    Nonempty (RenormalizationRelation g (Rfast g)) := by
  rw [Rfast, dif_pos h]
  exact Classical.choose_spec h

end Molecule
