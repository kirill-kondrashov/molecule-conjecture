import Molecule.BMol
import Molecule.HMol
import Molecule.Rfast
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.Basic

namespace Molecule

open Complex Topology Set Classical

attribute [local instance] Classical.propDecidable

/--
Predicate relating a BMol map to an HMol map.
We say `g` extends `h` if `h` is contained in `g` and their functions agree.
This allows us to move between the disconnected horseshoe world and the connected QL world.
-/
def IsExtension (g : BMol) (h : HMol) : Prop :=
  h.U ⊆ g.U ∧ h.V ⊆ g.V ∧ EqOn h.f g.f h.V

/--
Converts a HorseshoeMap (HMol) to a QuadraticLikeMap (BMol).
We search for a BMol that extends the given HMol.
If none exists, we return a default BMol.
-/
noncomputable def associated_BMol (h : HMol) : BMol :=
  if exists_ext : ∃ g : BMol, IsExtension g h then
    Classical.choose exists_ext
  else
    defaultBMol

/--
Converts a QuadraticLikeMap (BMol) to a HorseshoeMap (HMol).
We search for an HMol that is a restriction of the given BMol.
If none exists, we return a default HMol.
-/
noncomputable def associated_HMol (g : BMol) : HMol :=
  if exists_restr : ∃ h : HMol, IsExtension g h then
    Classical.choose exists_restr
  else
    defaultHMol

/--
The Renormalization Horseshoe of an operator R : BMol → BMol.
Per Dudko-Lyubich-Selinger (arXiv:1703.01206), the renormalization horseshoe
is the set of points in BMol with bi-infinite precompact orbits under R.
Here we define Rfast_HMol as the restriction of Rfast to the subspace HMol.

We define the operator by converting the HMol to its associated BMol,
applying Rfast, and converting back to HMol.
-/
noncomputable def Rfast_HMol (h : HMol) : HMol :=
  associated_HMol (Rfast (associated_BMol h))

end Molecule
