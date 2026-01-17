import Molecule.HMol
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact

namespace MLC

open Topology

/-- 
Predicate for Compactness of the Horseshoe operator.
In the context of the Molecule Conjecture (Dudko-Lyubich-Selinger, arXiv:1703.01206),
"The renormalization horseshoe is compact" refers to the compactness of the invariant set 
in the appropriate function space topology.

Since we model the horseshoe invariant set as the type `HMol`, this predicate asserts 
that `HMol` is a compact space. The operator `f` is the restriction of the renormalization 
operator to this set; while the property is intrinsic to the set, we include `f` in the 
signature to match the conjecture's structure where the operator defines the horseshoe.
-/
def IsCompactOperator (_ : HMol → HMol) : Prop := CompactSpace HMol

end MLC
