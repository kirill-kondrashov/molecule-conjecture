import Molecule.HMol
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact

namespace Molecule

open Topology

/-- 
Predicate for Compactness of the Horseshoe operator.
In the context of the Molecule Conjecture (Dudko-Lyubich-Selinger, arXiv:1703.01206),
"The renormalization horseshoe is compact" refers to the compactness of the invariant set 
in the appropriate function space topology.

In the current model interface we encode this as existence of a nonempty compact
`f`-invariant core subset of `HMol`.
-/
def IsCompactOperator (f : HMol → HMol) : Prop :=
  ∃ K : Set HMol, IsCompact K ∧ K.Nonempty ∧ ∀ ⦃x : HMol⦄, x ∈ K → f x ∈ K

/-- Constant maps admit a compact invariant core (`{x0}`). -/
theorem isCompactOperator_of_constant (x0 : HMol) :
    IsCompactOperator (fun _ : HMol => x0) := by
  refine ⟨{x0}, isCompact_singleton, Set.singleton_nonempty x0, ?_⟩
  intro x hx
  simp

end Molecule
