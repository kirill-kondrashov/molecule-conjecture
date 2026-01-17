import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.GreenLemmas
import Yoccoz.Quadratic.Complex.Groetzsch
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Finite.Basic
import Lean

namespace MLC

open Quadratic Complex Topology Set Filter

/-- Dudko's Molecule Conjecture. 
    We formulate it similarly to Yoccoz theorem but left as a conjecture (sorry). -/
theorem molecule_conjecture (c : ℂ) :
    ¬ (Summable fun n => modulus (PuzzleAnnulus c n)) →
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} := sorry

end MLC
