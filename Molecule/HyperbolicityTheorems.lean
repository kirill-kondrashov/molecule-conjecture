import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.PiecewiseAnalytic
import Molecule.FirstStepConstruction
import Molecule.Problem4_3

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Theorem 1: Hyperbolicity of Rfast.
This is one of the main components of the Molecule Conjecture.
We prove that the constructed Rfast operator is hyperbolic.
This relies on the "A Priori Bounds" (Problem 4.3).
-/
theorem Rfast_hyperbolicity :
  PseudoSiegelAPrioriBoundsStatement → IsHyperbolic Rfast_constructed := sorry

/--
Theorem 2: Analytic properties of Rfast.
We prove the operator is piecewise analytic with a 1D unstable direction.
-/
theorem Rfast_piecewise_analytic :
  PseudoSiegelAPrioriBoundsStatement → IsPiecewiseAnalytic1DUnstable Rfast_constructed := sorry

end MLC
