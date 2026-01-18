import Molecule.BMol
import Molecule.Hyperbolicity
import Molecule.PiecewiseAnalytic
import Molecule.FirstStepConstruction
import Molecule.Problem4_3

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Axiom 1: Hyperbolicity of Rfast.
This is one of the main components of the Molecule Conjecture.
We assume that the constructed Rfast operator is hyperbolic.
This relies on the "A Priori Bounds" (Problem 4.3).
-/
axiom Rfast_hyperbolicity_axiom :
  PseudoSiegelAPrioriBoundsStatement → IsHyperbolic Rfast_constructed

/--
Axiom 2: Analytic properties of Rfast.
We assume the operator is piecewise analytic with a 1D unstable direction.
-/
axiom Rfast_piecewise_analytic_axiom :
  PseudoSiegelAPrioriBoundsStatement → IsPiecewiseAnalytic1DUnstable Rfast_constructed

end MLC
