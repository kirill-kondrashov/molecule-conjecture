import Molecule.BMol
import Molecule.PiecewiseAnalytic
import Molecule.Problem4_3
import Molecule.Rfast

namespace MLC

/--
Axiom: Global Piecewise Analyticity.
We assert that if the local bounds hold (implying a fixed point with spectral gap),
then the renormalization operator Rfast extends to a piecewise analytic map
with a 1D unstable direction on the full domain (or the relevant invariant subspace).
Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization...", Section 8.
-/
axiom bounds_imply_piecewise_analytic (h : PseudoSiegelAPrioriBoundsStatement) :
  IsPiecewiseAnalytic1DUnstable Rfast

end MLC
