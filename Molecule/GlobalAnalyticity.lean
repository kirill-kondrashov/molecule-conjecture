import Molecule.BMol
import Molecule.PiecewiseAnalytic
import Molecule.Problem4_3
import Molecule.Rfast

namespace Molecule

/--
Global Piecewise Analyticity (assumed).
We thread an explicit hypothesis that Rfast is piecewise analytic with a 1D unstable direction.
Reference: Dudko, Lyubich, Selinger, "Pacman Renormalization...", Section 8.
-/
theorem bounds_imply_piecewise_analytic
    (_h : PseudoSiegelAPrioriBoundsStatement)
    (h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast) :
  IsPiecewiseAnalytic1DUnstable Rfast :=
  h_piecewise

end Molecule
