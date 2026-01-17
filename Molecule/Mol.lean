import Lean
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Connected
import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape

namespace MLC

open Complex

noncomputable section

/--
The Main Cardioid of the Mandelbrot set.
It is the set of parameters c for which the quadratic polynomial f_c(z) = z^2 + c
has an attracting fixed point.
The boundary of the main cardioid is given by the map c(t) = (e^(it)/2)(1 - e^(it)/2) for t ∈ [0, 2π).
-/
def MainCardioid : Set ℂ :=
  { c : ℂ | ∃ z : ℂ, z^2 + c = z ∧ ‖2 * z‖ < 1 }

/-- The map parameterizing the Main Cardioid interior. -/
def mainCardioidMap (z : ℂ) : ℂ := z - z^2

lemma mainCardioid_eq_image : MainCardioid = mainCardioidMap '' (Metric.ball 0 0.5) := by
  ext c
  constructor
  · rintro ⟨z, hz_eq, h2z⟩
    refine ⟨z, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      simp at h2z
      linarith
    · simp [mainCardioidMap]
      linear_combination -1 * hz_eq
  · rintro ⟨z, hz, rfl⟩
    use z
    simp [mainCardioidMap]
    rw [Metric.mem_ball, dist_zero_right] at hz
    linarith

lemma isConnected_mainCardioid : IsConnected MainCardioid := by
  rw [mainCardioid_eq_image]
  apply IsConnected.image
  · refine (convex_ball (0 : ℂ) 0.5).isConnected ?_
    use 0
    simp [Metric.mem_ball]
    norm_num
  · exact (continuous_id.sub (continuous_id.pow 2)).continuousOn

/--
The Main Cardioid parameterization boundary.
-/
def MainCardioidParam (t : ℝ) : ℂ :=
  let lambda := Complex.exp (I * t) -- This is e^(it)
  (lambda / 2) * (1 - lambda / 2)   -- This is (e^it/2)(1 - e^it/2)

/--
A parameter c has an attracting periodic orbit if there exists a periodic point z of period n
such that the magnitude of the multiplier (derivative of f_c^n at z) is strictly less than 1.
-/
def HasAttractingPeriodicOrbit (c : ℂ) : Prop :=
  ∃ n : ℕ, n > 0 ∧ ∃ z : ℂ,
    (fun w => w^2 + c)^[n] z = z ∧
    ‖deriv ((fun w => w^2 + c)^[n]) z‖ < 1

/--
In the context of the Mandelbrot set ℳ, a hyperbolic component is a connected component of the interior of ℳ
consisting of parameters c for which the quadratic map f_c(z) = z^2 + c has an attracting periodic orbit.
Here we define the set of all such parameters. A "hyperbolic component" would be a connected component of this set.
-/
def HyperbolicParameters : Set ℂ :=
  { c : ℂ | HasAttractingPeriodicOrbit c }

/--
The "main molecule" of the Mandelbrot set, denoted by Mol.

Per Appendix C of Dudko, Lyubich, Selinger (arXiv:1703.01206v3):
"Let us denote by Mol the main molecule of the Mandelbrot set; i.e. Mol is
the smallest closed subset of M containing the main hyperbolic component as well
as all hyperbolic components obtained from the main component via parabolic
bifurcations."

For the purpose of this formalization, we define Mol as a subset of the complex plane ℂ.
We approximate the definition by defining it as the closure of the Main Cardioid.
This ensures it is connected and contained in M (Main Cardioid ⊆ M).
Ideally, `MolSet` would be defined as:
`closure (MainCardioid ∪ ⋃ (K ∈ ParabolicComponents), K)`
where `ParabolicComponents` are components attached to MainCardioid.
-/
def MolSet : Set ℂ := closure MainCardioid

/--
A property identifying if a parameter belongs to the main molecule branches.
Currently defined as simply belonging to the Mandelbrot set, as a placeholder
for the full definition involving hyperbolic components.
-/
def IsMainMoleculeComponent (c : ℂ) : Prop := c ∈ Quadratic.MandelbrotSet


/-- The type Mol is the subtype of complex numbers in the MolSet. -/
def Mol := { x // x ∈ MolSet }

/-- Mol inherits the subspace topology from ℂ. -/
instance : TopologicalSpace Mol := by unfold Mol; infer_instance

/--
Helper lemma: The orbit map is continuous in c.
-/
lemma continuous_orbit (n : ℕ) : Continuous (fun c : ℂ => Quadratic.orbit c 0 n) := by
  induction n with
  | zero => simp [Quadratic.orbit]; exact continuous_const
  | succ n ih =>
    simp [Quadratic.orbit_succ]
    exact (ih.pow 2).add continuous_id

/--
General escape lemma: if |z| > 2 and |z| ≥ |c|, the orbit escapes.
-/
lemma escapes_of_large_norm_and_ge_c {c z : ℂ} (hz : ‖z‖ > 2) (hcz : ‖c‖ ≤ ‖z‖) :
    ¬ Quadratic.boundedOrbit c z := by
  intro h_bounded
  rcases h_bounded with ⟨M, hM⟩
  -- We prove by induction that |z_n| ≥ 2 + 3^n * (|z| - 2)
  have growth : ∀ n, ‖Quadratic.orbit c z n‖ ≥ 2 + 3^n * (‖z‖ - 2) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      let zn := Quadratic.orbit c z n
      have h_zn_ge_2 : ‖zn‖ ≥ 2 + 3^n * (‖z‖ - 2) := ih
      have h_zn_gt_2 : ‖zn‖ > 2 := by
        have : 3^n * (‖z‖ - 2) > 0 := mul_pos (pow_pos (by norm_num) n) (sub_pos.mpr hz)
        linarith
      
      have h_zn_ge_c : ‖zn‖ ≥ ‖c‖ := by
        have : 3^n * (‖z‖ - 2) ≥ 1 * (‖z‖ - 2) := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (sub_nonneg.mpr (le_of_lt hz))
        linarith
      
      rw [Quadratic.orbit_succ]
      have tri : ‖zn^2 + c‖ ≥ ‖zn‖^2 - ‖c‖ := by
        have := norm_add_le (zn^2 + c) (-c)
        simp only [add_neg_cancel_right, norm_neg] at this
        rw [Complex.norm_pow] at this
        linarith
      
      have step_ineq : ‖zn‖^2 - ‖c‖ ≥ 2 + 3 * (‖zn‖ - 2) := by
        calc ‖zn‖^2 - ‖c‖ 
             ≥ ‖zn‖^2 - ‖zn‖ := by linarith
           _ = (‖zn‖ - 2) * (‖zn‖ + 1) + 2 := by ring
           _ ≥ (‖zn‖ - 2) * 3 + 2 := by
             have : ‖zn‖ + 1 ≥ 3 := by linarith
             nlinarith
           _ = 2 + 3 * (‖zn‖ - 2) := by ring
        
      calc ‖zn^2 + c‖ ≥ ‖zn‖^2 - ‖c‖ := tri
           _ ≥ 2 + 3 * (‖zn‖ - 2) := step_ineq
           _ ≥ 2 + 3 * (2 + 3^n * (‖z‖ - 2) - 2) := by
             have : ‖zn‖ - 2 ≥ 3^n * (‖z‖ - 2) := by linarith
             linarith
           _ = 2 + 3 * (3^n * (‖z‖ - 2)) := by ring
           _ = 2 + 3^(n+1) * (‖z‖ - 2) := by ring_nf
  
  -- The growth implies unboundedness
  let C := ‖z‖ - 2
  have hC : C > 0 := sub_pos.mpr hz
  rcases exists_nat_ge ((M - 2) / C + 1) with ⟨N, hN_pow⟩
  have h3N : (3:ℝ)^N ≥ N := by
    have : ∀ n : ℕ, (3:ℝ)^n ≥ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        cases n with
        | zero => simp
        | succ n =>
          rw [pow_succ]
          simp only [Nat.cast_succ] at ih ⊢
          calc (3:ℝ)^(n+1) * 3 = 3 * (3:ℝ)^(n+1) := by ring
               _ ≥ 3 * (↑n + 1) := mul_le_mul_of_nonneg_left ih (by norm_num)
               _ = 3 * n + 3 := by ring
               _ ≥ n + 1 + 1 := by linarith
    exact this N
  
  specialize hM N
  have : ‖Quadratic.orbit c z N‖ ≥ 2 + 3^N * C := growth N
  have : 3^N * C > M - 2 := by
    calc (3:ℝ)^N * C ≥ N * C := mul_le_mul_of_nonneg_right h3N (le_of_lt hC)
         _ ≥ ((M - 2) / C + 1) * C := mul_le_mul_of_nonneg_right hN_pow (le_of_lt hC)
         _ = (M - 2) + C := by field_simp [ne_of_gt hC]
         _ > M - 2 := by linarith
  linarith

/--
If |z| > 2 and |c| ≤ 2, the orbit escapes to infinity.
-/
lemma escapes_if_gt_2 (c z : ℂ) (hc : ‖c‖ ≤ 2) (hz : ‖z‖ > 2) :
    ¬ Quadratic.boundedOrbit c z := by
  apply escapes_of_large_norm_and_ge_c hz
  trans 2
  exact hc
  exact le_of_lt hz

/--
If |c| > 2, the orbit of 0 escapes.
-/
lemma c_gt_2_escapes (c : ℂ) (hc : ‖c‖ > 2) : ¬ Quadratic.boundedOrbit c 0 := by
  have h_esc_c : ¬ Quadratic.boundedOrbit c c := by
    apply escapes_of_large_norm_and_ge_c hc (le_refl _)
  intro h_bounded
  apply h_esc_c
  cases h_bounded with | intro M hM =>
  use M
  intro n
  have : Quadratic.orbit c c n = Quadratic.orbit c 0 (n+1) := by
    dsimp [Quadratic.orbit]
    simp [Quadratic.fc]
  rw [this]
  exact hM (n+1)

/--
Mandelbrot set is contained in the closed disk of radius 2.
-/
lemma mandelbrot_subset_ball : Quadratic.MandelbrotSet ⊆ Metric.closedBall 0 2 := by
  intro c hc
  by_contra h
  rw [Metric.mem_closedBall, dist_zero_right] at h
  push_neg at h
  exact c_gt_2_escapes c h hc

/--
The Mandelbrot set is the intersection of preimages of the closed disk of radius 2 under the orbit maps.
M = ⋂_n {c | |f_c^n(0)| ≤ 2}
-/
lemma mandelbrot_eq_inter : Quadratic.MandelbrotSet = ⋂ n, {c : ℂ | ‖Quadratic.orbit c 0 n‖ ≤ 2} := by
  ext c
  constructor
  · intro h
    simp at *
    intro n
    by_contra h_gt
    push_neg at h_gt
    have hc_le_2 : ‖c‖ ≤ 2 := by
      by_contra h_big
      push_neg at h_big
      exact c_gt_2_escapes c h_big h
    have : ¬ Quadratic.boundedOrbit c 0 := by
       have h_esc := escapes_if_gt_2 c (Quadratic.orbit c 0 n) hc_le_2 h_gt
       intro h_bounded
       apply h_esc
       rcases h_bounded with ⟨M, hM⟩
       use M
       intro k
       simp [Quadratic.orbit, ← Function.iterate_add_apply, add_comm]
       exact hM (n + k)
    exact this h
  · intro h
    simp at *
    use 2

/--
Mandelbrot set is closed.
-/
lemma isClosed_mandelbrot : IsClosed Quadratic.MandelbrotSet := by
  rw [mandelbrot_eq_inter]
  apply isClosed_iInter
  intro n
  exact isClosed_le (continuous_norm.comp (continuous_orbit n)) continuous_const

/--
Mandelbrot set is compact.
-/
lemma isCompact_mandelbrot : IsCompact Quadratic.MandelbrotSet := by
  apply IsCompact.of_isClosed_subset
  · exact isCompact_closedBall 0 2
  · exact isClosed_mandelbrot
  · exact mandelbrot_subset_ball

/-- Mol is a closed subset of ℂ (closure MainCardioid). -/
lemma isClosed_molSet : IsClosed MolSet := isClosed_closure

/-- Mol is connected (closure of connected MainCardioid). -/
lemma isConnected_molSet : IsConnected MolSet :=
  IsConnected.closure isConnected_mainCardioid

lemma bounded_molSet : Bornology.IsBounded MolSet := by
  have h_subset : MainCardioid ⊆ Metric.ball 0 1 := by
    rw [mainCardioid_eq_image]
    rintro c ⟨z, hz, rfl⟩
    simp [mainCardioidMap]
    rw [Metric.mem_ball, dist_zero_right] at hz
    have : ‖z‖ < 0.5 := hz
    apply lt_of_le_of_lt (norm_sub_le z (z^2))
    rw [norm_pow]
    have : ‖z‖^2 < 0.25 := by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    linarith
  have h_clos : closure MainCardioid ⊆ Metric.closedBall 0 1 := by
    rw [← closure_ball (0:ℂ) (by norm_num)]
    exact closure_mono h_subset
  exact Bornology.IsBounded.subset Metric.isBounded_closedBall h_clos

lemma isCompact_molSet : IsCompact MolSet :=
  Metric.isCompact_of_isClosed_isBounded isClosed_molSet bounded_molSet

/-- Mol is compact. -/
instance : CompactSpace Mol := ⟨isCompact_iff_isCompact_univ.mp isCompact_molSet⟩

/-- Mol is a subset of ℂ, hence Hausdorff. -/
instance : T2Space Mol := by unfold Mol; infer_instance

/-- Mol is connected. -/
instance : ConnectedSpace Mol := isConnected_iff_connectedSpace.mp isConnected_molSet

/--
The cusp of the main molecule.
It corresponds to the cusp of the main cardioid (c = 1/4).
-/
def cuspVal : ℂ := 0.25

/-- We assume the cusp is in MolSet. -/
axiom cusp_in_Mol : cuspVal ∈ MolSet

def cusp : Mol := ⟨cuspVal, cusp_in_Mol⟩

instance : Inhabited Mol := ⟨cusp⟩

end
end MLC
