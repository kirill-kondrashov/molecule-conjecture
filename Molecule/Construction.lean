import Molecule.BMol
import Molecule.Mol
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.Algebra.Module.Basic

namespace MLC

open Complex Topology Filter Set

noncomputable section

/-!
# Construction of the Molecule Renormalization Models

This file constructs the concrete mathematical objects that serve as models for the
Molecule Conjecture.

1. **The Molecule Map (Q)**: `Q(z) = z(z+1)^2`. This cubic polynomial models the
   combinatorics of the renormalization.
2. **The Combinatorial Model (Rprm)**: Defined on the boundary of the Main Cardioid
   via its action on internal angles.

## References
* [DLS17] Dudko, Lyubich, Selinger, "Pacman Renormalization...", arXiv:1703.01206.
-/

/--
The "Molecule Map" Q(z) = z(z+1)^2.
This map models the dynamics of the renormalization operator on the moduli space.
-/
def MoleculeMap (z : ℂ) : ℂ := z * (z + 1)^2

lemma MoleculeMap_def (z : ℂ) : MoleculeMap z = z * (z^2 + 2*z + 1) := by
  dsimp [MoleculeMap]
  ring

/--
The derivative of the Molecule Map.
Q'(z) = (z+1)^2 + z * 2(z+1) = (z+1)(z+1 + 2z) = (z+1)(3z+1)
-/
def MoleculeMap_deriv (z : ℂ) : ℂ := (z + 1) * (3 * z + 1)

lemma MoleculeMap_deriv_correct : ∀ z, deriv MoleculeMap z = MoleculeMap_deriv z := by
  intro z
  unfold MoleculeMap MoleculeMap_deriv
  -- Expand (z+1)^2 = z^2 + 2z + 1
  have h_eq : (fun w : ℂ => w * (w + 1)^2) = (fun w => w^3 + 2*w^2 + w) := by
    funext w
    ring
  
  -- Use conv to rewrite inside the deriv application
  conv =>
    lhs
    arg 1
    rw [h_eq]
    
  -- Define the parts using combinators
  let p1 : ℂ → ℂ := id
  let p3 : ℂ → ℂ := p1 ^ 3
  let p2 : ℂ → ℂ := fun w => 2 * (p1 w)^2
  
  have h_split : (fun w => w^3 + 2*w^2 + w) = p3 + p2 + p1 := by
    funext w
    dsimp [p3, p2, p1]
    
  rw [h_split]
    
  -- Now we can use deriv_add on function sums
  rw [deriv_add]
  rotate_left
  · -- Differentiability of p3 + p2
    apply DifferentiableAt.add
    · apply DifferentiableAt.pow; apply differentiableAt_id
    · dsimp [p2, p1]; apply DifferentiableAt.const_mul; apply DifferentiableAt.pow; apply differentiableAt_id
  · -- Differentiability of p1
    apply differentiableAt_id
    
  rw [deriv_add]
  rotate_left
  · -- Differentiability of p3
    apply DifferentiableAt.pow; apply differentiableAt_id
  · -- Differentiability of p2
    dsimp [p2, p1]; apply DifferentiableAt.const_mul; apply DifferentiableAt.pow; apply differentiableAt_id
    
  -- Now the main equality goal: deriv p3 z + deriv p2 z + deriv p1 z = ...
  
  -- deriv p3
  dsimp [p3]
  rw [deriv_pow (f:=p1) differentiableAt_id]
  dsimp [p1]
  
  -- deriv p2
  dsimp [p2]
  rw [deriv_const_mul (c:=2)]
  rotate_left
  · dsimp [p1]; apply DifferentiableAt.pow; apply differentiableAt_id
    
  dsimp [p1]
  erw [deriv_pow (f:=id) differentiableAt_id]
  
  -- deriv p1
  rw [deriv_id z]
  
  dsimp
  ring

/--
Fixed points of the Molecule Map.
Q(z) = z => z(z+1)^2 = z
Solutions: z = 0 or (z+1)^2 = 1 => z+1 = ±1 => z = 0 or z = -2.
So fixed points are 0 (parabolic) and -2 (repelling/attracting depending on context, check derivative).
-/
lemma MoleculeMap_fixed_points : {z | MoleculeMap z = z} = {0, -2} := by
  ext z
  unfold MoleculeMap
  simp only [mem_setOf_eq]
  constructor
  · intro h
    have : z * ((z + 1)^2 - 1) = 0 := by rw [mul_sub_one, h, sub_self]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero this with rfl | h_inner
    · simp
    · -- (z+1)^2 = 1
      have h_sq : (z + 1)^2 = 1 := eq_of_sub_eq_zero h_inner
      -- z+1 = 1 or z+1 = -1
      rcases eq_or_eq_neg_of_sq_eq_sq (z+1) 1 (by simp [h_sq]) with h1 | h2
      · left; rw [← add_left_inj 1] at h1; simp at h1; exact h1
      · right;
        have : z = -1 - 1 := eq_sub_of_add_eq h2
        norm_num at this
        exact this
  · intro h
    rcases h with rfl | rfl
    · simp
    · ring

/--
Derivative at fixed point 0.
Q'(0) = (0+1)(0+1) = 1.
This confirms 0 is a parabolic fixed point with multiplier 1.
-/
lemma MoleculeMap_parabolic_zero : deriv MoleculeMap 0 = 1 := by
  rw [MoleculeMap_deriv_correct, MoleculeMap_deriv]
  simp

/--
The Combinatorial Model R_prm acting on angles θ ∈ [0, 1).
Defined in Appendix C.2 of [DLS17].
-/
def Rprm_angle (theta : ℝ) : ℝ :=
  if theta ≤ 0.5 then
    theta / (1 - theta)
  else
    (2 * theta - 1) / theta

/--
The map R_prm restricted to the boundary of the Main Cardioid.
We parameterize the boundary by angle θ -> c(θ).
This defines the action on the moduli space boundary.
-/
def Rprm_boundary (c : ℂ) : ℂ :=
  -- This is a non-constructive definition if we can't invert the parameterization easily.
  -- Ideally, if c = MainCardioidParam(t), then Rprm(c) = MainCardioidParam(Rprm_angle(t)).
  -- For now, we define it via the angle property assuming c is on the boundary.
  c -- Placeholder for the actual geometric construction on C

end

end MLC
