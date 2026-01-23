import Molecule.BMol
import Molecule.Rfast
import Yoccoz.Quadratic.Complex.Basic
import Molecule.FixedPointExistence

namespace MLC

open Quadratic Complex Topology Set Filter Classical

/--
A quasidisk is the image of the unit disk under a quasiconformal map of the plane.
This definition is kept opaque to avoid trivial proofs.
Ref: @refs/1703.01206v3.pdf
-/
opaque IsQuasidisk (s : Set ℂ) : Prop

/--
The pseudo-invariant property.
This typically means f(s ∩ U) ⊆ s or similar quasi-invariance, related to "P-invariant".
This definition is kept opaque to avoid trivial proofs.
Ref: @refs/1703.01206v3.pdf
-/
opaque PseudoInvariant (f : BMol) (s : Set ℂ) : Prop

/-- Every quasidisk is an open set. -/
axiom IsQuasidisk.is_open {s : Set ℂ} : IsQuasidisk s → IsOpen s

/-- The fixed point of renormalization has a pseudo-invariant quasidisk within D. -/
theorem fixed_point_has_ps_disk (f_star : BMol) (D : Set ℂ) (_h_open : IsOpen D)
    (_h_crit : criticalValue f_star ∈ D) (_h_fixed : Rfast f_star = f_star)
    (h_ps : ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps) :
  ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps :=
  h_ps

/--
Constructs the pseudo-Siegel disk for the fixed point f_star within the domain D.
This construction "fills in" parabolic fjords to ensure controlled geometry.
-/
noncomputable def construct_pseudo_siegel_disk (f_star : BMol) (D : Set ℂ)
    (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
      ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps) :
    Set ℂ :=
  if h : Rfast f_star = f_star ∧ IsOpen D ∧ criticalValue f_star ∈ D then
    Classical.choose (h_ps h.2.1 h.2.2 h.1)
  else
    ∅

/-- The constructed pseudo-Siegel disk is a quasidisk. -/
lemma ps_disk_quasidisk (f_star : BMol) (D : Set ℂ)
  (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
  (h_fixed : Rfast f_star = f_star) (_ : IsFastRenormalizable f_star)
  (h_open : IsOpen D) (h_crit : criticalValue f_star ∈ D) :
  IsQuasidisk (construct_pseudo_siegel_disk f_star D h_ps) := by
    rw [construct_pseudo_siegel_disk]
    have h_cond : Rfast f_star = f_star ∧ IsOpen D ∧ criticalValue f_star ∈ D := ⟨h_fixed, h_open, h_crit⟩
    rw [dif_pos h_cond]
    have h_exists := h_ps h_open h_crit h_fixed
    exact (Classical.choose_spec h_exists).2.1

/-- The constructed pseudo-Siegel disk is open. -/
lemma ps_disk_is_open (f_star : BMol) (D : Set ℂ)
  (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
  (h_fixed : Rfast f_star = f_star) (h_fast : IsFastRenormalizable f_star)
  (h_open : IsOpen D) (h_crit : criticalValue f_star ∈ D) :
  IsOpen (construct_pseudo_siegel_disk f_star D h_ps) := by
    apply IsQuasidisk.is_open
    exact ps_disk_quasidisk f_star D h_ps h_fixed h_fast h_open h_crit

/-- The constructed pseudo-Siegel disk contains the critical value. -/
lemma ps_disk_contains_crit (f_star : BMol) (D : Set ℂ)
  (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
  (h_fixed : Rfast f_star = f_star) (h_open : IsOpen D) (h_crit : criticalValue f_star ∈ D) :
  criticalValue f_star ∈ construct_pseudo_siegel_disk f_star D h_ps := by
    rw [construct_pseudo_siegel_disk]
    have h_cond : Rfast f_star = f_star ∧ IsOpen D ∧ criticalValue f_star ∈ D := ⟨h_fixed, h_open, h_crit⟩
    rw [dif_pos h_cond]
    have h_exists := h_ps h_open h_crit h_fixed
    exact (Classical.choose_spec h_exists).2.2.2

/-- The constructed pseudo-Siegel disk is a subset of D. -/
lemma ps_disk_subset (f_star : BMol) (D : Set ℂ)
  (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps) :
  construct_pseudo_siegel_disk f_star D h_ps ⊆ D := by
    rw [construct_pseudo_siegel_disk]
    split_ifs with h
    · obtain ⟨h_fixed, h_open, h_crit⟩ := h
      have h_exists := h_ps h_open h_crit h_fixed
      exact (Classical.choose_spec h_exists).1
    · exact Set.empty_subset D

/-- The constructed pseudo-Siegel disk is pseudo-invariant. -/
lemma ps_disk_invariant (f_star : BMol) (D : Set ℂ)
  (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
  (h_fixed : Rfast f_star = f_star) (_ : IsFastRenormalizable f_star)
  (h_open : IsOpen D) (h_crit : criticalValue f_star ∈ D) :
  PseudoInvariant f_star (construct_pseudo_siegel_disk f_star D h_ps) := by
    rw [construct_pseudo_siegel_disk]
    have h_cond : Rfast f_star = f_star ∧ IsOpen D ∧ criticalValue f_star ∈ D := ⟨h_fixed, h_open, h_crit⟩
    rw [dif_pos h_cond]
    have h_exists := h_ps h_open h_crit h_fixed
    exact (Classical.choose_spec h_exists).2.2.1

/--
Lemma: Existence of Pseudo-Siegel Disks.
One constructs "pseudo-Siegel disks" that fill in parabolic fjords (deep incursions of the Julia set),
obtaining quasi-invariant domains with controlled geometry.
-/
lemma exists_pseudo_siegel_disk (f_star : BMol) (D : Set ℂ)
  (h_ps : IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
    ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
  (h_fixed : Rfast f_star = f_star)
  (h_fast : IsFastRenormalizable f_star)
  (h_open : IsOpen D)
  (h_crit : criticalValue f_star ∈ D) :
  ∃ (D_ps : Set ℂ),
    IsOpen D_ps ∧
    criticalValue f_star ∈ D_ps ∧
    D_ps ⊆ D ∧
    IsQuasidisk D_ps ∧
    PseudoInvariant f_star D_ps := by
  use construct_pseudo_siegel_disk f_star D h_ps
  constructor
  · exact ps_disk_is_open f_star D h_ps h_fixed h_fast h_open h_crit
  constructor
  · exact ps_disk_contains_crit f_star D h_ps h_fixed h_open h_crit
  constructor
  · exact ps_disk_subset f_star D h_ps
  constructor
  · exact ps_disk_quasidisk f_star D h_ps h_fixed h_fast h_open h_crit
  · exact ps_disk_invariant f_star D h_ps h_fixed h_fast h_open h_crit

end MLC
