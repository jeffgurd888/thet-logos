import Mathlib.Tactic
import ThetLogos.PhaseRingSteps
import ThetLogos.PhaseRingRelaxStep
import ThetLogos.PhaseRingEnergy

/-!
# MV-2 SPLIT BRICK — PhaseRingRelaxEnergy (brick 5 of 5)

Split of the MV-2 draft module `ThetLogos.PhaseRingRelax`
(29 declarations) under the BRICK CAP law (Zero,
2026-11-11 21:37 EST; ~10 new declarations per build
invocation, banked per brick). Statements and proofs
are carried VERBATIM from the repaired draft
(mv2 @ 2456faf); the split moves text across module
seams only — no statement moved, no proof rewritten.
All declarations keep namespace
`ThetLogos.PhaseRingRelax`, so every full name is
unchanged. The design document lives in the header
of brick 1 (`ThetLogos.PhaseRingSteps`) and in
STATUS-MV2.md.

Contents of this brick: the energy under the step: the exact identity `liftEnergy_relaxStep`, the monotone `liftEnergy_relaxStep_le`, and the fixed-point characterization `relaxStep_fixed_iff` (3 theorems). Builds on bricks 1, 2, and 3.

Dial-ineligible; NO CLAIM; dials 0/4.
-/


namespace ThetLogos
namespace PhaseRingRelax

open PhaseWinding

variable {n : ℕ}

/-! ## The energy under the step: identity, monotone, fixed points -/

/-- **The exact energy identity:** one relaxation step
moves the energy toward the floor by the factor
`(1 − ε)^2` of its height above the floor — no more,
no less. -/
theorem liftEnergy_relaxStep (L : Lift n) (ε : ℝ) :
    liftEnergy (relaxStep L ε)
      = (1 - ε) ^ 2
          * (liftEnergy L - ((n : ℝ) + 1) * (stepMean L) ^ 2)
        + ((n : ℝ) + 1) * (stepMean L) ^ 2 := by
  have hstep : ∀ k : Fin (n + 1),
      (relaxStep L ε).step k
        = (1 - ε) * L.step k + ε * stepMean L := by
    intro k
    rw [relaxStep_step]
    ring
  have hexp : ∀ k : Fin (n + 1),
      ((1 - ε) * L.step k + ε * stepMean L) ^ 2
        = (1 - ε) ^ 2 * (L.step k) ^ 2
          + (2 * (1 - ε) * ε * stepMean L) * L.step k
          + ε ^ 2 * (stepMean L) ^ 2 := fun k => by ring
  have hA : ∑ k, (1 - ε) ^ 2 * (L.step k) ^ 2
      = (1 - ε) ^ 2 * liftEnergy L := by
    rw [← Finset.mul_sum]
    rfl
  have hB : ∑ k, (2 * (1 - ε) * ε * stepMean L) * L.step k
      = (2 * (1 - ε) * ε * stepMean L)
          * (((n : ℝ) + 1) * stepMean L) := by
    rw [← Finset.mul_sum, sum_step_eq]
  have hC : ∑ _k : Fin (n + 1), ε ^ 2 * (stepMean L) ^ 2
      = ε ^ 2 * (((n : ℝ) + 1) * (stepMean L) ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  calc liftEnergy (relaxStep L ε)
      = ∑ k, ((1 - ε) * L.step k + ε * stepMean L) ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [hstep k]
    _ = (1 - ε) ^ 2 * liftEnergy L
          + ((n : ℝ) + 1) * (stepMean L) ^ 2 * (2 * ε - ε ^ 2) := by
        rw [Finset.sum_congr rfl (fun k _ => hexp k),
          Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB,
          hC]
        ring
    _ = (1 - ε) ^ 2
            * (liftEnergy L - ((n : ℝ) + 1) * (stepMean L) ^ 2)
          + ((n : ℝ) + 1) * (stepMean L) ^ 2 := by ring

/-- **The monotone:** inside the stability bound
`ε ∈ [0, 1]`, one relaxation step does not increase
the lift Dirichlet energy. The bound is on the face —
outside it, no antitonicity is claimed. -/
theorem liftEnergy_relaxStep_le (L : Lift n) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    liftEnergy (relaxStep L ε) ≤ liftEnergy L := by
  obtain ⟨h0, h1⟩ := hε
  have hsq : (1 - ε) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - ε)]
  have hB := liftEnergy_ge L
  rw [liftEnergy_relaxStep]
  nlinarith [hB, hsq, sq_nonneg (1 - ε),
    mul_nonneg (sq_nonneg (1 - ε))
      (sub_nonneg.mpr hB)]

/-- **The equilibria of the step are exactly the
uniform twists:** at any nonzero step size, a lift
whose every bond is unmoved by the relaxation is a
uniform twist, and every uniform twist is unmoved.
At `w ≠ 0` these equilibria still carry their
winding — rest without unwinding. -/
theorem relaxStep_fixed_iff (L : Lift n) {ε : ℝ} (hε : ε ≠ 0) :
    (∀ k, (relaxStep L ε).step k = L.step k)
      ↔ IsUniformTwist L := by
  constructor
  · intro h k
    have hk := h k
    rw [relaxStep_step] at hk
    have hz : ε * (L.step k - stepMean L) = 0 := by linarith
    rcases mul_eq_zero.mp hz with hε' | hd
    · exact absurd hε' hε
    · exact sub_eq_zero.mp hd
  · intro h k
    rw [relaxStep_step, h k, sub_self, mul_zero, sub_zero]


end PhaseRingRelax
end ThetLogos
