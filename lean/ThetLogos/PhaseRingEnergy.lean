import Mathlib.Tactic
import ThetLogos.PhaseRingSteps

/-!
# MV-2 SPLIT BRICK — PhaseRingEnergy (brick 3 of 5)

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

Contents of this brick: the energy floor and its attainment: `liftEnergy_sub_floor`, `liftEnergy_nonneg`, `liftEnergy_ge`, `liftEnergy_eq_iff` (4 theorems). Builds on brick 1.

Dial-ineligible; NO CLAIM; dials 0/4.
-/


namespace ThetLogos
namespace PhaseRingRelax

open PhaseWinding

variable {n : ℕ}

/-! ## The energy floor and its attainment -/

/-- The energy above its floor is a sum of squared
deviations from the mean step: the algebra behind the
floor and its equality case. -/
theorem liftEnergy_sub_floor (L : Lift n) :
    liftEnergy L - ((n : ℝ) + 1) * (stepMean L) ^ 2
      = ∑ k, (L.step k - stepMean L) ^ 2 := by
  have hexp : ∀ k : Fin (n + 1),
      (L.step k - stepMean L) ^ 2
        = (L.step k) ^ 2 - (2 * stepMean L) * L.step k
          + (stepMean L) ^ 2 := fun k => by ring
  have hA : ∑ k, (2 * stepMean L) * L.step k
      = (2 * stepMean L) * (((n : ℝ) + 1) * stepMean L) := by
    rw [← Finset.mul_sum, sum_step_eq]
  have hC : ∑ _k : Fin (n + 1), (stepMean L) ^ 2
      = ((n : ℝ) + 1) * (stepMean L) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hC]
  show (∑ k, (L.step k) ^ 2) - ((n : ℝ) + 1) * (stepMean L) ^ 2
      = (∑ k, (L.step k) ^ 2) - (2 * stepMean L)
          * (((n : ℝ) + 1) * stepMean L)
          + ((n : ℝ) + 1) * (stepMean L) ^ 2
  ring

/-- The energy is nonnegative — a sum of squares. -/
theorem liftEnergy_nonneg (L : Lift n) : 0 ≤ liftEnergy L :=
  Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **The floor:** at any lift, the energy is at least
`(n + 1)` squared mean steps — equivalently
`(2π w)^2 / (n + 1)`. A ring's winding cannot be
carried for less. -/
theorem liftEnergy_ge (L : Lift n) :
    ((n : ℝ) + 1) * (stepMean L) ^ 2 ≤ liftEnergy L := by
  rw [← sub_nonneg, liftEnergy_sub_floor]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **The floor is attained exactly at the uniform
twists:** the energy equals its fixed-winding floor
iff every bond steps by the mean. -/
theorem liftEnergy_eq_iff (L : Lift n) :
    liftEnergy L = ((n : ℝ) + 1) * (stepMean L) ^ 2
      ↔ IsUniformTwist L := by
  constructor
  · intro h k
    have h0 : ∑ k, (L.step k - stepMean L) ^ 2 = 0 := by
      rw [← liftEnergy_sub_floor, sub_eq_zero]
      exact h
    have hk := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (L.step k - stepMean L))).mp h0 k
      (Finset.mem_univ k)
    have h2 : L.step k - stepMean L = 0 := by simpa using hk
    exact sub_eq_zero.mp h2
  · intro h
    have h0 : ∑ k, (L.step k - stepMean L) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [h k]
    rw [← sub_eq_zero, liftEnergy_sub_floor]
    exact h0


end PhaseRingRelax
end ThetLogos
