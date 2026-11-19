import Mathlib.Tactic
import ThetLogos.PhaseRingSteps
import ThetLogos.PhaseRingEnergy

/-!
# MV-2 SPLIT BRICK — PhaseRingUniform (brick 4 of 5)

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

Contents of this brick: the uniform twists: `uniformLift` and its winding/step/twist/floor facts, plus the Fourier-lift instances (1 def + 6 theorems). Builds on bricks 1 and 3.

Dial-ineligible; NO CLAIM; dials 0/4.
-/


namespace ThetLogos
namespace PhaseRingRelax

open PhaseWinding

variable {n : ℕ}

/-! ## The uniform twists: equilibria at every winding -/

/-- The **uniform twist at any winding** `w : ℤ`: every
bond — the seam included — steps by `2π * w / (n + 1)`.
(The landed `fourierLift` is this at `w = m.val` for a
mode index `m`; the exhibit needs every integer.) -/
noncomputable def uniformLift (w : ℤ) : Lift n where
  Θ := fun k => 2 * Real.pi * (w : ℝ) * (k.val : ℝ) / ((n : ℝ) + 1)
  wrap := 2 * Real.pi * (w : ℝ) / ((n : ℝ) + 1)
  w := w
  closing := by
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    show (2 * Real.pi * (w : ℝ) * ((Fin.last n).val : ℝ)
          / ((n : ℝ) + 1))
        - (2 * Real.pi * (w : ℝ) * ((0 : Fin (n + 1)).val : ℝ)
            / ((n : ℝ) + 1))
        + (2 * Real.pi * (w : ℝ) / ((n : ℝ) + 1))
      = 2 * Real.pi * ((w : ℤ) : ℝ)
    rw [Fin.val_last]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
      sub_zero]
    push_cast
    field_simp

/-- The uniform twist's winding is the winding it was
built at. -/
theorem uniformLift_winding (w : ℤ) :
    (uniformLift (n := n) w).winding = w :=
  rfl

/-- Every bond of the uniform twist steps by the same
`2π * w / (n + 1)` — the wrap bond included. -/
theorem uniformLift_step (w : ℤ) (k : Fin (n + 1)) :
    (uniformLift (n := n) w).step k
      = 2 * Real.pi * (w : ℝ) / ((n : ℝ) + 1) := by
  by_cases hk : k = Fin.last n
  · subst hk
    exact Lift.step_last _
  · rw [Lift.step_of_ne_last _ hk]
    show 2 * Real.pi * (w : ℝ) * ((cyc k).val : ℝ) / ((n : ℝ) + 1)
        - 2 * Real.pi * (w : ℝ) * (k.val : ℝ) / ((n : ℝ) + 1)
        = 2 * Real.pi * (w : ℝ) / ((n : ℝ) + 1)
    rw [coe_cyc_of_ne_last hk]
    push_cast
    field_simp
    ring

/-- The uniform twist is a uniform twist: its every
step is its own mean step. -/
theorem uniformLift_isUniformTwist (w : ℤ) :
    IsUniformTwist (uniformLift (n := n) w) := by
  intro k
  rw [uniformLift_step]
  rfl

/-- The uniform twist attains the energy floor at its
winding. -/
theorem liftEnergy_uniformLift (w : ℤ) :
    liftEnergy (uniformLift (n := n) w)
      = ((n : ℝ) + 1) * (stepMean (uniformLift (n := n) w)) ^ 2 :=
  (liftEnergy_eq_iff _).mpr (uniformLift_isUniformTwist w)

/-- The landed Fourier lift is a uniform twist (its
winding is its mode index, its steps are uniform). -/
theorem fourierLift_isUniformTwist (m : Fin (n + 1)) :
    IsUniformTwist (fourierLift m) := by
  have hw : (fourierLift m).w = (m.val : ℤ) := rfl
  intro k
  rw [fourierLift_step]
  show 2 * Real.pi * (m.val : ℝ) / ((n : ℝ) + 1)
      = stepMean (fourierLift m)
  unfold stepMean
  rw [hw]
  push_cast
  ring

/-- The Fourier lift attains the energy floor at its
winding. -/
theorem liftEnergy_fourierLift (m : Fin (n + 1)) :
    liftEnergy (fourierLift m)
      = ((n : ℝ) + 1) * (stepMean (fourierLift m)) ^ 2 :=
  (liftEnergy_eq_iff _).mpr (fourierLift_isUniformTwist m)


end PhaseRingRelax
end ThetLogos
