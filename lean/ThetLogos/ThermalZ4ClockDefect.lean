import ThetLogos.ThermalZ4Ladder

namespace ThetLogos

/-!
# ThetLogos.ThermalZ4ClockDefect — the clock defect (Tiers T1/T2)

The 4-state Gibbs ladder of `ThetLogos.ThermalZ4Ladder`, acted on by the
clock turn `k ↦ k + 1` on `Fin 4`. This brick transports the ladder's
landed step ratios — it does not re-derive them — into a statement about
the clock, and draws the non-invariance corollary.

## Content, stated plainly

The clock is a broken symmetry of the ladder's thermal state, and the
breaking is measured: `exp (-β / 4)` per step, `exp (3 * β / 4)` at the
wrap; the defect is exactly the ladder's slope. Headline 3,
`z4_clock_defect_factor`, is the defect factor identity, transported
from the ladder's landed `z4Weight_step_ratio` and
`z4Weight_wrap_ratio`. Headline 4, `z4_clock_not_invariant`, is its
teeth: for `β > 0` the shifted weights are not the weights.

## Bearing, labeled on the face

This module is RAW MATERIAL FOR W2: a measured state-asymmetry under
the clock that a grading could carry. It is raw material only — it does
not land W2, and it constructs no irreversible step and no semigroup.

It has no bearing on W1: nothing here is a flow or a section of one.

G1/G2 are untouched: the defect is a fact about the clock acting on
weights, fully compatible with the landed verdict that the modular
flow fixes its Gibbs state. The C⁴ leg's strong form stays
refuted-as-stated; this brick is not its exception.

## Fences

NO CLAIM.
Dials 0/4. This is a finite definition-and-identity brick: a clock
turn, a shifted weight, one transported factor identity, and one
non-invariance corollary. Nothing further is asserted.
-/

/-- The clock turn on `Fin 4`: `k ↦ k + 1`, in `Fin 4`'s modular
    addition (so site 3 turns to site 0). Tier T2. -/
def z4Shift (k : Fin 4) : Fin 4 := k + 1

/-- The clock-turned state read at site `k`: the ladder weight at the
    turned site, `z4Weight β (k + 1)`. Tier T2. -/
noncomputable def z4ShiftedWeight (β : ℝ) (k : Fin 4) : ℝ :=
  z4Weight β (z4Shift k)

/-- Headline 3 — defect factor identity, TRANSPORTED from the ladder's
    landed step ratios (`z4Weight_step_ratio` at the matching
    `Fin 3` index for the within-ladder steps, `z4Weight_wrap_ratio`
    at the wrap). The ladder's ratios are consumed as landed; they are
    not re-derived here. Per step the shifted weight is
    `exp (-β / 4)` times the weight; at the wrap it is
    `exp (3 * β / 4)` times the weight at site 3. Tier T1. -/
theorem z4_clock_defect_factor (β : ℝ) :
    (∀ k : Fin 4, k.val < 3 →
        z4ShiftedWeight β k = Real.exp (-β / 4) * z4Weight β k)
      ∧ z4ShiftedWeight β 3 = Real.exp (3 * β / 4) * z4Weight β 3 := by
  constructor
  · intro k hk
    have hcast : Fin.castSucc (⟨k.val, hk⟩ : Fin 3) = k := by
      ext
      rfl
    have hsucc : (⟨k.val, hk⟩ : Fin 3).succ = z4Shift k := by
      ext
      simp only [Fin.val_succ, z4Shift, Fin.val_add, Fin.val_one]
      have hlt : k.val + 1 < 4 := by omega
      rw [Nat.mod_eq_of_lt hlt]
    have h := z4Weight_step_ratio β (⟨k.val, hk⟩ : Fin 3)
    rw [hsucc, hcast] at h
    unfold z4ShiftedWeight
    rw [h, mul_comm]
  · have hshift : z4Shift (3 : Fin 4) = 0 := by
      ext
      simp [z4Shift]
    unfold z4ShiftedWeight
    rw [hshift, z4Weight_wrap_ratio, mul_comm]

/-- Headline 4 — non-invariance corollary (the teeth): for `β > 0`
    the clock-turned weights are NOT the weights. At site 0, Headline 3
    gives the factor `exp (-β / 4) ≠ 1` against a strictly positive
    weight (`z4Weight_pos`). Tier T1. -/
theorem z4_clock_not_invariant {β : ℝ} (hβ : 0 < β) :
    ¬ (∀ k : Fin 4, z4ShiftedWeight β k = z4Weight β k) := by
  intro h
  have h0 := h 0
  have hdef := (z4_clock_defect_factor β).1 0 (by decide)
  rw [hdef] at h0
  have hw : 0 < z4Weight β 0 := z4Weight_pos β 0
  have hexp : Real.exp (-β / 4) = 1 := by
    have hmul : Real.exp (-β / 4) * z4Weight β 0
        = 1 * z4Weight β 0 := by
      rw [one_mul]
      exact h0
    exact mul_right_cancel₀ hw.ne' hmul
  rw [Real.exp_eq_one_iff] at hexp
  linarith

end ThetLogos
