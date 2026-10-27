import ThetLogos.MeasuredClockAnswer
import Mathlib.Data.Fin.VecNotation

/-!
# ThetLogos.MeasuredClockCollapse — the collapse receipt for Q1′ as posed

**Status: a self-correction artifact of this house, recorded at full
volume. NO CLAIM.**

The posted question Q1′ — `measuredClockQuestion N ε`, the existential
in `MeasuredClockSpectrum.lean` — is **ill-posed**: its tolerance `ε`
is absolute, while the target it must meet, `c * clockObs m`, scales
with the free constant `c`. Shrinking `c` therefore shrinks the target
into the tolerance with a zero spectrum, at *every* `N`. The headline
result below is the receipt, at theorem grade: with the degenerate
witness `β = 1`, `lam = fun _ => 0`, `f = fun _ => (0, 0)` and the
scale `c = 19 / 10^17`, every modular frequency difference is `0` and
`c * clockObs m ≤ c * clockObs 6 = clockObsErr 6` — the last step being
the exact rational identity the data entry itself built in
(`clockObsErr 6 = clockObs 6 * (19 / 10^17)`, proved below from the
entered table). The same construction proves the question at *every*
positive tolerance (second theorem). The posed existential has no
`N`-content at all: the definition answers itself.

**What this does not touch.** The N = 9 and N = 8 theorems
(`measuredClockAnswer`, `measuredClockAnswer8`) **stand** — they are
exact, nondegenerate fits at `c = 1`, and those witnesses remain the
meaningful content. What falls is only the framing that below those
instances the posed question remained a question. The repaired
question, in which the scale is eliminated and the tolerances ride
per-line in observation units, is a *new* entry (Q1′′) under the
house relabeling rule; the original `blockedQ1` stands untouched, and
`measuredClockQuestion` is not edited.
-/

namespace ThetLogos

/-- Every entered ratio is dominated by the index-6 ratio — checked
    entry by entry against the entered table. -/
lemma clockObs_le_six : ∀ m : Fin 7, clockObs m ≤ clockObs 6 := by
  intro m
  fin_cases m <;> norm_num [clockObs]

/-- The data entry's own exact identity: the index-6 uncertainty is
    the index-6 ratio times `19 / 10^17` — read off the entered table,
    not an approximation. -/
lemma clockObsErr_six_eq : clockObsErr 6 = clockObs 6 * (19 / 10 ^ 17) := by
  norm_num [clockObs, clockObsErr]

/-- **The collapse receipt.** The posed question Q1′, at its
    pre-registered tolerance `ε = clockObsErr 6`, is true at *every*
    `N` — decided trivially by the degenerate witness in the module
    header. This records the ill-posedness of the posed existential
    (absolute tolerance against a freely scaling target); it is not
    a fit. The exact fits at N = 9 and N = 8 stand untouched. -/
theorem measuredClockQuestion_trivial (N : ℕ) [NeZero N] :
    measuredClockQuestion N (clockObsErr 6 : ℝ) := by
  refine ⟨1, fun _ => 0, ((19 / 10 ^ 17 : ℚ) : ℝ),
    fun _ => (⟨0, NeZero.pos N⟩, ⟨0, NeZero.pos N⟩), one_pos, ?_, ?_⟩
  · exact_mod_cast (by norm_num : (19 / 10 ^ 17 : ℚ) ≠ 0)
  · intro m
    have hdiff : modularFreqDiff 1 (fun _ => (0 : ℝ)) (⟨0, NeZero.pos N⟩ : Fin N)
        (⟨0, NeZero.pos N⟩ : Fin N) = 0 := by
      simp [modularFreqDiff]
    have hq : (19 / 10 ^ 17 : ℚ) * clockObs m ≤ clockObsErr 6 := by
      rw [clockObsErr_six_eq, mul_comm (clockObs 6)]
      exact mul_le_mul_of_nonneg_left (clockObs_le_six m) (by norm_num)
    have hcast : ((19 / 10 ^ 17 : ℚ) : ℝ) * (clockObs m : ℝ)
        = (((19 / 10 ^ 17 : ℚ) * clockObs m : ℚ) : ℝ) := by
      push_cast
      ring
    rw [hdiff, zero_sub, hcast, abs_neg, ← Rat.cast_abs]
    rw [abs_of_nonneg (mul_nonneg (by norm_num)
      (by exact_mod_cast clockObs_nonneg m))]
    exact_mod_cast hq

/-- **The general-tolerance form of the collapse.** The posed
    question is true at every `N` and every positive tolerance `ε`:
    the same zero spectrum works, with the scale
    `c = ε / (2 * clockObs 6)` chosen small enough that the scaled
    target fits inside `ε` on its own. -/
theorem measuredClockQuestion_of_pos (N : ℕ) [NeZero N] {ε : ℝ}
    (hε : 0 < ε) : measuredClockQuestion N ε := by
  have h6 : (0 : ℝ) < (clockObs 6 : ℝ) := by
    have h : (0 : ℚ) < clockObs 6 := by norm_num [clockObs]
    exact_mod_cast h
  refine ⟨1, fun _ => 0, ε / (2 * (clockObs 6 : ℝ)),
    fun _ => (⟨0, NeZero.pos N⟩, ⟨0, NeZero.pos N⟩), one_pos, ?_, ?_⟩
  · positivity
  · intro m
    have hdiff : modularFreqDiff 1 (fun _ => (0 : ℝ)) (⟨0, NeZero.pos N⟩ : Fin N)
        (⟨0, NeZero.pos N⟩ : Fin N) = 0 := by
      simp [modularFreqDiff]
    have hm : (clockObs m : ℝ) ≤ (clockObs 6 : ℝ) := by
      exact_mod_cast clockObs_le_six m
    have hc : (0 : ℝ) ≤ ε / (2 * (clockObs 6 : ℝ)) := by positivity
    rw [hdiff, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hc (clockObs_nonneg m))]
    calc ε / (2 * (clockObs 6 : ℝ)) * (clockObs m : ℝ)
        ≤ ε / (2 * (clockObs 6 : ℝ)) * (clockObs 6 : ℝ) :=
          mul_le_mul_of_nonneg_left hm hc
      _ = ε / 2 := by field_simp
      _ ≤ ε := by linarith

end ThetLogos
