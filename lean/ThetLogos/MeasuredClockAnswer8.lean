import ThetLogos.MeasuredClockAnswer
import Mathlib.Data.Fin.VecNotation

/-!
# ThetLogos.MeasuredClockAnswer8 — Q1′ answered at N = 8 (Tier T1, about T4 input)

**Status: the posted question `measuredClockQuestion`, answered for the
single instance below. NO CLAIM beyond that instance.**

The instance: **N = 8**, **ε = `clockObsErr 6` ≈ 8.87 × 10⁻¹²** — the same
tolerance as the landed N = 9 answer (`MeasuredClockAnswer`), the largest
of the seven entered published uncertainties.

Why 8 levels suffice, when the N = 9 construction spent 9: that
construction's squares were `0`, `1`, and `1 + obs m`, but its pairing
only ever touched the base level `1` — the `0` level was never used.
This module drops the offset anchor instead: since every measured ratio
is positive, the levels' squares can be `0` and the ratios themselves,
`obs m`, pairing each line against the zero level. The fit is **exact**
(fit error `0 ≤ ε`), with witnesses `β = 1`, `c = 1`,
`lam = √(squares)`, one triple and one temperature matching all seven
lines simultaneously, as the question demands.

This is a verdict on this instance only. The question at **N ≤ 7**
remains open — that is Q1′'s live form now — and the original
`blockedQ1` stands untouched.
-/

namespace ThetLogos

/-- The level squares of the N = 8 fit: `0` and the seven measured
    ratios themselves. -/
noncomputable def clockFitSq8 : Fin 8 → ℝ :=
  ![0, (clockObs 0 : ℝ), (clockObs 1 : ℝ), (clockObs 2 : ℝ), (clockObs 3 : ℝ),
    (clockObs 4 : ℝ), (clockObs 5 : ℝ), (clockObs 6 : ℝ)]

/-- The Dirac spectrum of the fit: square roots of `clockFitSq8`. -/
noncomputable def clockFitLam8 : Fin 8 → ℝ := fun k => Real.sqrt (clockFitSq8 k)

/-- The line assignment: line `m` is paired to its own level `m + 1`
    against the zero level `0`. -/
def clockFitF8 : Fin 7 → Fin 8 × Fin 8 :=
  fun m => (⟨m.val + 1, by have h := m.isLt; omega⟩, ⟨0, by norm_num⟩)

/-- The first component of the fit pairing lands on the level whose
    square is the measured ratio `obs m` itself. -/
lemma clockFitSq8_fst (m : Fin 7) :
    clockFitSq8 (clockFitF8 m).1 = (clockObs m : ℝ) := by
  fin_cases m <;> simp [clockFitSq8, clockFitF8, clockObs]

/-- The second component of the fit pairing lands on the zero level,
    whose square is `0`. -/
lemma clockFitSq8_snd (m : Fin 7) : clockFitSq8 (clockFitF8 m).2 = 0 := by
  fin_cases m <;> simp [clockFitSq8, clockFitF8]

/-- **Q1′ answered at N = 8** (ε the largest entered uncertainty): the
    measured clock spectrum is reproduced *exactly* (fit error 0 ≤ ε)
    by one thermal triple — `β = 1`, `lam = clockFitLam8`, `c = 1`,
    `f = clockFitF8` — with each line read as a difference against the
    zero level. This is a verdict on this instance only; the question
    at N ≤ 7 stays open, and the original `blockedQ1` stands
    untouched. -/
theorem measuredClockAnswer8 :
    measuredClockQuestion 8 (clockObsErr 6 : ℝ) := by
  refine ⟨1, clockFitLam8, 1, clockFitF8, one_pos, one_ne_zero, ?_⟩
  intro m
  have h1 := clockFitSq8_fst m
  have h2 := clockFitSq8_snd m
  have hpos := clockObs_nonneg m
  have e1 : (clockFitLam8 (clockFitF8 m).1) ^ 2 = (clockObs m : ℝ) := by
    have hnn : (0 : ℝ) ≤ clockFitSq8 (clockFitF8 m).1 := by rw [h1]; exact hpos
    calc (clockFitLam8 (clockFitF8 m).1) ^ 2
        = clockFitSq8 (clockFitF8 m).1 := Real.sq_sqrt hnn
      _ = (clockObs m : ℝ) := h1
  have e2 : (clockFitLam8 (clockFitF8 m).2) ^ 2 = 0 := by
    have hnn : (0 : ℝ) ≤ clockFitSq8 (clockFitF8 m).2 := by rw [h2]
    calc (clockFitLam8 (clockFitF8 m).2) ^ 2
        = clockFitSq8 (clockFitF8 m).2 := Real.sq_sqrt hnn
      _ = 0 := h2
  have hdiff : modularFreqDiff 1 clockFitLam8 (clockFitF8 m).1 (clockFitF8 m).2
      = (clockObs m : ℝ) := by
    rw [modularFreqDiff, e1, e2]; ring
  rw [hdiff, one_mul, sub_self, abs_zero]
  exact clockObsErr_six_nonneg

end ThetLogos
