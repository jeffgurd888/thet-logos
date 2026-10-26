import ThetLogos.MeasuredClockSpectrum
import Mathlib.Data.Fin.VecNotation

/-!
# ThetLogos.MeasuredClockAnswer — Q1′ answered at one pre-registered instance (Tier T1, about T4 input)

**Status: the posted question `measuredClockQuestion`, answered for the
single pre-registered instance below. NO CLAIM beyond that instance.**

The instance (pre-registered in
`routeb-general-scratch/progress-q1answer.md` before any proof was
attempted, following the scoping memo
`routeb-general-scratch/q1-repair-scoping-2026-10-25.md`):

- **N = 9 = M + 2** (M = 7 measured lines). Per the memo's §3.1, this is
  exactly the threshold at which the per-spectrum question becomes
  answerable by direct construction: levels whose squares are `0`, `A`,
  and `A + obs m`, pairing each line to `(A + obs m, A)`. The question
  for **N ≤ 8 is not touched by this module and remains open** — a
  verdict on this instance is a verdict on this instance only.
- **ε = `clockObsErr 6` ≈ 8.87 × 10⁻¹²** — the largest of the seven
  entered published uncertainties (the ⁸⁷Sr/¹³³Cs entry; indices 0–5 are
  all ≤ 2.6 × 10⁻¹⁶), proved maximal in `clockObsErr_six_max` below.
  The tolerance is the entered table's own biggest error bar.

The construction is **exact**: the fit error is `0`, so the tolerance is
met with the whole error bar to spare. Witnesses: `β = 1`, `c = 1`,
`A = 1`, `lam = √(squares)`, each line paired to its own level against
the shared base level — one triple, one temperature, matching all seven
lines simultaneously, as the question demands.
-/

namespace ThetLogos

/-- The level squares of the fit: `0`, the shared base `1`, and
    `1 + obs m` for each measured line `m`. -/
noncomputable def clockFitSq : Fin 9 → ℝ :=
  ![0, 1, 1 + (clockObs 0 : ℝ), 1 + (clockObs 1 : ℝ), 1 + (clockObs 2 : ℝ),
    1 + (clockObs 3 : ℝ), 1 + (clockObs 4 : ℝ), 1 + (clockObs 5 : ℝ),
    1 + (clockObs 6 : ℝ)]

/-- The Dirac spectrum of the fit: square roots of `clockFitSq`. -/
noncomputable def clockFitLam : Fin 9 → ℝ := fun k => Real.sqrt (clockFitSq k)

/-- The line assignment: line `m` is paired to its own level `m + 2`
    against the shared base level `1`. -/
def clockFitF : Fin 7 → Fin 9 × Fin 9 :=
  fun m => (⟨m.val + 2, by have h := m.isLt; omega⟩, ⟨1, by norm_num⟩)

/-- Every entered ratio is nonnegative (in fact positive) — checked
    entry by entry against the entered table. -/
lemma clockObs_nonneg : ∀ m : Fin 7, (0 : ℝ) ≤ (clockObs m : ℝ) := by
  intro m
  fin_cases m <;> norm_num [clockObs]

/-- The chosen tolerance is nonnegative. -/
lemma clockObsErr_six_nonneg : (0 : ℝ) ≤ (clockObsErr 6 : ℝ) := by
  have h : (0 : ℚ) ≤ clockObsErr 6 := by norm_num [clockObsErr]
  exact_mod_cast h

/-- The chosen tolerance is the largest entered uncertainty:
    `clockObsErr 6` dominates every `clockObsErr m` — checked entry by
    entry against the entered table. -/
lemma clockObsErr_six_max : ∀ m : Fin 7, clockObsErr m ≤ clockObsErr 6 := by
  intro m
  fin_cases m <;> norm_num [clockObsErr]

/-- The first component of the fit pairing lands on the level whose
    square is `1 + obs m`. -/
lemma clockFitSq_fst (m : Fin 7) :
    clockFitSq (clockFitF m).1 = 1 + (clockObs m : ℝ) := by
  fin_cases m <;> simp [clockFitSq, clockFitF]

/-- The second component of the fit pairing lands on the base level,
    whose square is `1`. -/
lemma clockFitSq_snd (m : Fin 7) : clockFitSq (clockFitF m).2 = 1 := by
  fin_cases m <;> simp [clockFitSq, clockFitF]

/-- **Q1′ answered at the pre-registered instance** (N = 9, ε the
    largest entered uncertainty): the measured clock spectrum is
    reproduced *exactly* (fit error 0 ≤ ε) by one thermal triple —
    `β = 1`, `lam = clockFitLam`, `c = 1`, `f = clockFitF`. This is a
    verdict on this instance only; the question at N ≤ 8 stays open,
    and the original `blockedQ1` stands untouched. -/
theorem measuredClockAnswer :
    measuredClockQuestion 9 (clockObsErr 6 : ℝ) := by
  refine ⟨1, clockFitLam, 1, clockFitF, one_pos, one_ne_zero, ?_⟩
  intro m
  have h1 := clockFitSq_fst m
  have h2 := clockFitSq_snd m
  have hpos := clockObs_nonneg m
  have e1 : (clockFitLam (clockFitF m).1) ^ 2 = 1 + (clockObs m : ℝ) := by
    have hnn : (0 : ℝ) ≤ clockFitSq (clockFitF m).1 := by rw [h1]; linarith
    calc (clockFitLam (clockFitF m).1) ^ 2
        = clockFitSq (clockFitF m).1 := Real.sq_sqrt hnn
      _ = 1 + (clockObs m : ℝ) := h1
  have e2 : (clockFitLam (clockFitF m).2) ^ 2 = 1 := by
    have hnn : (0 : ℝ) ≤ clockFitSq (clockFitF m).2 := by rw [h2]; norm_num
    calc (clockFitLam (clockFitF m).2) ^ 2
        = clockFitSq (clockFitF m).2 := Real.sq_sqrt hnn
      _ = 1 := h2
  have hdiff : modularFreqDiff 1 clockFitLam (clockFitF m).1 (clockFitF m).2
      = (clockObs m : ℝ) := by
    rw [modularFreqDiff, e1, e2]; ring
  rw [hdiff, one_mul, sub_self, abs_zero]
  exact clockObsErr_six_nonneg

end ThetLogos
