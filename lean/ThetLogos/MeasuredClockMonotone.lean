import ThetLogos.MeasuredClockDecision7

/-!
# ThetLogos.MeasuredClockMonotone — Q1′′ decided for all N: fit iff `N ≥ 8`

**Status: the monotonicity brick. Tier T1, about Tier T4 entered
data. NO CLAIM.**

`measuredClockQuestion2` (`MeasuredClockQuestion2.lean`) — the
measured clock question with the free scale eliminated and per-line
tolerances — was decided at its threshold in
`MeasuredClockDecision7.lean`: **no fit at `N = 7`**
(`measuredClockNoFit7`), **exact fit at `N = 8`**
(`measuredClockAnswer2_8`). What was missing was the bridge between
instances: nothing in the tree said that a fit at one size pads to a
fit at every larger size, so formally the question at `N ≤ 6` stood
undecided in the record even though the direction is forced.

This module lands exactly that bridge and the decision it buys:

- `measuredClockQuestion2_succ` — one padding step: a fit at `N`
  gives a fit at `N + 1` (embed the spectrum along `Fin.castSucc`;
  the new last level is never used by the padded assignment, so
  every modular frequency difference the assignment reads is
  preserved exactly, with the same `β` and the same tolerances).
- `measuredClockQuestion2_add` / `measuredClockQuestion2_of_le` —
  the padding iterated: a fit at `M` gives a fit at every `N ≥ M`.
- `measuredClockQuestion2_iff_eight_le` — **the decision, for
  every `N`**:
  `measuredClockQuestion2 N ↔ 8 ≤ N`. Forward: a fit at `N ≤ 7`
  pads up to a fit at `7`, contradicting `measuredClockNoFit7`.
  Backward: the exact fit at `8` pads up to every `N ≥ 8`.

## On `N = 0`

The definition of `measuredClockQuestion2` carries the instance
argument `[NeZero N]`, so the question at `N = 0` cannot even be
posed in that form — there is no thermal triple on a 0-dimensional
space, and the instance is the record's way of saying so. The
decision above is stated for every `N` at which the question is
posed (any `N` carrying `[NeZero N]`). For comparison only: the
right-hand side at `N = 0` reads `8 ≤ 0`, which is false — the
threshold statement and the unposability agree that there is no
fit at the bottom.

## The fence

The clock table (`clockObs`, `clockObsErr`) is **Tier T4 INPUT** —
measured ratios from the CIPM compilation entered in
`MeasuredClockSpectrum.lean`, not derived and not proved. This
module decides a finite fit question about that table, for all `N`,
and nothing else. "Thermal time is physical time" as a claim about
physics remains **Tier T5 interpretation**, untouched here. Dial 1
does **not** move: the ratios were inputs, and the spectra in the
witnesses were chosen to fit them — a construction, not a
derivation of a measured number. **NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

/-- The padded spectrum: the levels of `Fin N` keep their values
    along `Fin.castSucc`, and the new last level of `Fin (N + 1)` is
    set to `0`. A padded assignment never reads the last level, so
    the value placed there is immaterial to every fit. -/
noncomputable def paddedSpectrum {N : ℕ} (lam : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  fun i => if h : i.val < N then lam ⟨i.val, h⟩ else 0

/-- The padded spectrum agrees with the original spectrum on every
    embedded level. -/
theorem paddedSpectrum_castSucc {N : ℕ} (lam : Fin N → ℝ) (i : Fin N) :
    paddedSpectrum lam (Fin.castSucc i) = lam i := by
  unfold paddedSpectrum
  split
  · congr 1
  · exact absurd i.isLt ‹_›

/-- **One padding step.** A measured-clock fit at `N` levels gives
    a fit at `N + 1` levels: same inverse temperature, the spectrum
    embedded along `Fin.castSucc`, the assignment composed with
    `Fin.castSucc` on both components. Every modular frequency
    difference the assignment reads is preserved exactly, so each
    line still lands within its own entered tolerance. -/
theorem measuredClockQuestion2_succ {N : ℕ} [NeZero N]
    (h : measuredClockQuestion2 N) : measuredClockQuestion2 (N + 1) := by
  obtain ⟨β, lam, f, hβ, hf⟩ := h
  refine ⟨β, paddedSpectrum lam,
    fun m => (Fin.castSucc (f m).1, Fin.castSucc (f m).2), hβ, fun m => ?_⟩
  have key : modularFreqDiff β (paddedSpectrum lam) (Fin.castSucc (f m).1)
        (Fin.castSucc (f m).2)
      = modularFreqDiff β lam (f m).1 (f m).2 := by
    unfold modularFreqDiff
    rw [paddedSpectrum_castSucc, paddedSpectrum_castSucc]
  rw [key]
  exact hf m

/-- **Padding, iterated.** A measured-clock fit at `N` levels gives
    a fit at `N + k` levels, for every `k`. -/
theorem measuredClockQuestion2_add {N : ℕ} [NeZero N] (k : ℕ)
    (h : measuredClockQuestion2 N) : measuredClockQuestion2 (N + k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hNk : N + k ≠ 0 := fun h0 => NeZero.ne N (by omega)
    exact @measuredClockQuestion2_succ (N + k) ⟨hNk⟩ ih

/-- **Monotonicity.** A measured-clock fit at `M` levels gives a fit
    at every `N ≥ M`. -/
theorem measuredClockQuestion2_of_le {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ≤ N)
    (h : measuredClockQuestion2 M) : measuredClockQuestion2 N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = M + k := ⟨N - M, by omega⟩
  exact measuredClockQuestion2_add k h

/-- **Q1′′ decided for all `N`.** The measured clock question with
    the scale eliminated and per-line tolerances — seven entered
    CIPM clock ratios, each to be reproduced by a modular frequency
    difference within its own entered uncertainty — has a fit if
    and only if the spectrum has at least eight levels:
    `measuredClockQuestion2 N ↔ 8 ≤ N`, for every `N` at which the
    question is posed (the definition carries `[NeZero N]`; see the
    module header on `N = 0`). The threshold is
    `measuredClockNoFit7` from below and `measuredClockAnswer2_8`
    from above, joined by monotonicity. -/
theorem measuredClockQuestion2_iff_eight_le {N : ℕ} [NeZero N] :
    measuredClockQuestion2 N ↔ 8 ≤ N := by
  constructor
  · intro h
    by_contra hcon
    have h7 : measuredClockQuestion2 7 :=
      measuredClockQuestion2_of_le (N := 7) (by omega) h
    exact measuredClockNoFit7 h7
  · intro h8
    exact measuredClockQuestion2_of_le h8 measuredClockAnswer2_8

/-- **No fit below the threshold.** For every `N` with `1 ≤ N ≤ 7`
    at which the question is posed, there is no measured-clock fit.
    (The `N = 7` case is `measuredClockNoFit7`; the rest is
    monotonicity read backwards.) -/
theorem measuredClockQuestion2_not_of_lt {N : ℕ} [NeZero N] (hN : N < 8) :
    ¬ measuredClockQuestion2 N := by
  intro h
  have h8 : 8 ≤ N := measuredClockQuestion2_iff_eight_le.mp h
  exact absurd h8 (by omega)

end ThetLogos
