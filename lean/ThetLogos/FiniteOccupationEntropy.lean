import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ThetLogos.FiniteEntropy
import ThetLogos.FiniteOccupationEntropyPin

namespace ThetLogos

/-!
# ThetLogos.FiniteOccupationEntropy — AB-7 content

Occupation entropy of `N` two-level sites: maximum at half occupation,
closed-form forward difference, sign corollaries, endpoint exhibits, and
the bridge to the landed `entropyW` seat.

**Status: THEOREMS (this module). NO CLAIM. Dials 0/4. Dial-ineligible** —
a finite counting brick (see the pin,
`ThetLogos.FiniteOccupationEntropyPin`, for the commission, the price,
and the fences). The final four theorems prove the pin's frozen forms
verbatim.

Kills: K-AB7-DUP / K-AB7-FIAT / K-AB7-BOUND armed at the pin; none fired.
The sign corollaries are bare sign facts about a log-ratio of counting
numbers; no other vocabulary appears in any statement.
-/

/-- The occupation entropy is nonnegative: the microstate count is a
    natural number, so its logarithm is `0` (count `0` or `1`) or
    positive. Tier T1. -/
theorem occEntropy_nonneg (N k : ℕ) : 0 ≤ occEntropy N k := by
  rcases Nat.eq_zero_or_pos (Nat.choose N k) with h | h
  · have hz : occEntropy N k = 0 := by
      simp [occEntropy, h]
    rw [hz]
  · unfold occEntropy
    apply Real.log_nonneg
    exact_mod_cast h

/-- **Form (1): maximum at half occupation.** `occEntropy N k` is at most
    `occEntropy N (N / 2)` — `Nat.choose_le_middle` read through `log`.
    Tier T1. -/
theorem occEntropy_le_middle (N k : ℕ) :
    occEntropy N k ≤ occEntropy N (N / 2) := by
  rcases Nat.eq_zero_or_pos (Nat.choose N k) with h | h
  · have hz : occEntropy N k = 0 := by
      simp [occEntropy, h]
    rw [hz]
    exact occEntropy_nonneg N _
  · unfold occEntropy
    apply Real.log_le_log (by exact_mod_cast h)
    exact_mod_cast Nat.choose_le_middle k N

/-- **Form (2): forward difference, closed form.** For `k < N`,
    `occEntropy N (k + 1) − occEntropy N k = log ((N − k) / (k + 1))`,
    from `Nat.choose_succ_right_eq` cast to `ℝ`. Tier T1. -/
theorem occEntropy_succ_sub {N k : ℕ} (hk : k < N) :
    occEntropy N (k + 1) - occEntropy N k
      = Real.log ((N - k : ℝ) / (k + 1)) := by
  have hkN : k ≤ N := hk.le
  have hB : (0 : ℝ) < Nat.choose N k := by
    exact_mod_cast Nat.choose_pos hkN
  have hNk : (0 : ℝ) < (N : ℝ) - k := by
    have hlt : (k : ℝ) < N := by exact_mod_cast hk
    linarith
  have key : (Nat.choose N (k + 1) : ℝ) * ((k : ℝ) + 1)
      = (Nat.choose N k : ℝ) * ((N : ℝ) - k) := by
    have h : ((Nat.choose N (k + 1) * (k + 1) : ℕ) : ℝ)
        = ((Nat.choose N k * (N - k) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq N k
    push_cast [Nat.cast_sub hkN] at h
    exact h
  have hA : (0 : ℝ) < Nat.choose N (k + 1) := by
    by_contra hcon
    push_neg at hcon
    have hle : (Nat.choose N (k + 1) : ℝ) * ((k : ℝ) + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon (by positivity)
    rw [key] at hle
    exact not_lt_of_ge hle (mul_pos hB hNk)
  have hdiv : (Nat.choose N (k + 1) : ℝ) / Nat.choose N k
      = ((N : ℝ) - k) / ((k : ℝ) + 1) := by
    rw [div_eq_div_iff hB.ne' (by positivity : ((k : ℝ) + 1) ≠ 0)]
    rw [key]
    ring
  unfold occEntropy
  rw [← Real.log_div hA.ne' hB.ne', hdiv]

/-- **Form (3), below the middle step:** if `k + 1 < N − k`, the forward
    difference is positive (the ratio exceeds `1`). Tier T1. -/
theorem occEntropy_succ_sub_pos {N k : ℕ} (hk : k < N)
    (h : k + 1 < N - k) :
    0 < occEntropy N (k + 1) - occEntropy N k := by
  rw [occEntropy_succ_sub hk]
  apply Real.log_pos
  rw [one_lt_div (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  have h' : ((k + 1 : ℕ) : ℝ) < ((N - k : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hk.le] at h'
  push_cast at h'
  linarith

/-- **Form (3), past the middle step:** if `N − k < k + 1`, the forward
    difference is negative (the ratio is below `1`). Tier T1. -/
theorem occEntropy_succ_sub_neg {N k : ℕ} (hk : k < N)
    (h : N - k < k + 1) :
    occEntropy N (k + 1) - occEntropy N k < 0 := by
  rw [occEntropy_succ_sub hk]
  apply Real.log_neg
  · apply div_pos _ (by positivity : (0 : ℝ) < (k : ℝ) + 1)
    have hlt : (k : ℝ) < N := by exact_mod_cast hk
    linarith
  · rw [div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    have h' : ((N - k : ℕ) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_sub hk.le] at h'
    push_cast at h'
    linarith

/-- **Form (3), at the middle step:** if `N − k = k + 1`, the forward
    difference is zero (the ratio is `1`). Tier T1. -/
theorem occEntropy_succ_sub_eq_zero {N k : ℕ} (h : N - k = k + 1) :
    occEntropy N (k + 1) - occEntropy N k = 0 := by
  have hk : k < N := by omega
  rw [occEntropy_succ_sub hk]
  have h' : ((N - k : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hk.le] at h'
  push_cast at h'
  rw [h', div_self (by positivity : ((k : ℝ) + 1) ≠ 0), Real.log_one]

/-- Endpoint exhibit: at occupation `0` there is one configuration, so
    the occupation entropy is `0`. Tier T1. -/
theorem occEntropy_zero_right (N : ℕ) : occEntropy N 0 = 0 := by
  simp [occEntropy]

/-- Endpoint exhibit: at full occupation there is one configuration, so
    the occupation entropy is `0`. Tier T1. -/
theorem occEntropy_self (N : ℕ) : occEntropy N N = 0 := by
  simp [occEntropy]

/-- **Form (4): bridge to the landed `entropyW` seat.** For `k ≤ N`,
    `occEntropy N k` is the `entropyW` of the uniform weight `1 / card`
    on the type of `k`-subsets of `Fin N` — the landed saturation
    theorem `entropyW_eq_log_card_iff` evaluated at that weight, with
    the type's cardinality computed as `Nat.choose N k`. Tier T1. -/
theorem occEntropy_eq_entropyW_uniform {N k : ℕ} (hk : k ≤ N) :
    occEntropy N k =
      entropyW (fun _ : ↥(Finset.powersetCard k
          (Finset.univ : Finset (Fin N))) =>
        1 / (Fintype.card ↥(Finset.powersetCard k
          (Finset.univ : Finset (Fin N))) : ℝ)) := by
  have hcard : Fintype.card ↥(Finset.powersetCard k
      (Finset.univ : Finset (Fin N))) = Nat.choose N k := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin]
  have hpos : 0 < Nat.choose N k := Nat.choose_pos hk
  have hprob : IsProbWeight (fun _ : ↥(Finset.powersetCard k
      (Finset.univ : Finset (Fin N))) =>
        1 / (Fintype.card ↥(Finset.powersetCard k
          (Finset.univ : Finset (Fin N))) : ℝ)) := by
    constructor
    · intro _
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      exact mul_one_div_cancel (by exact_mod_cast hpos.ne')
  have h := (entropyW_eq_log_card_iff hprob).mpr (fun _ => rfl)
  rw [hcard] at h ⊢
  exact h.symm

/-- The pin's frozen form (1), proved. Tier T1. -/
theorem occEntropy_max_at_half : occEntropyMaxAtHalfForm :=
  fun N k => occEntropy_le_middle N k

/-- The pin's frozen form (2), proved. Tier T1. -/
theorem occEntropy_step : occEntropyStepForm :=
  fun N k hk => occEntropy_succ_sub hk

/-- The pin's frozen form (3), proved. Tier T1. -/
theorem occEntropy_step_signs : occEntropyStepSignsForm :=
  ⟨fun N k hk h => occEntropy_succ_sub_pos hk h,
   fun N k hk h => occEntropy_succ_sub_neg hk h,
   fun N k h => occEntropy_succ_sub_eq_zero h⟩

/-- The pin's frozen form (4), proved. Tier T1. -/
theorem occEntropy_bridge : occEntropyBridgeForm :=
  fun N k hk => occEntropy_eq_entropyW_uniform hk

end ThetLogos
