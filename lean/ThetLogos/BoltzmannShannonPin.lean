import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ThetLogos

/-!
# ThetLogos.BoltzmannShannonPin — the Boltzmann–Shannon finite identity (MCC seed brick)

**Commission:** Zero, 2026-11-19 10:23 EST ("Build the Boltzmann–Shannon
finite pin"), from the MCC registry seed
(`mcc-registry-seed-six-traditions-2026-11-19.md`, Entries 5–6 and the seed
correspondence table), under the compiled charter
(`mathematical-correspondence-comparison-compiled-2026-11-19.md`).

**What this pin is.** The seed found exactly one correspondence among the
six traditions that is exact and cheap: Boltzmann ↔ Shannon. On a finite
seat the two entropy functionals are related by pure base change, and at
the uniform distribution both collapse to the logarithm of the number of
states. This pin proves exactly that finite identity:

* `gibbsEntropy p = Real.log 2 * shannonEntropy p` for **every** `p`
  (no side conditions — the base change is termwise);
* at the uniform distribution on `Fin n` (`n ≥ 1`),
  `gibbsEntropy = Real.log n` and `shannonEntropy = Real.logb 2 n`;
* the Planck form as a corollary: `k * gibbsEntropy (uniform) = k * Real.log n`
  — the finite shadow of `S = k log W`;
* `gibbsEntropy` is nonnegative on probability distributions.

**K-BS-COSTUME fence (pre-registered, on the face).** This pin proves a
finite identity between two entropy functionals. It does NOT establish a
physical correspondence between Boltzmann's thermodynamics and Shannon's
information theory, it is NOT a TST claim, and it moves no dial.
**NO CLAIM; dials 0/4; lane grade; rides the next integration tranche.**

**The log-0 convention, stated openly.** In Mathlib, `Real.log 0 = 0` and
`Real.logb b 0 = 0`, so a zero-probability term contributes
`0 * 0 = 0` to both functionals — the terms vanish on their own, and the
bridge identity below is proved termwise for every real argument, so it
needs no side condition anywhere. The uniform-distribution theorems only
ever evaluate the functionals at `(n : ℝ)⁻¹ > 0`.
-/

/-- Gibbs entropy of a finite weight function `p`: `-∑ i, p i * log (p i)`
(natural logarithm). Zero-probability terms vanish by Mathlib's
`Real.log 0 = 0` convention. -/
noncomputable def gibbsEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- Shannon entropy of a finite weight function `p`, in bits:
`-∑ i, p i * logb 2 (p i)`. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ i, p i * Real.logb 2 (p i)

/-- The uniform distribution on `Fin n`: every state carries weight
`(n : ℝ)⁻¹`. -/
noncomputable def uniformProb (n : ℕ) : Fin n → ℝ :=
  fun _ => (n : ℝ)⁻¹

/-- BRIDGE: the Gibbs and Shannon functionals differ only by the constant
base-change factor `Real.log 2`, for **every** weight function `p`, with no
side conditions. Termwise this is `log x = log 2 * logb 2 x`, pure algebra
off `Real.log 2 ≠ 0`, valid at `x = 0` by the `log 0 = 0` convention. -/
theorem gibbsEntropy_eq_log_two_mul_shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) :
    gibbsEntropy p = Real.log 2 * shannonEntropy p := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hterm : ∀ x : ℝ, Real.log x = Real.log 2 * Real.logb 2 x := by
    intro x
    rw [Real.logb]
    field_simp
  have hsum : (∑ i, p i * Real.log (p i)) = Real.log 2 * ∑ i, p i * Real.logb 2 (p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm (p i)]
    ring
  simp only [gibbsEntropy, shannonEntropy]
  rw [hsum, mul_neg]

/-- HEADLINE: the Gibbs entropy of the uniform distribution on `Fin n`
(`n ≥ 1`) is exactly `Real.log n` — the finite Boltzmann relation
`S ∝ log W` at `W = n`, with proportionality constant 1 in natural-log
units. -/
theorem gibbsEntropy_uniform (n : ℕ) (hn : 1 ≤ n) :
    gibbsEntropy (uniformProb n) = Real.log n := by
  have hn' : n ≠ 0 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn'
  simp only [gibbsEntropy, uniformProb]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hn0, one_mul, Real.log_inv, neg_neg]

/-- The Shannon entropy of the uniform distribution on `Fin n` (`n ≥ 1`)
is exactly `Real.logb 2 n` — the state count in bits. Proved through the
bridge and the headline, cancelling the nonzero factor `Real.log 2`. -/
theorem shannonEntropy_uniform (n : ℕ) (hn : 1 ≤ n) :
    shannonEntropy (uniformProb n) = Real.logb 2 n := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h := gibbsEntropy_uniform n hn
  rw [gibbsEntropy_eq_log_two_mul_shannonEntropy] at h
  have hterm : Real.log (n : ℝ) = Real.log 2 * Real.logb 2 (n : ℝ) := by
    rw [Real.logb]
    field_simp
  rw [hterm] at h
  exact mul_left_cancel₀ h2 h

/-- PLANCK FORM (corollary): for any constant `k`, the `k`-scaled Gibbs
entropy of the uniform distribution on `Fin n` (`n ≥ 1`) is
`k * Real.log n` — the finite seat of `S = k log W` (whose exact form, per
the registry seed Entry 5, is Planck's formulation of Boltzmann's
proportionality). -/
theorem planck_entropy_uniform (k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    k * gibbsEntropy (uniformProb n) = k * Real.log n := by
  rw [gibbsEntropy_uniform n hn]

/-- The Gibbs entropy of a probability distribution is nonnegative.
The package hypothesis `_hsum` (the weights sum to 1) is carried as part
of what "probability distribution" means; the bound itself needs only the
pointwise hypotheses — each term satisfies `p i * log (p i) ≤ 0` because
`0 ≤ p i ≤ 1` forces `log (p i) ≤ 0`, the `p i = 0` term included by the
`log 0 = 0` convention. Disclosed on the face, per house precedent. -/
theorem gibbsEntropy_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) (_hsum : ∑ i, p i = 1) :
    0 ≤ gibbsEntropy p := by
  simp only [gibbsEntropy]
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos (h0 i) (Real.log_nonpos (h0 i) (h1 i))

end ThetLogos
