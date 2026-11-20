/-
# WP2 character route, Module B, brick B1d — the column
# expansion (scope §3, B1 headline)

For `β ≥ 0`, the column weight is a finite nonnegative
combination of the irreducible characters over τ:

  `exp (-β * gramDens ρ g)
     = ∑_{χ ∈ τ} (coeff χ) • χ g`,

  `coeff χ = e^{-β} ∑'_m (β/d)^m/m! · 2^{-m} ·
     ∑_{a+b=m} (m.choose a) · mult_χ (a, b) ≥ 0`,

where `mult` is B1c's word multiplicity.  The proof is the
pointwise `exp` series in `Re χ = (χ + χ̄)/2`, regrouped
by B1c: absolute convergence from `mult_χ (a, b) ≤ d^{a+b}`
(the majorant collapses to `β^m/m!`).  No `d = 0` case
split in the statement: Lean's junk division makes both
sides agree there (`charFn = 0`, `gramDens = 1`,
`(β/0)^m = 0` for `m ≥ 1`, `mult (a, b) = 0` for
`a + b ≥ 1` — the last because at `d = 0` every word
character with `a + b ≥ 1` vanishes, so no constituent
contributes to it).

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelWordDecomp
import ThetLogos.LayerKernelGramCert

open Finset
open scoped Matrix

namespace ThetLogos

section ColumnExpansion

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [TopologicalSpace G] [DiscreteTopology G]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The word multiplicity, chosen once and for all from
B1c's decomposition (per `(a, b)`). -/
noncomputable def wordMult (χ : G → ℂ) (a b : ℕ) : ℕ :=
  Classical.choose (word_decomp ρ a b) χ

theorem wordMult_apply (a b : ℕ) (g : G) :
    charFn ρ g ^ a * star (charFn ρ g) ^ b
      = ∑ χ ∈ irredCharSet_finite.toFinset,
        (wordMult ρ χ a b : ℂ) * χ g :=
  (Classical.choose_spec (word_decomp ρ a b)).1 g

theorem wordMult_le (a b : ℕ) (χ : G → ℂ) :
    wordMult ρ χ a b ≤ d ^ (a + b) :=
  (Classical.choose_spec (word_decomp ρ a b)).2 χ

/-- The antidiagonal multiplicity sum, as a real number:
`S_m χ = ∑_{a+b=m} (m.choose a) · mult_χ (a, b)`. -/
noncomputable def multSum (χ : G → ℂ) (m : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal m,
    ((m.choose p.1 : ℕ) : ℝ) * (wordMult ρ χ p.1 p.2 : ℝ)

/-- The bound on the antidiagonal sum: `S_m χ ≤ d^m · 2^m`,
from `mult_χ (a, b) ≤ d^{a+b}` and `∑_a (m.choose a) = 2^m`. -/
theorem multSum_le (χ : G → ℂ) (m : ℕ) :
    multSum ρ χ m ≤ (d : ℝ) ^ m * 2 ^ m := by
  have h1 : ∀ p ∈ Finset.antidiagonal m,
      ((m.choose p.1 : ℕ) : ℝ) * (wordMult ρ χ p.1 p.2 : ℝ)
        ≤ ((m.choose p.1 : ℕ) : ℝ) * (d : ℝ) ^ m := by
    intro p hp
    have hpm : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    have hle : wordMult ρ χ p.1 p.2 ≤ d ^ m := by
      rw [← hpm]
      exact wordMult_le ρ p.1 p.2 χ
    have hcast : (wordMult ρ χ p.1 p.2 : ℝ) ≤ (d : ℝ) ^ m := by
      have h2 : (wordMult ρ χ p.1 p.2 : ℝ) ≤ ((d ^ m : ℕ) : ℝ) :=
        Nat.cast_le.mpr hle
      rwa [Nat.cast_pow] at h2
    exact mul_le_mul_of_nonneg_left hcast
      (Nat.cast_nonneg _)
  calc multSum ρ χ m
      ≤ ∑ _p ∈ Finset.antidiagonal m, (d : ℝ) ^ m
          * ((m.choose _p.1 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have h := h1 p hp
        rwa [mul_comm (((m.choose p.1 : ℕ) : ℝ)) ((d : ℝ) ^ m)] at h
    _ = (d : ℝ) ^ m * ∑ p ∈ Finset.antidiagonal m,
          ((m.choose p.1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
    _ = (d : ℝ) ^ m * 2 ^ m := by
        congr 1
        have h := Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a _b => ((m.choose a : ℕ) : ℝ)) m
        rw [h]
        have h2 : ∀ k ∈ Finset.range (m + 1),
            ((m.choose k : ℕ) : ℝ) = ((m.choose k : ℕ) : ℝ) := fun k _ => rfl
        have h3 : (∑ k ∈ Finset.range (m + 1),
            ((m.choose k : ℕ) : ℝ)) = (2 : ℝ) ^ m := by
          exact_mod_cast Nat.sum_range_choose m
        exact h3

/-- The column coefficient of `χ` at `β`:
`e^{-β} ∑'_m (β/d)^m/m! · 2^{-m} · S_m χ`. -/
noncomputable def colCoeff (β : ℝ) (χ : G → ℂ) : ℝ :=
  Real.exp (-β) * ∑' m : ℕ, (β / (d : ℝ)) ^ m / (m.factorial : ℝ)
    * (2 : ℝ)⁻¹ ^ m * multSum ρ χ m
/-- The absolute value of the `m`-th series term, in
positive form. -/
theorem colTerm_abs (β : ℝ) (χ : G → ℂ) (m : ℕ) :
    |(β / (d : ℝ)) ^ m / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
        * multSum ρ χ m|
      = (|β| / (d : ℝ)) ^ m / (m.factorial : ℝ)
        * (2 : ℝ)⁻¹ ^ m * multSum ρ χ m := by
  have hS : 0 ≤ multSum ρ χ m := by
    rw [multSum]
    refine Finset.sum_nonneg fun p _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hdnn : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  have hfnn : |((m.factorial : ℕ) : ℝ)| = (m.factorial : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_div, hdnn, hfnn,
    abs_pow, abs_inv, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hS]

/-- The real majorant bound: the `m`-th series term is at
most `|β|^m / m!` in absolute value. -/
theorem colTerm_bound (β : ℝ) (χ : G → ℂ) (m : ℕ) :
    ‖(β / (d : ℝ)) ^ m / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
        * multSum ρ χ m‖
      ≤ |β| ^ m / (m.factorial : ℝ) := by
  have hSle := multSum_le ρ χ m
  rw [Real.norm_eq_abs, colTerm_abs]
  by_cases hd0 : d = 0
  · subst hd0
    by_cases hm : m = 0
    · subst hm
      have hms : multSum ρ χ 0 = (wordMult ρ χ 0 0 : ℝ) := by
        simp [multSum, Finset.Nat.antidiagonal_zero]
      have hle : wordMult ρ χ 0 0 ≤ 1 := by
        have h := wordMult_le ρ 0 0 χ
        simpa using h
      have hle2 : (wordMult ρ χ 0 0 : ℝ) ≤ 1 := by exact_mod_cast hle
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        mul_one, one_mul, hms]
      exact hle2
    · have h1 : (|β| / ((0 : ℕ) : ℝ)) ^ m = 0 := by
        rw [Nat.cast_zero, div_zero, zero_pow hm]
      rw [h1]
      simp only [zero_div, zero_mul]
      exact div_nonneg (pow_nonneg (abs_nonneg _) _)
        (Nat.cast_nonneg _)
  · have hdpos : (0 : ℝ) < (d : ℝ) := by
      have h : 0 < d := Nat.pos_of_ne_zero hd0
      exact_mod_cast h
    have hdf : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    have hff : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    have hprod : (|β| / (d : ℝ)) ^ m / (m.factorial : ℝ)
        * (2 : ℝ)⁻¹ ^ m * ((d : ℝ) ^ m * 2 ^ m)
        = |β| ^ m / (m.factorial : ℝ) := by
      calc (|β| / (d : ℝ)) ^ m / (m.factorial : ℝ)
            * (2 : ℝ)⁻¹ ^ m * ((d : ℝ) ^ m * 2 ^ m)
          = ((|β| / (d : ℝ)) ^ m * (d : ℝ) ^ m)
              * ((2 : ℝ)⁻¹ ^ m * 2 ^ m) / (m.factorial : ℝ) := by ring
        _ = (|β| ^ m * 1) / (m.factorial : ℝ) := by
            rw [← mul_pow, div_mul_cancel₀ _ hdf, ← mul_pow,
              show (2 : ℝ)⁻¹ * 2 = 1 from
                inv_mul_cancel₀ (by norm_num), one_pow]
        _ = |β| ^ m / (m.factorial : ℝ) := by rw [mul_one]
    calc (|β| / (d : ℝ)) ^ m / (m.factorial : ℝ)
          * (2 : ℝ)⁻¹ ^ m * multSum ρ χ m
        ≤ (|β| / (d : ℝ)) ^ m / (m.factorial : ℝ)
          * (2 : ℝ)⁻¹ ^ m * ((d : ℝ) ^ m * 2 ^ m) :=
          mul_le_mul_of_nonneg_left hSle (by positivity)
      _ = |β| ^ m / (m.factorial : ℝ) := hprod

/-- The column series is summable (majorized by the
exponential series). -/
theorem colCoeff_summable (β : ℝ) (χ : G → ℂ) :
    Summable (fun m : ℕ => (β / (d : ℝ)) ^ m / (m.factorial : ℝ)
      * (2 : ℝ)⁻¹ ^ m * multSum ρ χ m) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial |β|)
    (colTerm_bound ρ β χ)

/-- For `β ≥ 0` the column coefficient is nonnegative. -/
theorem colCoeff_nonneg {β : ℝ} (hβ : 0 ≤ β) (χ : G → ℂ) :
    0 ≤ colCoeff ρ β χ := by
  refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun m => ?_)
  refine mul_nonneg (mul_nonneg ?_ (by positivity)) ?_
  · exact div_nonneg (pow_nonneg (div_nonneg hβ
      (Nat.cast_nonneg _)) _) (Nat.cast_nonneg _)
  · rw [multSum]
    refine Finset.sum_nonneg fun p _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The column expansion** (scope §3, B1 headline): for
`β ≥ 0`, the column weight `exp (-β * gramDens ρ g)` is
the finite nonnegative combination
`∑_{χ ∈ τ} (coeff χ) • χ g` of the irreducible characters,
with `coeff = colCoeff` as above. -/
theorem column_expansion {β : ℝ} (hβ : 0 ≤ β) (g : G) :
    ((Real.exp (-β * gramDens ρ g) : ℝ) : ℂ)
      = ∑ χ ∈ irredCharSet_finite.toFinset,
        (colCoeff ρ β χ : ℂ) * χ g := by
  classical
  set χg := charFn ρ g with hχg
  -- the real part of the character, in complex form
  have hre : ((charFn ρ g).re : ℂ) = (χg + star χg) / 2 := by
    have h := Complex.add_conj χg
    rw [starRingEnd_apply] at h
    have h2 : ((2 * (χg).re : ℝ) : ℂ) = 2 * ((χg).re : ℂ) := by
      push_cast
      ring
    rw [h2] at h
    rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), h, mul_comm]
  -- the exponent, regrouped
  have harg : ((-β * gramDens ρ g : ℝ) : ℂ)
      = -(β : ℂ) + (β : ℂ) * (χg + star χg) / (2 * (d : ℂ)) := by
    rw [gramDens]
    push_cast
    rw [hre]
    ring
  -- the exp series of the regrouped exponent
  have hexp : Complex.exp ((β : ℂ) * (χg + star χg) / (2 * (d : ℂ)))
      = ∑' m : ℕ, ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
          * (2 : ℂ)⁻¹ ^ m * (χg + star χg) ^ m := by
    have hw : (β : ℂ) * (χg + star χg) / (2 * (d : ℂ))
        = ((β : ℂ) / (d : ℂ)) * (2 : ℂ)⁻¹ * (χg + star χg) := by ring
    have h : Complex.exp (((β : ℂ) / (d : ℂ)) * (2 : ℂ)⁻¹
        * (χg + star χg))
        = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
            • (((β : ℂ) / (d : ℂ)) * (2 : ℂ)⁻¹ * (χg + star χg)) ^ m := by
      have h2 := congrFun (NormedSpace.exp_eq_tsum ℂ)
        (((β : ℂ) / (d : ℂ)) * (2 : ℂ)⁻¹ * (χg + star χg))
      have h3 : Complex.exp (((β : ℂ) / (d : ℂ)) * (2 : ℂ)⁻¹
          * (χg + star χg))
          = NormedSpace.exp (((β : ℂ) / (d : ℂ)) * (2 : ℂ)⁻¹
            * (χg + star χg)) :=
        congrFun Complex.exp_eq_exp_ℂ _
      rwa [h3]
    rw [hw, h]
    refine tsum_congr fun m => ?_
    rw [smul_eq_mul, mul_pow, mul_pow, div_eq_mul_inv]
    ring
  -- per-`m` regrouping over τ (finite manipulations only)
  have hcast : ∀ χ : G → ℂ, ∀ m : ℕ, ((multSum ρ χ m : ℝ) : ℂ)
      = ∑ p ∈ Finset.antidiagonal m,
          ((m.choose p.1 : ℂ)) * (wordMult ρ χ p.1 p.2 : ℂ) := by
    intro χ m
    rw [multSum]
    push_cast
    rfl
  have hper : ∀ m : ℕ, ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
        * (2 : ℂ)⁻¹ ^ m * (χg + star χg) ^ m
      = ∑ χ ∈ irredCharSet_finite.toFinset,
          ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
            * ((multSum ρ χ m : ℝ) : ℂ) * χ g := by
    intro m
    have hanti : (χg + star χg) ^ m
        = ∑ p ∈ Finset.antidiagonal m,
            ((m.choose p.1 : ℂ)) * (χg ^ p.1 * (star χg) ^ p.2) := by
      rw [Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => ((m.choose a : ℂ)) * (χg ^ a * (star χg) ^ b)) m,
        add_pow]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hexp2 : ∀ p ∈ Finset.antidiagonal m,
        ((m.choose p.1 : ℂ)) * (χg ^ p.1 * (star χg) ^ p.2)
        = ∑ χ ∈ irredCharSet_finite.toFinset,
            ((m.choose p.1 : ℂ)) * ((wordMult ρ χ p.1 p.2 : ℂ) * χ g) := by
      intro p _
      rw [wordMult_apply ρ p.1 p.2 g, Finset.mul_sum]
    have h3 : ∀ χ ∈ irredCharSet_finite.toFinset,
        ((multSum ρ χ m : ℝ) : ℂ) * χ g
        = ∑ p ∈ Finset.antidiagonal m,
            ((m.choose p.1 : ℂ)) * ((wordMult ρ χ p.1 p.2 : ℂ) * χ g) := by
      intro χ _
      rw [hcast χ m, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by ring
    calc ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
          * (2 : ℂ)⁻¹ ^ m * (χg + star χg) ^ m
        = ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
            * ∑ χ ∈ irredCharSet_finite.toFinset,
              ((multSum ρ χ m : ℝ) : ℂ) * χ g := by
          rw [hanti, Finset.sum_congr rfl h3, ← Finset.sum_comm]
          refine congrArg _ (Finset.sum_congr rfl fun p hp => ?_)
          exact hexp2 p hp
      _ = ∑ χ ∈ irredCharSet_finite.toFinset,
            ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
              * ((multSum ρ χ m : ℝ) : ℂ) * χ g := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => by ring
  -- summability of the complex pieces
  have hFb : ∀ (χ : G → ℂ) (m : ℕ),
      ‖((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
          * ((multSum ρ χ m : ℝ) : ℂ) * χ g‖
        ≤ (|β| ^ m / (m.factorial : ℝ)) * ‖χ g‖ := by
    intro χ m
    have hnorm : ‖((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
        * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ m : ℝ) : ℂ) * χ g‖
        = (|β| / (d : ℝ)) ^ m / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
          * multSum ρ χ m * ‖χ g‖ := by
      have hFid : ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
            * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ m : ℝ) : ℂ)
          = (((β / (d : ℝ)) ^ m / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
              * multSum ρ χ m : ℝ) : ℂ) := by
        push_cast
        ring
      rw [show ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
            * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ m : ℝ) : ℂ) * χ g
          = (((β / (d : ℝ)) ^ m / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
              * multSum ρ χ m : ℝ) : ℂ) * χ g from
        congrArg (fun z => z * χ g) hFid]
      rw [norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, colTerm_abs]
    rw [hnorm]
    have hb := colTerm_bound ρ β χ m
    rw [Real.norm_eq_abs, colTerm_abs] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hF : ∀ χ : G → ℂ, Summable (fun m : ℕ =>
      ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
        * ((multSum ρ χ m : ℝ) : ℂ) * χ g) := by
    intro χ
    refine Summable.of_norm_bounded ?_ (hFb χ)
    exact (Real.summable_pow_div_factorial |β|).mul_right ‖χ g‖
  have hFsum : ∀ s : Finset (G → ℂ), Summable (fun m : ℕ =>
      ∑ χ ∈ s, ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
        * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ m : ℝ) : ℂ) * χ g) := by
    intro s
    have hb : ∀ m : ℕ, ‖∑ χ ∈ s, ((β : ℂ) / (d : ℂ)) ^ m
          / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
          * ((multSum ρ χ m : ℝ) : ℂ) * χ g‖
        ≤ (|β| ^ m / (m.factorial : ℝ)) * ∑ χ ∈ s, ‖χ g‖ := by
      intro m
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun χ _ => hFb χ m).trans_eq ?_
      rw [Finset.mul_sum]
    exact Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial |β|).mul_right
        (∑ χ ∈ s, ‖χ g‖)) hb
  -- the tsum / finite-sum swap, by Finset induction
  have hswap : ∀ s : Finset (G → ℂ),
      (∑' m : ℕ, ∑ χ ∈ s, ((β : ℂ) / (d : ℂ)) ^ m
          / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
          * ((multSum ρ χ m : ℝ) : ℂ) * χ g)
        = ∑ χ ∈ s, ∑' m : ℕ, ((β : ℂ) / (d : ℂ)) ^ m
          / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
          * ((multSum ρ χ m : ℝ) : ℂ) * χ g := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert χ s hχs ih =>
      have h1 : ∀ m : ℕ, (∑ χ' ∈ insert χ s,
            ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
              * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ' m : ℝ) : ℂ) * χ' g)
          = ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
              * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ m : ℝ) : ℂ) * χ g
            + ∑ χ' ∈ s, ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
              * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ' m : ℝ) : ℂ) * χ' g :=
        fun m => Finset.sum_insert hχs
      rw [tsum_congr h1, (hF χ).tsum_add (hFsum s), ih,
        Finset.sum_insert hχs]
  -- assembly
  calc ((Real.exp (-β * gramDens ρ g) : ℝ) : ℂ)
      = Complex.exp (-(β : ℂ)
          + (β : ℂ) * (χg + star χg) / (2 * (d : ℂ))) := by
        rw [Complex.ofReal_exp, harg]
    _ = Complex.exp (-(β : ℂ))
          * Complex.exp ((β : ℂ) * (χg + star χg) / (2 * (d : ℂ))) :=
        Complex.exp_add _ _
    _ = Complex.exp (-(β : ℂ))
          * ∑' m : ℕ, ∑ χ ∈ irredCharSet_finite.toFinset,
            ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
              * ((multSum ρ χ m : ℝ) : ℂ) * χ g :=
        congrArg _ (hexp.trans (tsum_congr hper))
    _ = Complex.exp (-(β : ℂ))
          * ∑ χ ∈ irredCharSet_finite.toFinset, ∑' m : ℕ,
            ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
              * ((multSum ρ χ m : ℝ) : ℂ) * χ g :=
        congrArg _ (hswap _)
    _ = ∑ χ ∈ irredCharSet_finite.toFinset,
          (colCoeff ρ β χ : ℂ) * χ g := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        have hχ : (colCoeff ρ β χ : ℂ) * χ g
            = Complex.exp (-(β : ℂ)) * ∑' m : ℕ,
              ((β : ℂ) / (d : ℂ)) ^ m / (m.factorial : ℂ)
                * (2 : ℂ)⁻¹ ^ m * ((multSum ρ χ m : ℝ) : ℂ) * χ g := by
          calc (colCoeff ρ β χ : ℂ) * χ g
              = (Complex.exp (-(β : ℂ))
                  * ∑' m : ℕ, (((β / (d : ℝ)) ^ m
                      / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
                      * multSum ρ χ m : ℝ) : ℂ)) * χ g := by
                congr 1
                show ((Real.exp (-β) * ∑' m : ℕ, (β / (d : ℝ)) ^ m
                      / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
                      * multSum ρ χ m : ℝ) : ℂ) = _
                rw [Complex.ofReal_mul, Complex.ofReal_exp,
                  Complex.ofReal_neg, Complex.ofReal_tsum]
            _ = Complex.exp (-(β : ℂ))
                  * ((∑' m : ℕ, (((β / (d : ℝ)) ^ m
                      / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
                      * multSum ρ χ m : ℝ) : ℂ)) * χ g) :=
                mul_assoc _ _ _
            _ = Complex.exp (-(β : ℂ))
                  * ∑' m : ℕ, (((β / (d : ℝ)) ^ m
                      / (m.factorial : ℝ) * (2 : ℝ)⁻¹ ^ m
                      * multSum ρ χ m : ℝ) : ℂ) * χ g :=
                congrArg (fun z => Complex.exp (-(β : ℂ)) * z)
                  tsum_mul_right.symm
            _ = Complex.exp (-(β : ℂ))
                  * ∑' m : ℕ, ((β : ℂ) / (d : ℂ)) ^ m
                    / (m.factorial : ℂ) * (2 : ℂ)⁻¹ ^ m
                    * ((multSum ρ χ m : ℝ) : ℂ) * χ g := by
                refine congrArg (fun z => Complex.exp (-(β : ℂ)) * z)
                  (tsum_congr fun m => ?_)
                push_cast
                ring
        exact hχ.symm

end ColumnExpansion

end ThetLogos
