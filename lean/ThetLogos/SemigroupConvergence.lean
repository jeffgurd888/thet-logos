/-
# SHELF-1d - semigroup convergence: Trotter-Kato (working label)

Brick SHELF-1d of the SHELF line, completing the SHELF-1
line's registered seats: approximation / convergence -
the Lie-Trotter product formula and Trotter-Kato type
results at the seats the corpus owns. Built against
SHELF-1a (`SemigroupCore.lean`: `C0Semigroup`,
`expSemigroup`, `ResolventSpec`, `yosidaApprox`) and
SHELF-1b (`SemigroupGeneration.lean`: `DissBound`,
`HasResolventAt`, `norm_exp_le`, `duhamel_estimate`),
cited by their landed names, never forked. SHELF-1c
(`AnalyticSemigroup.lean`) is NOT in the tree at build
time (checked 2026-11-01) - this brick proceeds without
it. SHELF-6 (`SemigroupDuality.lean`) uses the same
`expSemigroup` / `ResolventSpec` vocabulary on its finite
C(K) seat; its bounded operators are instances of the
bounded seats below, no fork needed. NO CLAIM beyond
the theorems below; dials 0/4.

## Probe inventory (pin Mathlib v4.35.0-rc3, 2026-11-01)

* Trotter / Chernoff / Lie product formula: NONE in the
  pin (grep for `Trotter`, product-formula `Chernoff`
  over `Mathlib/` returns only Lie-algebra "product"
  and the probabilistic Chernoff bound). No semigroup
  convergence API and no Trotter-Kato statement either.
* What the pin DOES own, consumed here:
  `NormedSpace.exp_add_of_commute` and
  `NormedSpace.exp_sum_of_commute`
  (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`):
  `exp (x + y) = exp x * exp y` for commuting Banach-
  algebra elements; `NormedSpace.exp_nsmul`:
  `exp (n • x) = (exp x) ^ n`; `Commute.exp_right` /
  `Commute.exp_left`; `NormedSpace.exp_continuous`;
  `hasDerivAt_exp_smul_const`
  (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`).
* Corpus API consumed: SHELF-1b's `norm_exp_le`
  (`||exp X|| <= Real.exp ||X||`, from the defining
  series) and the algebraic `ResolventSpec` calculus of
  SHELF-1a (section 4 there). SHELF-1b's
  `duhamel_estimate` is NOT consumed: its proof routes
  through `Commute P Q`, so it does not price the
  noncommuting exponential difference; section 2 below
  proves the algebra-level Duhamel estimate with no
  commutation between the two exponents (each exponent
  commutes only with its own exponential).

## What lands

1. **Lie-Trotter at the bounded commuting seat (FULL
   at this seat).** For bounded `A B : E ->L[R] E` with
   `Commute A B` (the hypothesis stated exactly), the
   product formula collapses to an exact finite
   identity: `(exp (s•A) * exp (s•B)) ^ n
   = exp ((n*s) • (A + B))` for every `n` and `s`
   (`trotter_pow_exact`), hence with `s = t / n` the
   Trotter approximants are CONSTANT in `n >= 1` and
   equal `(expSemigroup (A + B)).toFun t`
   (`lie_trotter_commuting`), so the Lie-Trotter limit
   holds trivially at this seat
   (`lie_trotter_tendsto`, applied form
   `lie_trotter_tendsto_apply`).
2. **Trotter-Kato at the bounded seat (FULL at this
   seat, in the norm-convergence form).** If bounded
   generators converge in operator norm,
   `Aseq n -> A`, then (a) their resolvents at any
   parameter where `ResolventSpec`s and a uniform
   resolvent bound hold converge in operator norm, at
   rate `C^2 * ||Aseq n - A||`
   (`tk_resolvent_opNorm_le`, `tk_resolvent_tendsto`),
   and (b) their semigroups converge in operator norm
   uniformly on compact time intervals `[0, T]`
   (`tk_semigroup_uniform_on_Icc`), via the section-2
   estimate `||exp X - exp Y||
   <= Real.exp (max ||X|| ||Y||) * ||X - Y||`
   (`exp_sub_exp_norm_le`).

## The seam (pre-named PARTIAL)

* **General Trotter-Kato is NOT landed: PARTIAL at
  exactly this seam.** The classical statement -
  STRONG resolvent convergence of (possibly unbounded)
  generators, plus uniform boundedness, implies STRONG
  semigroup convergence uniformly on compact time
  intervals - is not proved here. The missing step,
  named exactly: the passage from strong (pointwise)
  resolvent convergence to semigroup convergence
  routes classically through a Chernoff / Post-Widder
  approximation theorem, and the pin owns no Chernoff
  approximation theorem, no Post-Widder exponential
  formula, and no Laplace / resolvent-integral formula
  (the last is SHELF-1a's named remainder, verbatim).
  Section 3 uses the strictly stronger hypothesis of
  operator-NORM generator convergence, under which the
  passage is the elementary estimate of section 2.
* **Noncommuting Lie-Trotter is NOT landed.** Without
  `Commute A B` the one-step product differs from
  `exp (s • (A + B))` at second order in `s`, and the
  convergence of its `n`-th power needs exactly the
  Chernoff error estimate the pin lacks (above).
  SHELF-1b's `duhamel_estimate` does not substitute:
  it assumes `Commute P Q` and contraction bounds.

## Read-back

The consumer is SHELF-1a's own `expSemigroup`: section
1 is stated directly as a splitting of
`(expSemigroup (A + B)).toFun t` into the product of
the `expSemigroup A` / `expSemigroup B` factors, and
section 3 as convergence of `expSemigroup (Aseq n)`.
Every bounded seat of the corpus (in particular
SHELF-6's finite C(K) operators) inherits both by
instantiation. No unbounded seat consumes the
norm-convergence form of section 3 yet: SHELF-1b's
Yosida approximants converge only strongly on the
domain, not in operator norm - that is the seam above,
not a silent gap.

Count band: S-M.
-/

import ThetLogos.SemigroupGeneration
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ThetLogos

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-! ## 1. The Lie-Trotter product formula at the bounded
commuting seat -/

section Trotter

variable (A B : E →L[ℝ] E)

/-- The one-step Trotter factor: the product, in the
operator algebra, of the two bounded exponentials at
step size `s`. As a continuous linear map,
`(trotterFactor A B s) x
= (expSemigroup A).toFun s ((expSemigroup B).toFun s x)`. -/
noncomputable def trotterFactor (s : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp (s • A) * NormedSpace.exp (s • B)

theorem trotterFactor_apply (s : ℝ) (x : E) :
    trotterFactor A B s x
      = (expSemigroup A).toFun s ((expSemigroup B).toFun s x) := by
  rw [trotterFactor, expSemigroup_toFun, expSemigroup_toFun]
  rfl

/-- Under the exact commutation hypothesis
`Commute A B`, the one-step Trotter factor is the
exponential of the sum at the same step size. -/
theorem trotterFactor_eq_exp (hAB : Commute A B) (s : ℝ) :
    trotterFactor A B s
      = NormedSpace.exp (s • (A + B)) := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  have hcomm : Commute (s • A) (s • B) :=
    (hAB.smul_left s).smul_right s
  rw [trotterFactor, ← NormedSpace.exp_add_of_commute hcomm,
    smul_add]

/-- The exact finite identity the commuting seat
supports: the `n`-th power of the one-step Trotter
factor at step size `s` is the exponential of the sum
at total time `n * s`, for every `n : ℕ` and every
real `s`. -/
theorem trotter_pow_exact (hAB : Commute A B) (s : ℝ)
    (n : ℕ) :
    (trotterFactor A B s) ^ n
      = NormedSpace.exp (((n : ℝ) * s) • (A + B)) := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  rw [trotterFactor_eq_exp A B hAB s,
    ← NormedSpace.exp_nsmul n (s • (A + B))]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

/-- The exact identity in SHELF-1a's vocabulary: the
`n`-th power of the one-step Trotter factor is
`(expSemigroup (A + B)).toFun (n * s)`. -/
theorem trotter_pow_expSemigroup (hAB : Commute A B)
    (s : ℝ) (n : ℕ) :
    (trotterFactor A B s) ^ n
      = (expSemigroup (A + B)).toFun ((n : ℝ) * s) := by
  rw [trotter_pow_exact A B hAB s n, expSemigroup_toFun]

/-- **Lie-Trotter product formula at the bounded
commuting seat.** For `Commute A B` and every
`n >= 1`, the Trotter approximant at step size `t / n`
is EXACTLY the sum semigroup at time `t`: the product
formula collapses to a constant sequence at this seat. -/
theorem lie_trotter_commuting (hAB : Commute A B)
    (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (trotterFactor A B (t / (n : ℝ))) ^ n
      = (expSemigroup (A + B)).toFun t := by
  rw [trotter_pow_expSemigroup A B hAB (t / (n : ℝ)) n]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  congr 2
  field_simp

/-- The Lie-Trotter limit at the commuting seat, as a
sequence over `ℕ` (the `n + 1` step size avoids the
degenerate step): the approximants are eventually -
in fact everywhere - constant, hence converge to
`(expSemigroup (A + B)).toFun t` in operator norm. -/
theorem lie_trotter_tendsto (hAB : Commute A B) (t : ℝ) :
    Tendsto (fun n : ℕ =>
        (trotterFactor A B (t / ((n : ℝ) + 1))) ^ (n + 1))
      atTop (𝓝 ((expSemigroup (A + B)).toFun t)) := by
  apply tendsto_atTop_of_eventually_const
    (i₀ := 0)
  intro n _
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have e := lie_trotter_commuting A B hAB t
    (n := n + 1) (by simp)
  rwa [Nat.cast_add, Nat.cast_one] at e

/-- The applied (strong) form of the Lie-Trotter limit
at the commuting seat. -/
theorem lie_trotter_tendsto_apply (hAB : Commute A B)
    (t : ℝ) (x : E) :
    Tendsto (fun n : ℕ =>
        ((trotterFactor A B (t / ((n : ℝ) + 1))) ^ (n + 1)) x)
      atTop (𝓝 ((expSemigroup (A + B)).toFun t x)) :=
  ((ContinuousLinearMap.apply ℝ E) x).continuous.tendsto _
    |>.comp (lie_trotter_tendsto A B hAB t)

end Trotter

/-! ## 3 (resolvent half). Trotter-Kato at the bounded
seat: resolvent convergence from generator norm
convergence -/

section TrotterKatoResolvent

/-- The generator value of a bounded semigroup: for
`expSemigroup A`, SHELF-1a's `genVal` is `A x`. -/
theorem expSemigroup_genVal_eq (A : E →L[ℝ] E) {x : E}
    (hx : x ∈ (expSemigroup A).genDom) :
    (expSemigroup A).genVal hx = A x := by
  have h := expSemigroup_generator_apply A x hx
  rwa [C0Semigroup.generator_apply] at h

/-- The resolvent difference identity at the bounded
seat: if `R` is a resolvent of `A` and `R'` a resolvent
of `A'` at the same parameter `lam` (both in
SHELF-1a's `ResolventSpec` sense for the respective
bounded semigroups), then for every `x`,
`R' x - R x = - R' ((A - A') (R x))`. Pure algebra from
the two specifications. -/
theorem resolvent_sub_eq (A A' : E →L[ℝ] E) (lam : ℝ)
    {R R' : E →L[ℝ] E}
    (hR : ResolventSpec (expSemigroup A) lam R)
    (hR' : ResolventSpec (expSemigroup A') lam R')
    (x : E) :
    R' x - R x = - R' ((A - A') (R x)) := by
  set u := R x with hu
  have humem : u ∈ (expSemigroup A).genDom :=
    mem_genDom_resolvent (expSemigroup A) lam R hR x
  have humem' : u ∈ (expSemigroup A').genDom :=
    (expSemigroup A').mem_genDom.mpr
      ⟨A' u, expSemigroup_hasGen A' u⟩
  have hspec' := hR'.1 u humem'
  rw [expSemigroup_genVal_eq A' humem'] at hspec'
  have hgen : lam • u - A u = x := by
    have h2 := genVal_resolvent (expSemigroup A) lam R hR x
    rw [expSemigroup_genVal_eq A
      (mem_genDom_resolvent (expSemigroup A) lam R hR x)] at h2
    rw [h2]
    abel
  have harg : lam • u - A' u = x + (A - A') u := by
    rw [ContinuousLinearMap.sub_apply]
    rw [← hgen]
    abel
  rw [harg, map_add] at hspec'
  conv_lhs => rw [← hspec']
  abel

/-- Operator-norm rate for resolvent convergence at
the bounded seat: with a common bound `C` on both
resolvents, `||R' - R|| <= C^2 * ||A' - A||`. -/
theorem tk_resolvent_opNorm_le (A A' : E →L[ℝ] E)
    (lam : ℝ) {R R' : E →L[ℝ] E} {C : ℝ} (hC : 0 ≤ C)
    (hR : ResolventSpec (expSemigroup A) lam R)
    (hR' : ResolventSpec (expSemigroup A') lam R')
    (hRb : ‖R‖ ≤ C) (hR'b : ‖R'‖ ≤ C) :
    ‖R' - R‖ ≤ C ^ 2 * ‖A' - A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity : (0 : ℝ) ≤ C ^ 2 * ‖A' - A‖)
  intro x
  have h1 : ‖R' x - R x‖ ≤ ‖R'‖ * ‖(A - A') (R x)‖ := by
    rw [resolvent_sub_eq A A' lam hR hR' x, norm_neg]
    exact R'.le_opNorm _
  have h2 : ‖(A - A') (R x)‖ ≤ ‖A - A'‖ * ‖R x‖ :=
    (A - A').le_opNorm _
  have h3 : ‖R x‖ ≤ ‖R‖ * ‖x‖ := R.le_opNorm x
  have hnorm : ‖A - A'‖ = ‖A' - A‖ := by
    rw [← norm_neg, neg_sub]
  calc ‖(R' - R) x‖ = ‖R' x - R x‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖R'‖ * (‖A - A'‖ * (‖R‖ * ‖x‖)) :=
        le_trans h1 (mul_le_mul_of_nonneg_left
          (le_trans h2 (mul_le_mul_of_nonneg_left h3
            (norm_nonneg _))) (norm_nonneg _))
    _ ≤ C ^ 2 * ‖A' - A‖ * ‖x‖ := by
        have g1 : ‖R‖ * ‖x‖ ≤ C * ‖x‖ :=
          mul_le_mul_of_nonneg_right hRb (norm_nonneg _)
        have g2 : ‖A - A'‖ * (‖R‖ * ‖x‖)
            ≤ ‖A' - A‖ * (C * ‖x‖) := by
          rw [hnorm]
          exact mul_le_mul_of_nonneg_left g1 (norm_nonneg _)
        have g3 : ‖R'‖ * (‖A - A'‖ * (‖R‖ * ‖x‖))
            ≤ C * (‖A' - A‖ * (C * ‖x‖)) :=
          mul_le_mul hR'b g2
            (by positivity) hC
        refine le_trans g3 (le_of_eq ?_)
        ring

/-- **Trotter-Kato at the bounded seat, resolvent
half.** Operator-norm convergence of bounded
generators implies operator-norm convergence of their
resolvents at any parameter carrying `ResolventSpec`s
with a uniform bound `C`. -/
theorem tk_resolvent_tendsto {Aseq : ℕ → (E →L[ℝ] E)}
    {A : E →L[ℝ] E} (hA : Tendsto Aseq atTop (𝓝 A))
    (lam : ℝ) {Rseq : ℕ → (E →L[ℝ] E)} {R : E →L[ℝ] E}
    {C : ℝ} (hC : 0 ≤ C)
    (hR : ResolventSpec (expSemigroup A) lam R)
    (hRseq : ∀ n, ResolventSpec (expSemigroup (Aseq n))
      lam (Rseq n))
    (hRb : ‖R‖ ≤ C) (hRseqb : ∀ n, ‖Rseq n‖ ≤ C) :
    Tendsto (fun n => ‖Rseq n - R‖) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n => ‖Aseq n - A‖) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => Aseq n - A) atTop
        (𝓝 (A - A)) := hA.sub_const A
    rw [sub_self] at h1
    simpa using h1.norm
  have hrate : Tendsto (fun n => C ^ 2 * ‖Aseq n - A‖)
      atTop (𝓝 (C ^ 2 * 0)) :=
    tendsto_const_nhds.mul hdiff
  rw [mul_zero] at hrate
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hrate
  intro n
  exact tk_resolvent_opNorm_le A (Aseq n) lam hC hR
    (hRseq n) hRb (hRseqb n)

end TrotterKatoResolvent

/-! ## 2. The algebra-level Duhamel estimate (no
commutation between the two exponents) -/

section ExpEstimate

variable (X Y : E →L[ℝ] E)

/-- The derivative of the interpolation
`s |-> exp (s • X) * exp ((1 - s) • Y)` in the operator
algebra: each exponent commutes only with its own
exponential (`Commute.exp_right` of a scalar multiple
of itself), so no `Commute X Y` is needed. -/
theorem hasDerivAt_exp_interp (s : ℝ) :
    HasDerivAt
      (fun u : ℝ => NormedSpace.exp (u • X)
        * NormedSpace.exp ((1 - u) • Y))
      (NormedSpace.exp (s • X) * (X - Y)
        * NormedSpace.exp ((1 - s) • Y)) s := by
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
      (NormedSpace.exp (s • X) * X) s :=
    hasDerivAt_exp_smul_const X s
  have hg : HasDerivAt (fun v : ℝ => NormedSpace.exp (v • Y))
      (NormedSpace.exp ((1 - s) • Y) * Y) (1 - s) :=
    hasDerivAt_exp_smul_const Y (1 - s)
  have hh : HasDerivAt (fun u : ℝ => 1 - u) (-1) s :=
    (hasDerivAt_id s).const_sub 1
  have hmul0 := h1.mul (hg.scomp s hh)
  have hneg : (-1 : ℝ) • (NormedSpace.exp ((1 - s) • Y) * Y)
      = -(NormedSpace.exp ((1 - s) • Y) * Y) := by
    rw [neg_smul, one_smul]
  have eY : NormedSpace.exp ((1 - s) • Y) * Y
      = Y * NormedSpace.exp ((1 - s) • Y) :=
    (((Commute.refl Y).smul_right (1 - s)).exp_right).eq.symm
  have heq : NormedSpace.exp (s • X) * X
        * NormedSpace.exp ((1 - s) • Y)
        + NormedSpace.exp (s • X)
          * ((-1 : ℝ) • (NormedSpace.exp ((1 - s) • Y) * Y))
      = NormedSpace.exp (s • X) * (X - Y)
        * NormedSpace.exp ((1 - s) • Y) := by
    rw [hneg, mul_neg, eY]
    noncomm_ring
  simp only [Function.comp_apply] at hmul0
  rw [heq] at hmul0
  exact hmul0

/-- Continuity of the interpolation derivative. -/
theorem continuous_exp_interp_deriv :
    Continuous (fun s : ℝ => NormedSpace.exp (s • X)
      * (X - Y) * NormedSpace.exp ((1 - s) • Y)) := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  apply Continuous.mul
  apply Continuous.mul
  · exact NormedSpace.exp_continuous.comp
      (continuous_id.smul continuous_const)
  · exact continuous_const
  · exact NormedSpace.exp_continuous.comp
      ((continuous_const.sub continuous_id).smul
        continuous_const)

/-- **The exponential difference estimate.**
`||exp X - exp Y|| <= Real.exp (max ||X|| ||Y||)
* ||X - Y||` for arbitrary bounded `X Y` - no
commutation, no contraction hypothesis. Proof:
differentiate the interpolation of
`hasDerivAt_exp_interp` and integrate; the norm of the
integrand is priced by SHELF-1b's `norm_exp_le` and the
convex-combination bound
`s * ||X|| + (1 - s) * ||Y|| <= max ||X|| ||Y||`. -/
theorem exp_sub_exp_norm_le :
    ‖NormedSpace.exp X - NormedSpace.exp Y‖
      ≤ Real.exp (max ‖X‖ ‖Y‖) * ‖X - Y‖ := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  set G : ℝ → (E →L[ℝ] E) := fun s =>
    NormedSpace.exp (s • X) * NormedSpace.exp ((1 - s) • Y)
    with hGdef
  set G' : ℝ → (E →L[ℝ] E) := fun s =>
    NormedSpace.exp (s • X) * (X - Y)
      * NormedSpace.exp ((1 - s) • Y) with hG'def
  have hderiv : ∀ s : ℝ, HasDerivAt G (G' s) s :=
    fun s => hasDerivAt_exp_interp X Y s
  have hInt : IntervalIntegrable G' MeasureTheory.volume 0 1 :=
    (continuous_exp_interp_deriv X Y).intervalIntegrable 0 1
  have hFTC : ∫ s in (0 : ℝ)..1, G' s = G 1 - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s) hInt
  have hG1 : G 1 = NormedSpace.exp X := by
    rw [hGdef]
    simp only [one_smul, sub_self, zero_smul,
      NormedSpace.exp_zero, mul_one]
  have hG0 : G 0 = NormedSpace.exp Y := by
    rw [hGdef]
    simp only [zero_smul, NormedSpace.exp_zero, one_mul,
      sub_zero, one_smul]
  calc ‖NormedSpace.exp X - NormedSpace.exp Y‖
      = ‖∫ s in (0 : ℝ)..1, G' s‖ := by
        rw [hFTC, hG1, hG0]
    _ ≤ (Real.exp (max ‖X‖ ‖Y‖) * ‖X - Y‖) * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun s hs => by
            have hsI : s ∈ Set.Ioc (0 : ℝ) 1 := by
              rwa [Set.uIoc_of_le zero_le_one] at hs
            have hs0 : 0 ≤ s := hsI.1.le
            have hs1 : s ≤ 1 := hsI.2
            have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
            have hnorm1 : ‖NormedSpace.exp (s • X)‖
                ≤ Real.exp (s * ‖X‖) := by
              refine le_trans (norm_exp_le _)
                (Real.exp_le_exp.mpr ?_)
              rw [norm_smul, Real.norm_of_nonneg hs0]
            have hnorm2 : ‖NormedSpace.exp ((1 - s) • Y)‖
                ≤ Real.exp ((1 - s) * ‖Y‖) := by
              refine le_trans (norm_exp_le _)
                (Real.exp_le_exp.mpr ?_)
              rw [norm_smul, Real.norm_of_nonneg h1s]
            have hconv : s * ‖X‖ + (1 - s) * ‖Y‖
                ≤ max ‖X‖ ‖Y‖ := by
              calc s * ‖X‖ + (1 - s) * ‖Y‖
                  ≤ s * max ‖X‖ ‖Y‖
                    + (1 - s) * max ‖X‖ ‖Y‖ :=
                    add_le_add
                      (mul_le_mul_of_nonneg_left
                        (le_max_left _ _) hs0)
                      (mul_le_mul_of_nonneg_left
                        (le_max_right _ _) h1s)
                _ = max ‖X‖ ‖Y‖ := by
                    rw [← add_mul]
                    have : s + (1 - s) = 1 := by ring
                    rw [this, one_mul]
            calc ‖G' s‖
                ≤ ‖NormedSpace.exp (s • X)‖ * ‖X - Y‖
                  * ‖NormedSpace.exp ((1 - s) • Y)‖ := by
                  rw [hG'def]
                  exact le_trans (norm_mul_le _ _)
                    (mul_le_mul_of_nonneg_right
                      (norm_mul_le _ _) (norm_nonneg _))
              _ ≤ (Real.exp (s * ‖X‖) * ‖X - Y‖)
                  * Real.exp ((1 - s) * ‖Y‖) :=
                  mul_le_mul
                    (mul_le_mul_of_nonneg_right hnorm1
                      (norm_nonneg _)) hnorm2 (norm_nonneg _)
                    (mul_nonneg (Real.exp_pos _).le
                      (norm_nonneg _))
              _ = Real.exp (s * ‖X‖ + (1 - s) * ‖Y‖)
                  * ‖X - Y‖ := by
                  have e : Real.exp (s * ‖X‖) * ‖X - Y‖
                      * Real.exp ((1 - s) * ‖Y‖)
                      = (Real.exp (s * ‖X‖)
                        * Real.exp ((1 - s) * ‖Y‖))
                        * ‖X - Y‖ := by ring
                  rw [e, ← Real.exp_add]
              _ ≤ Real.exp (max ‖X‖ ‖Y‖) * ‖X - Y‖ :=
                  mul_le_mul_of_nonneg_right
                    (Real.exp_le_exp.mpr hconv)
                    (norm_nonneg _))
    _ = Real.exp (max ‖X‖ ‖Y‖) * ‖X - Y‖ := by
        rw [sub_zero, abs_one, mul_one]

end ExpEstimate

/-! ## 3 (semigroup half). Trotter-Kato at the bounded
seat: semigroup convergence uniformly on compact time
intervals, from generator norm convergence -/

section TrotterKatoSemigroup

/-- Pointwise-in-time operator-norm rate: for
`t ∈ [0, T]` and `||A'|| <= ||A|| + 1`,
`||exp (t•A') - exp (t•A)||
<= Real.exp (T * (||A|| + 1)) * T * ||A' - A||`,
directly from `exp_sub_exp_norm_le`. -/
theorem tk_semigroup_norm_le (A A' : E →L[ℝ] E)
    {T : ℝ} (hT : 0 ≤ T) (hA' : ‖A'‖ ≤ ‖A‖ + 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖(expSemigroup A').toFun t - (expSemigroup A).toFun t‖
      ≤ Real.exp (T * (‖A‖ + 1)) * T * ‖A' - A‖ := by
  rw [expSemigroup_toFun, expSemigroup_toFun]
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hX : ‖t • A'‖ ≤ T * (‖A‖ + 1) := by
    rw [norm_smul, Real.norm_of_nonneg ht0]
    exact mul_le_mul htT hA' (norm_nonneg _) hT
  have hY : ‖t • A‖ ≤ T * (‖A‖ + 1) := by
    rw [norm_smul, Real.norm_of_nonneg ht0]
    exact mul_le_mul htT (by linarith [norm_nonneg A])
      (norm_nonneg _) hT
  have hmax : max ‖t • A'‖ ‖t • A‖ ≤ T * (‖A‖ + 1) :=
    max_le hX hY
  calc ‖NormedSpace.exp (t • A') - NormedSpace.exp (t • A)‖
      ≤ Real.exp (max ‖t • A'‖ ‖t • A‖) * ‖t • A' - t • A‖ :=
        exp_sub_exp_norm_le _ _
    _ ≤ Real.exp (T * (‖A‖ + 1)) * (T * ‖A' - A‖) := by
        apply mul_le_mul (Real.exp_le_exp.mpr hmax) _
          (norm_nonneg _) (Real.exp_pos _).le
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht0]
        exact mul_le_mul_of_nonneg_right htT (norm_nonneg _)
    _ = Real.exp (T * (‖A‖ + 1)) * T * ‖A' - A‖ := by ring

/-- **Trotter-Kato at the bounded seat, semigroup
half.** Operator-norm convergence of bounded generators
implies operator-norm convergence of their semigroups
uniformly on every compact time interval `[0, T]`. -/
theorem tk_semigroup_uniform_on_Icc
    {Aseq : ℕ → (E →L[ℝ] E)} {A : E →L[ℝ] E}
    (hA : Tendsto Aseq atTop (𝓝 A))
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc 0 T,
      ‖(expSemigroup (Aseq n)).toFun t
        - (expSemigroup A).toFun t‖ ≤ ε := by
  set C0 : ℝ := Real.exp (T * (‖A‖ + 1)) with hC0def
  have hC0 : 0 < C0 := Real.exp_pos _
  set δ : ℝ := min 1 (ε / (C0 * T + 1)) with hδdef
  have hδ : 0 < δ :=
    lt_min one_pos (by positivity)
  rw [Metric.tendsto_atTop] at hA
  obtain ⟨N, hN⟩ := hA δ hδ
  refine ⟨N, fun n hn t ht => ?_⟩
  have hd : dist (Aseq n) A < δ := hN n hn
  have hdiff : ‖Aseq n - A‖ < δ := by
    rwa [dist_eq_norm] at hd
  have hA' : ‖Aseq n‖ ≤ ‖A‖ + 1 := by
    have h1 : ‖Aseq n‖ ≤ ‖A‖ + ‖Aseq n - A‖ := by
      have e : Aseq n = A + (Aseq n - A) := by abel
      conv_lhs => rw [e]
      exact norm_add_le _ _
    have h2 : ‖Aseq n - A‖ < 1 :=
      lt_of_lt_of_le hdiff (min_le_left _ _)
    linarith
  have hrate := tk_semigroup_norm_le A (Aseq n) hT hA' ht
  refine le_trans hrate ?_
  have hδ2 : ‖Aseq n - A‖ ≤ ε / (C0 * T + 1) :=
    le_of_lt (lt_of_lt_of_le hdiff (min_le_right _ _))
  have hCT : (0 : ℝ) ≤ C0 * T := mul_nonneg hC0.le hT
  calc C0 * T * ‖Aseq n - A‖
      ≤ C0 * T * (ε / (C0 * T + 1)) :=
        mul_le_mul_of_nonneg_left hδ2 hCT
    _ ≤ ε := by
        have hpos : (0 : ℝ) < C0 * T + 1 := by positivity
        have hratio : C0 * T / (C0 * T + 1) ≤ 1 :=
          (div_le_one hpos).mpr (by linarith)
        have e : C0 * T * (ε / (C0 * T + 1))
            = ε * (C0 * T / (C0 * T + 1)) := by ring
        rw [e]
        calc ε * (C0 * T / (C0 * T + 1)) ≤ ε * 1 :=
              mul_le_mul_of_nonneg_left hratio hε.le
          _ = ε := mul_one _

/-- The applied (strong) form, uniform on `[0, T]` for
each fixed vector: the same `N` works for the orbit
bound `ε * ||x||`. -/
theorem tk_semigroup_uniform_on_Icc_apply
    {Aseq : ℕ → (E →L[ℝ] E)} {A : E →L[ℝ] E}
    (hA : Tendsto Aseq atTop (𝓝 A))
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc 0 T,
      ‖(expSemigroup (Aseq n)).toFun t x
        - (expSemigroup A).toFun t x‖ ≤ ε * ‖x‖ := by
  obtain ⟨N, hN⟩ := tk_semigroup_uniform_on_Icc hA hT hε
  refine ⟨N, fun n hn t ht => ?_⟩
  calc ‖(expSemigroup (Aseq n)).toFun t x
        - (expSemigroup A).toFun t x‖
      = ‖((expSemigroup (Aseq n)).toFun t
        - (expSemigroup A).toFun t) x‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖(expSemigroup (Aseq n)).toFun t
          - (expSemigroup A).toFun t‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖x‖ :=
        mul_le_mul_of_nonneg_right (hN n hn t ht)
          (norm_nonneg _)

end TrotterKatoSemigroup
