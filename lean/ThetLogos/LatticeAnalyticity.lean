import ThetLogos.LatticeCorrelations
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-
# β-analyticity and first-order coefficients (Pitch 4, Stage 1c-0 exhibit)

HONESTY LEDGER — read this before citing anything from this file.

## 0. What this file is

Tier: **T1 at the finite-lattice level** — machine-checked theorems
about one fixed finite lattice, in the Stage 0 / Stage 1a setting of
`ThetLogos.LatticeGauge` / `ThetLogos.LatticeCorrelations`, whose
devices are consumed unchanged.

This is the **Stage 1c-0 exhibit** carved out of Stage 1c by the
parked-fleet gauntlet (`whitepaper/gauntlet-parked-fleet-2026-10-17.md`
§2, price M): at **fixed finite volume**, with no uniformity in volume
or spacing claimed anywhere:

(i) **Analyticity**: for every bounded measurable observable `F`, the
function `β ↦ ⟨F⟩_β` is analytic at `β = 0` (proved through the
canonical entire extension to a complex coupling; numerator and
denominator are ratios of integral-analytic functions, and the
denominator is Stage 1a's nowhere-vanishing `gibbsPartition`).

(ii) **The first-order coefficient, exactly**: with the Wilson action
written as `β • A`, `A` the β-free density sum (`wilsonAction_eq`
below — Stage 0's `wilsonAction` is literally `β * ∑ plaquetteDensity`),
the derivative of a plaquette expectation at `β = 0` is
`−κ_p` with `κ_p = Cov₀(W_p, A)` (§5), and `κ_p` collapses to a finite
sum over **link-sharing plaquettes only** (§6): at `β = 0` the
factorization of Stage 1a kills every covariance term whose plaquette
shares no link with `p`. On the circle instance the sum is evaluated
in closed form: `κ_p = −1/2`, so `⟨W_p⟩_β = β/2 + O(β²)` (§7).

(iii) **The loop version is a perimeter law at first order**: for a
general Wilson loop `W_C`, the first-order coefficient `κ(C)` is a
finite sum over plaquettes sharing a link with `C`, and the number of
such plaquettes is at most `12 · |C|` — the response at first order
sees the loop's perimeter, not its area (§6).

(iv) **Rigorous remainder**: the `O(β²)` in the first-order expansion
of any bounded observable's expectation carries an **explicit**
constant (`firstOrderConst`), built only from the observable's bound
and Stage 0's action bound (§3–§4). No asymptotic hand-waving.

## 0.1 Mandatory clauses (binding on this module)

**(i) Finite-volume clause.** Every statement is at fixed finite `Λ`.
No limit — in volume, in spacing, in anything — is taken or asserted.

**(ii) K5 clause (pre-named in the gauntlet).** Nothing in this module
is area-law evidence. The perimeter law of (iii) is a statement about
the first-order response at `β = 0`; the minimal-surface tiling that
produces an area law is an all-orders phenomenon. No text may quote
this module as bearing on confinement.

**(iii) No decay/clustering claim.** Nothing here asserts exponential
decay of correlations, a correlation length, or a mass. Uniform
clustering is Stage 1c proper, parked at XL; this exhibit is a ladder
toward it, not a down payment on it.

**(iv) PARTIAL-δ untouched; Clay clause.** The Gram/character-expansion
clause of Stage 1b-B is not spent or addressed here. **Parts of the
official Clay Yang–Mills statement closed by this module: 0.**

This module is NOT in the root import list of the library (the corpus
pattern for recent exhibits); it is verified by a targeted build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal Topology

/-! ## §1. The β-free action density and its bounds

Stage 0's `wilsonAction σ ρ β U` is `β` times a β-free sum of
plaquette densities. Naming that sum `A` (`actionDensity`) puts the
Gibbs weight in the form `exp (−β • A)` that the whole exhibit
differentiates. -/

section Setup

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The β-free action density sum:
`A U = Σ_x Σ_{μ<ν} plaquetteDensity U x μ ν`. -/
noncomputable def actionDensity (U : Config Λ G) : ℝ :=
  ∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν

/-- Stage 0's Wilson action is `β` times the density sum — the
definitional identity the whole exhibit rests on. -/
theorem wilsonAction_eq (β : ℝ) (U : Config Λ G) :
    wilsonAction σ ρ β U = β * actionDensity σ ρ U := rfl

/-- Stage 0's explicit action bound `2 · (16 · |Λ|)`, named once at the
density level. -/
noncomputable def actionBound : ℝ := 2 * (16 * (Fintype.card Λ : ℝ))

theorem actionBound_nonneg : 0 ≤ actionBound (Λ := Λ) := by
  unfold actionBound
  positivity

/-- The density sum is nonnegative (for `0 < d`). -/
theorem actionDensity_nonneg (hd : 0 < d) (U : Config Λ G) :
    0 ≤ actionDensity σ ρ U := by
  have h := wilsonAction_nonneg σ ρ hd zero_le_one U
  rwa [wilsonAction_eq σ ρ (1 : ℝ) U, one_mul] at h

/-- The density sum is bounded by `actionBound`, from Stage 0's
`wilsonAction_abs_le` at `β = 1`. -/
theorem actionDensity_abs_le (hd : 0 < d) (U : Config Λ G) :
    |actionDensity σ ρ U| ≤ actionBound (Λ := Λ) := by
  have h := wilsonAction_abs_le σ ρ hd (1 : ℝ) U
  rwa [wilsonAction_eq σ ρ (1 : ℝ) U, one_mul, abs_one, one_mul] at h

/-- The density sum is measurable (it is Stage 0's action at `β = 1`). -/
theorem measurable_actionDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Measurable (actionDensity σ ρ) := by
  have h : actionDensity σ ρ = wilsonAction σ ρ 1 := by
    funext U
    rw [wilsonAction_eq σ ρ (1 : ℝ) U, one_mul]
  rw [h]
  exact measurable_wilsonAction σ ρ hρcont 1

/-- A bounded measurable observable on configuration space is
integrable against the product Haar probability measure. -/
theorem integrable_of_bounded {F : Config Λ G → ℂ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ U, ‖F U‖ ≤ C) :
    Integrable F (configMeasure μG) :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)

/-- The norm of an integral over the probability configuration space
is bounded by any pointwise bound on the integrand's norm. -/
theorem norm_integral_le_of_forall_bound {F : Config Λ G → ℂ}
    (hF : Integrable F (configMeasure μG)) {C : ℝ}
    (hC : ∀ U, ‖F U‖ ≤ C) :
    ‖∫ U, F U ∂(configMeasure μG)‖ ≤ C := by
  calc ‖∫ U, F U ∂(configMeasure μG)‖
      ≤ ∫ U, ‖F U‖ ∂(configMeasure μG) := norm_integral_le_integral_norm _
    _ ≤ ∫ _U : Config Λ G, C ∂(configMeasure μG) :=
        integral_mono_ae ((integrable_norm_iff hF.aestronglyMeasurable).mpr hF)
          (integrable_const C) (ae_of_all _ hC)
    _ = C := by simp

/-- Integrability of observable-times-density-power integrands:
everything in sight is bounded and measurable on a probability
space. -/
theorem integrable_mul_actionDensity_pow
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) (k : ℕ) :
    Integrable (fun U => F U * (actionDensity σ ρ U : ℂ) ^ k)
      (configMeasure μG) := by
  have hA : Measurable fun U : Config Λ G => (actionDensity σ ρ U : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_actionDensity σ ρ hρcont)
  refine integrable_of_bounded μG (hF.mul (hA.pow_const k))
    (C := B * actionBound (Λ := Λ) ^ k) fun U => ?_
  rw [norm_mul, norm_pow, Complex.norm_real]
  exact mul_le_mul (hFB U) (pow_le_pow_left₀ (abs_nonneg _)
    (actionDensity_abs_le σ ρ hd U) k) (pow_nonneg (abs_nonneg _) k)
    (le_trans (norm_nonneg _) (hFB U))

/-- The `k`-th Gibbs moment of an observable at `β = 0`:
`∫ F · A^k` against the product Haar measure. -/
noncomputable def gibbsMoment (F : Config Λ G → ℂ) (k : ℕ) : ℂ :=
  ∫ U, F U * (actionDensity σ ρ U : ℂ) ^ k ∂(configMeasure μG)

/-- Moment bound: `‖∫ F A^k‖ ≤ B · actionBound^k`. -/
theorem norm_gibbsMoment_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) (k : ℕ) :
    ‖gibbsMoment σ μG ρ F k‖ ≤ B * actionBound (Λ := Λ) ^ k := by
  refine norm_integral_le_of_forall_bound μG
    (integrable_mul_actionDensity_pow σ μG ρ hρcont hd hF hFB k) fun U => ?_
  rw [norm_mul, norm_pow, Complex.norm_real]
  exact mul_le_mul (hFB U) (pow_le_pow_left₀ (abs_nonneg _)
    (actionDensity_abs_le σ ρ hd U) k) (pow_nonneg (abs_nonneg _) k)
    (le_trans (norm_nonneg _) (hFB U))

/-- The mean of the density sum: `E₀[A]`, a real number. -/
noncomputable def actionMean : ℝ :=
  ∫ U, actionDensity σ ρ U ∂(configMeasure μG)

/-- The density sum is integrable against the configuration measure. -/
theorem integrable_actionDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    Integrable (actionDensity σ ρ) (configMeasure μG) :=
  Integrable.of_bound (measurable_actionDensity σ ρ hρcont).aestronglyMeasurable _
    (ae_of_all _ fun U => by
      rw [Real.norm_eq_abs]
      exact actionDensity_abs_le σ ρ hd U)

theorem actionMean_nonneg
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    0 ≤ actionMean σ μG ρ :=
  integral_nonneg_of_ae (ae_of_all _ fun U => actionDensity_nonneg σ ρ hd U)

theorem actionMean_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    actionMean σ μG ρ ≤ actionBound (Λ := Λ) := by
  calc actionMean σ μG ρ = ∫ U, actionDensity σ ρ U ∂(configMeasure μG) := rfl
    _ ≤ ∫ _U : Config Λ G, actionBound (Λ := Λ) ∂(configMeasure μG) :=
        integral_mono_ae (integrable_actionDensity σ μG ρ hρcont hd)
          (integrable_const _)
          (ae_of_all _ fun U => le_trans (le_abs_self _)
            (actionDensity_abs_le σ ρ hd U))
    _ = actionBound (Λ := Λ) := by simp

end Setup

/-! ## §2. The exponential's Taylor bound and the first-order expansion

The whole first-order theory is one calculus estimate, applied twice
(numerator and denominator): `|e^{−x} − (1 − x)| ≤ (x²/2)·e^{|x|}`,
proved from the power series with an explicit tail bound. -/

section Expansion

/-- The complex exponential as a power series with
`Nat.factorial` denominators. -/
theorem complex_exp_eq_tsum (w : ℂ) :
    Complex.exp w = ∑' k : ℕ, w ^ k / (Nat.factorial k : ℂ) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact congr_fun NormedSpace.exp_eq_tsum_div w

/-- The real exponential as a power series. -/
theorem real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' k : ℕ, x ^ k / (Nat.factorial k : ℝ) := by
  rw [Real.exp_eq_exp_ℝ]
  exact congr_fun NormedSpace.exp_eq_tsum_div x

/-- **The one calculus estimate.** For real `x`,
`|e^{−x} − (1 − x)| ≤ (x²/2) · e^{|x|}`, from the power series with
the tail bounded term-by-term (`(k+2)! ≥ 2·k!`). -/
theorem exp_neg_sub_linear_bound (x : ℝ) :
    |Real.exp (-x) - (1 - x)| ≤ x ^ 2 / 2 * Real.exp |x| := by
  have hfact : ∀ k : ℕ, (2 : ℝ) * (Nat.factorial k : ℝ)
      ≤ (Nat.factorial (k + 2) : ℝ) := by
    intro k
    have h1 : (Nat.factorial (k + 2) : ℝ)
        = ((k + 2 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ)) := by
      rw [show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
    rw [h1]
    have hk : (0 : ℝ) ≤ (Nat.factorial k : ℝ) := by positivity
    have h2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      have h21 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
        have : ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) :=
          Nat.cast_le.mpr (by omega)
        simpa using this
      have h22 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        have : ((1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr (by omega)
        simpa using this
      calc (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) * 1 := by rwa [mul_one]
        _ ≤ ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h22 (le_trans zero_le_two h21)
    calc (2 : ℝ) * (Nat.factorial k : ℝ)
        ≤ (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) * (Nat.factorial k : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hk
      _ = ((k + 2 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ)) := by
          ring
  have htail : ∀ k : ℕ, |x| ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)
      ≤ (x ^ 2 / 2) * (|x| ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have hpos : (0 : ℝ) < (Nat.factorial (k + 2) : ℝ) := by positivity
    have hkf : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
    rw [pow_add, sq_abs]
    rw [div_le_iff₀ hpos]
    have e : |x| ^ k * x ^ 2
        = (x ^ 2 / 2) * (|x| ^ k / (Nat.factorial k : ℝ))
          * (2 * (Nat.factorial k : ℝ)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hfact k) (by positivity)
  have hsumm : Summable fun k : ℕ => (-x) ^ k / (Nat.factorial k : ℝ) :=
    Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) (fun k =>
      le_of_eq (by
        rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
          abs_of_nonneg (show (0:ℝ) ≤ (Nat.factorial k : ℝ) from Nat.cast_nonneg _)]))
  have hsummAbs : Summable fun k : ℕ => |x| ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) :=
    (summable_nat_add_iff 2).mpr (Real.summable_pow_div_factorial |x|)
  have hexp : Real.exp (-x) = ∑' k : ℕ, (-x) ^ k / (Nat.factorial k : ℝ) :=
    real_exp_eq_tsum (-x)
  have hsplit : (∑' k : ℕ, (-x) ^ k / (Nat.factorial k : ℝ))
      = (1 + -x) + ∑' k : ℕ, (-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) := by
    have h := (hsumm.sum_add_tsum_nat_add 2).symm
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    simp only [Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, div_one, pow_one, zero_add] at h
    exact h
  have hrem : Real.exp (-x) - (1 - x)
      = ∑' k : ℕ, (-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) := by
    rw [hexp, hsplit]; ring
  have hsummNorm : Summable (fun k : ℕ =>
      ‖(-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)‖) :=
    hsummAbs.congr (fun k => by
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
        abs_of_nonneg (show (0:ℝ) ≤ (Nat.factorial (k + 2) : ℝ)
          from Nat.cast_nonneg _)])
  rw [hrem]
  calc |∑' k : ℕ, (-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)|
      ≤ ∑' k : ℕ, |(-x) ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)| :=
        norm_tsum_le_tsum_norm hsummNorm
    _ = ∑' k : ℕ, |x| ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) := by
        apply tsum_congr
        intro k
        rw [abs_div, abs_pow, abs_neg,
          abs_of_nonneg (show (0:ℝ) ≤ (Nat.factorial (k + 2) : ℝ)
            from Nat.cast_nonneg _)]
    _ ≤ ∑' k : ℕ, (x ^ 2 / 2) * (|x| ^ k / (Nat.factorial k : ℝ)) :=
        hsummAbs.tsum_le_tsum htail
          ((Real.summable_pow_div_factorial |x|).mul_left _)
    _ = (x ^ 2 / 2) * Real.exp |x| := by
        rw [tsum_mul_left, ← real_exp_eq_tsum]

end Expansion

/-! ## §3. The complex covariance at `β = 0` and the first-order expansion

Stage 1a's `gibbsCov` is for real-valued observables; the plaquette
observable is complex-valued, so the covariance is defined here
directly from `gibbsExpect` at `β = 0` (the plain product-Haar
expectation, by Stage 0's `gibbsExpect_zero`). -/

section FirstOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The complex covariance at `β = 0`:
`Cov₀(F, H) = ⟨F·H⟩₀ − ⟨F⟩₀⟨H⟩₀`. -/
noncomputable def covZero (F H : Config Λ G → ℂ) : ℂ :=
  gibbsExpect σ μG ρ 0 (fun U => F U * H U)
    - gibbsExpect σ μG ρ 0 F * gibbsExpect σ μG ρ 0 H

/-- The zeroth moment is the `β = 0` expectation. -/
theorem gibbsMoment_zero (F : Config Λ G → ℂ) :
    gibbsMoment σ μG ρ F 0 = gibbsExpect σ μG ρ 0 F := by
  rw [gibbsExpect_zero]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp [gibbsMoment]

/-- The first moment is the `β = 0` expectation of `F · A`. -/
theorem gibbsMoment_one (F : Config Λ G → ℂ) :
    gibbsMoment σ μG ρ F 1
      = gibbsExpect σ μG ρ 0 (fun U => F U * (actionDensity σ ρ U : ℂ)) := by
  rw [gibbsExpect_zero]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp [gibbsMoment]

/-- The `β = 0` expectation of the complexified density sum is the
cast of its real mean. -/
theorem gibbsExpect_zero_actionDensityC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    gibbsExpect σ μG ρ 0 (fun U => (actionDensity σ ρ U : ℂ))
      = (actionMean σ μG ρ : ℂ) := by
  rw [gibbsExpect_zero]
  exact integral_complex_ofReal

/-- The covariance against the density sum, in moment form:
`Cov₀(F, A) = ∫ F·A − (∫ F)·E₀[A]`. -/
theorem covZero_actionDensity (F : Config Λ G → ℂ)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))
      = gibbsMoment σ μG ρ F 1
        - gibbsMoment σ μG ρ F 0 * (actionMean σ μG ρ : ℂ) := by
  rw [covZero, ← gibbsMoment_one σ μG ρ F, ← gibbsMoment_zero σ μG ρ F,
    gibbsExpect_zero_actionDensityC σ μG ρ hρcont hd]

/-- Norm bound on the covariance against `A`:
`‖Cov₀(F, A)‖ ≤ 2·B·actionBound`. -/
theorem norm_covZero_actionDensity_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) :
    ‖covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))‖
      ≤ 2 * B * actionBound (Λ := Λ) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hFB (fun _ => 1))
  have hm0 : ‖gibbsMoment σ μG ρ F 0‖ ≤ B := by
    have h := norm_gibbsMoment_le σ μG ρ hρcont hd hF hFB 0
    simpa using h
  have hm1 : ‖gibbsMoment σ μG ρ F 1‖ ≤ B * actionBound (Λ := Λ) := by
    have h := norm_gibbsMoment_le σ μG ρ hρcont hd hF hFB 1
    simpa using h
  rw [covZero_actionDensity σ μG ρ F hρcont hd]
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (actionMean_nonneg σ μG ρ hρcont hd)]
  have h1 : ‖gibbsMoment σ μG ρ F 1‖ ≤ B * actionBound (Λ := Λ) := hm1
  have h2 : ‖gibbsMoment σ μG ρ F 0‖ * actionMean σ μG ρ
      ≤ B * actionBound (Λ := Λ) :=
    mul_le_mul hm0 (actionMean_le σ μG ρ hρcont hd)
      (actionMean_nonneg σ μG ρ hρcont hd) hB
  linarith [h1, h2]

/-- The numerator of the Gibbs expectation at real `β`, written with
the density sum: `∫ exp(−βA)·F`. -/
noncomputable def gibbsNum (F : Config Λ G → ℂ) (β : ℝ) : ℂ :=
  ∫ U, (Real.exp (-(β * actionDensity σ ρ U)) : ℂ) * F U
    ∂(configMeasure μG)

/-- `gibbsExpect` is the ratio of `gibbsNum` to the partition
function. -/
theorem gibbsExpect_eq_num_div (β : ℝ) (F : Config Λ G → ℂ) :
    gibbsExpect σ μG ρ β F
      = gibbsNum σ μG ρ F β / (gibbsPartition σ μG ρ β : ℂ) := by
  unfold gibbsExpect gibbsNum gibbsPartition
  congr 1

/-- The numerator integrand is integrable (bounded on a probability
space). -/
theorem integrable_gibbsNum_integrand
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) (β : ℝ) :
    Integrable (fun U => (Real.exp (-(β * actionDensity σ ρ U)) : ℂ) * F U)
      (configMeasure μG) := by
  have hA : Measurable fun U : Config Λ G => (actionDensity σ ρ U : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_actionDensity σ ρ hρcont)
  have hexp : Measurable fun U : Config Λ G =>
      (Real.exp (-(β * actionDensity σ ρ U)) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_actionDensity σ ρ hρcont).const_mul β).neg)
  refine integrable_of_bounded μG (hexp.mul hF)
    (C := Real.exp (|β| * actionBound (Λ := Λ)) * B) fun U => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  refine mul_le_mul ?_ (hFB U) (norm_nonneg _)
    (Real.exp_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
  have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
    le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
  calc -(β * actionDensity σ ρ U) ≤ |β * actionDensity σ ρ U| := neg_le_abs _
    _ = |β| * actionDensity σ ρ U := by rw [abs_mul, abs_of_nonneg hAU]
    _ ≤ |β| * actionBound (Λ := Λ) :=
        mul_le_mul_of_nonneg_left hAle (abs_nonneg β)

/-- The pointwise Taylor bound, in the form the expansion consumes:
for `|β| ≤ 1`, the exponential's first-order defect at `A U` is at
most `(actionBound²/2)·e^{actionBound}·β²`. -/
theorem exp_defect_bound
    (hd : 0 < d) {β : ℝ} (hβ : |β| ≤ 1) (U : Config Λ G) :
    |Real.exp (-(β * actionDensity σ ρ U)) - (1 - β * actionDensity σ ρ U)|
      ≤ (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2 := by
  have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
  have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
    le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
  have hA : 0 ≤ actionBound (Λ := Λ) := actionBound_nonneg
  have h1 : (β * actionDensity σ ρ U) ^ 2 / 2 * Real.exp |β * actionDensity σ ρ U|
      ≤ (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2 := by
    have hsq : (β * actionDensity σ ρ U) ^ 2
        ≤ actionBound (Λ := Λ) ^ 2 * β ^ 2 := by
      rw [mul_comm β (actionDensity σ ρ U), mul_pow]
      exact mul_le_mul (pow_le_pow_left₀ hAU hAle 2) (le_refl _)
        (sq_nonneg β) (pow_nonneg hA 2)
    have hexp : Real.exp |β * actionDensity σ ρ U|
        ≤ Real.exp (actionBound (Λ := Λ)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [abs_mul, abs_of_nonneg hAU]
      exact le_trans (mul_le_mul_of_nonneg_right hβ hAU) (by
        rw [one_mul]; exact hAle)
    have hnn : (0:ℝ) ≤ (β * actionDensity σ ρ U) ^ 2 / 2 := by positivity
    calc (β * actionDensity σ ρ U) ^ 2 / 2 * Real.exp |β * actionDensity σ ρ U|
        ≤ (actionBound (Λ := Λ) ^ 2 * β ^ 2 / 2) * Real.exp (actionBound (Λ := Λ)) :=
          mul_le_mul (by linarith [hsq]) hexp (Real.exp_nonneg _) (by positivity)
      _ = (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2 := by
          ring
  exact le_trans (exp_neg_sub_linear_bound (β * actionDensity σ ρ U)) h1

/-- **Numerator expansion.** For `|β| ≤ 1`, the Gibbs numerator is
its first-order Taylor polynomial in `β` up to an explicit
`O(β²)` error. -/
theorem gibbsNum_firstOrder
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) {β : ℝ} (hβ : |β| ≤ 1) :
    ‖gibbsNum σ μG ρ F β
        - (gibbsMoment σ μG ρ F 0 - (β : ℂ) * gibbsMoment σ μG ρ F 1)‖
      ≤ B * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2 := by
  have hA : Measurable fun U : Config Λ G => (actionDensity σ ρ U : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_actionDensity σ ρ hρcont)
  have hIntD : Integrable
      (fun U => ((Real.exp (-(β * actionDensity σ ρ U)) : ℂ)
        - (1 - (β : ℂ) * (actionDensity σ ρ U : ℂ))) * F U)
      (configMeasure μG) := by
    have hexp : Measurable fun U : Config Λ G =>
        (Real.exp (-(β * actionDensity σ ρ U)) : ℂ) :=
      Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp ((measurable_actionDensity σ ρ hρcont).const_mul β).neg)
    have hlin : Measurable fun U : Config Λ G =>
        (1 : ℂ) - (β : ℂ) * (actionDensity σ ρ U : ℂ) :=
      measurable_const.sub (measurable_const.mul hA)
    refine integrable_of_bounded μG ((hexp.sub hlin).mul hF)
      (C := (Real.exp (actionBound (Λ := Λ)) + (1 + actionBound (Λ := Λ)))
        * B) fun U => ?_
    rw [norm_mul]
    refine mul_le_mul ?_ (hFB U) (norm_nonneg _) ?_
    · refine le_trans (norm_sub_le _ _) ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      have h1 : Real.exp (-(β * actionDensity σ ρ U))
          ≤ Real.exp (actionBound (Λ := Λ)) := by
        refine Real.exp_le_exp.mpr ?_
        have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
        have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
          le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
        calc -(β * actionDensity σ ρ U) ≤ |β * actionDensity σ ρ U| := neg_le_abs _
          _ = |β| * actionDensity σ ρ U := by rw [abs_mul, abs_of_nonneg hAU]
          _ ≤ actionBound (Λ := Λ) :=
              le_trans (mul_le_mul_of_nonneg_right hβ hAU) (by rwa [one_mul])
      have h2 : ‖(1 : ℂ) - (β : ℂ) * (actionDensity σ ρ U : ℂ)‖
          ≤ 1 + actionBound (Λ := Λ) := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_one, norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
        have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
          le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
        have : |β| * |actionDensity σ ρ U| ≤ actionBound (Λ := Λ) :=
          le_trans (mul_le_mul_of_nonneg_right hβ
            (abs_nonneg (actionDensity σ ρ U))) (by
            rwa [one_mul, abs_of_nonneg hAU])
        linarith [this]
      linarith [h1, h2]
    · have hA : 0 ≤ actionBound (Λ := Λ) := actionBound_nonneg
      positivity
  have hInt1 : Integrable (fun U => (Real.exp (-(β * actionDensity σ ρ U)) : ℂ) * F U)
      (configMeasure μG) :=
    integrable_gibbsNum_integrand σ μG ρ hρcont hd hF hFB β
  have hInt2 : Integrable
      (fun U => (1 - (β : ℂ) * (actionDensity σ ρ U : ℂ)) * F U)
      (configMeasure μG) := by
    have hlin : Measurable fun U : Config Λ G =>
        (1 : ℂ) - (β : ℂ) * (actionDensity σ ρ U : ℂ) :=
      measurable_const.sub (measurable_const.mul hA)
    refine integrable_of_bounded μG (hlin.mul hF)
      (C := (1 + actionBound (Λ := Λ)) * B) fun U => ?_
    rw [norm_mul]
    refine mul_le_mul ?_ (hFB U) (norm_nonneg _)
      (add_nonneg zero_le_one actionBound_nonneg)
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
    have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
      le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
    have h3 : |β| * |actionDensity σ ρ U| ≤ actionBound (Λ := Λ) :=
      le_trans (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)) (by
        rwa [one_mul, abs_of_nonneg hAU])
    linarith [h3]
  have hEq : gibbsNum σ μG ρ F β
        - (gibbsMoment σ μG ρ F 0 - (β : ℂ) * gibbsMoment σ μG ρ F 1)
      = ∫ U, ((Real.exp (-(β * actionDensity σ ρ U)) : ℂ)
          - (1 - (β : ℂ) * (actionDensity σ ρ U : ℂ))) * F U
          ∂(configMeasure μG) := by
    calc gibbsNum σ μG ρ F β
          - (gibbsMoment σ μG ρ F 0 - (β : ℂ) * gibbsMoment σ μG ρ F 1)
        = (∫ U, (Real.exp (-(β * actionDensity σ ρ U)) : ℂ) * F U
            ∂(configMeasure μG))
          - ∫ U, (1 - (β : ℂ) * (actionDensity σ ρ U : ℂ)) * F U
            ∂(configMeasure μG) := by
          congr 1
          simp only [gibbsMoment, pow_zero, mul_one,
            ← integral_const_mul]
          rw [← integral_sub (integrable_of_bounded μG hF hFB)
            ((integrable_mul_actionDensity_pow σ μG ρ hρcont hd hF hFB 1).const_mul
              (β : ℂ))]
          refine integral_congr_ae (ae_of_all _ fun U => ?_)
          ring
      _ = ∫ U, ((Real.exp (-(β * actionDensity σ ρ U)) : ℂ)
            - (1 - (β : ℂ) * (actionDensity σ ρ U : ℂ))) * F U
            ∂(configMeasure μG) := by
          rw [← integral_sub hInt1 hInt2]
          refine integral_congr_ae (ae_of_all _ fun U => ?_)
          ring
  rw [hEq]
  refine norm_integral_le_of_forall_bound μG hIntD fun U => ?_
  have hcast : ((Real.exp (-(β * actionDensity σ ρ U)) : ℂ)
        - (1 - (β : ℂ) * (actionDensity σ ρ U : ℂ)))
      = ((Real.exp (-(β * actionDensity σ ρ U))
          - (1 - β * actionDensity σ ρ U) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans (mul_le_mul (exp_defect_bound σ ρ hd hβ U) (hFB U)
    (norm_nonneg _) ?_) (le_of_eq (by ring))
  exact mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg actionBound_nonneg 2)
    (by norm_num)) (Real.exp_nonneg _)) (sq_nonneg β)

/-- The exponential-of-density integrand is integrable (real
valued). -/
theorem integrable_exp_neg_actionDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    Integrable (fun U => Real.exp (-(β * actionDensity σ ρ U)))
      (configMeasure μG) := by
  have hmeas : Measurable fun U : Config Λ G =>
      Real.exp (-(β * actionDensity σ ρ U)) :=
    Real.measurable_exp.comp ((measurable_actionDensity σ ρ hρcont).const_mul β).neg
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (Real.exp (|β| * actionBound (Λ := Λ))) (ae_of_all _ fun U => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.mpr ?_
  have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
  have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
    le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
  calc -(β * actionDensity σ ρ U) ≤ |β * actionDensity σ ρ U| := neg_le_abs _
    _ = |β| * actionDensity σ ρ U := by rw [abs_mul, abs_of_nonneg hAU]
    _ ≤ |β| * actionBound (Λ := Λ) :=
        mul_le_mul_of_nonneg_left hAle (abs_nonneg β)

/-- **Partition expansion.** For `|β| ≤ 1`, the partition function
is `1 − β·E₀[A]` up to an explicit `O(β²)` error. -/
theorem gibbsPartition_firstOrder
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {β : ℝ} (hβ : |β| ≤ 1) :
    |gibbsPartition σ μG ρ β - (1 - β * actionMean σ μG ρ)|
      ≤ (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2 := by
  have hIntE : Integrable (fun U => Real.exp (-(β * actionDensity σ ρ U)))
      (configMeasure μG) :=
    integrable_exp_neg_actionDensity σ μG ρ hρcont hd β
  have hIntL : Integrable (fun U => (1 : ℝ) - β * actionDensity σ ρ U)
      (configMeasure μG) :=
    (integrable_const (1 : ℝ)).sub
      ((integrable_actionDensity σ μG ρ hρcont hd).const_mul β)
  have hEq : gibbsPartition σ μG ρ β - (1 - β * actionMean σ μG ρ)
      = ∫ U, (Real.exp (-(β * actionDensity σ ρ U))
          - (1 - β * actionDensity σ ρ U)) ∂(configMeasure μG) := by
    have h1 : gibbsPartition σ μG ρ β
        = ∫ U, Real.exp (-(β * actionDensity σ ρ U)) ∂(configMeasure μG) := by
      unfold gibbsPartition
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      show Real.exp (-wilsonAction σ ρ β U)
        = Real.exp (-(β * actionDensity σ ρ U))
      rw [wilsonAction_eq σ ρ β U]
    have h2 : (1 : ℝ) - β * actionMean σ μG ρ
        = ∫ U, ((1 : ℝ) - β * actionDensity σ ρ U) ∂(configMeasure μG) := by
      have hA : Integrable (actionDensity σ ρ) (configMeasure μG) :=
        integrable_actionDensity σ μG ρ hρcont hd
      rw [integral_sub (integrable_const (1 : ℝ)) (hA.const_mul β),
        integral_const_mul]
      simp [actionMean]
    rw [h1, h2, ← integral_sub hIntE hIntL]
  rw [hEq, ← Real.norm_eq_abs]
  calc ‖∫ U, (Real.exp (-(β * actionDensity σ ρ U))
          - (1 - β * actionDensity σ ρ U)) ∂(configMeasure μG)‖
      ≤ ∫ U, ‖Real.exp (-(β * actionDensity σ ρ U))
          - (1 - β * actionDensity σ ρ U)‖ ∂(configMeasure μG) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _U : Config Λ G,
          (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2
          ∂(configMeasure μG) :=
        integral_mono_ae ((hIntE.sub hIntL).norm) (integrable_const _)
          (ae_of_all _ fun U => by
            show ‖Real.exp (-(β * actionDensity σ ρ U))
                - (1 - β * actionDensity σ ρ U)‖
              ≤ (actionBound (Λ := Λ) ^ 2 / 2
                * Real.exp (actionBound (Λ := Λ))) * β ^ 2
            rw [Real.norm_eq_abs]
            exact exp_defect_bound σ ρ hd hβ U)
    _ = (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))) * β ^ 2 := by
        simp


/-- The partition function is bounded below by the exponential of
the worst-case action: `Z_β ≥ exp(−|β|·actionBound)` (Stage 1a's
positivity, quantified). -/
theorem gibbsPartition_lower
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    Real.exp (-(|β| * actionBound (Λ := Λ))) ≤ gibbsPartition σ μG ρ β := by
  have hIntE : Integrable (fun U => Real.exp (-(β * actionDensity σ ρ U)))
      (configMeasure μG) :=
    integrable_exp_neg_actionDensity σ μG ρ hρcont hd β
  have h1 : gibbsPartition σ μG ρ β
      = ∫ U, Real.exp (-(β * actionDensity σ ρ U)) ∂(configMeasure μG) := by
    unfold gibbsPartition
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    show Real.exp (-wilsonAction σ ρ β U) = Real.exp (-(β * actionDensity σ ρ U))
    rw [wilsonAction_eq σ ρ β U]
  rw [h1]
  calc Real.exp (-(|β| * actionBound (Λ := Λ)))
      = ∫ _U : Config Λ G, Real.exp (-(|β| * actionBound (Λ := Λ)))
          ∂(configMeasure μG) := by simp
    _ ≤ ∫ U, Real.exp (-(β * actionDensity σ ρ U)) ∂(configMeasure μG) :=
        integral_mono_ae (integrable_const _) hIntE (ae_of_all _ fun U => by
          refine Real.exp_le_exp.mpr ?_
          have hAU : 0 ≤ actionDensity σ ρ U := actionDensity_nonneg σ ρ hd U
          have hAle : actionDensity σ ρ U ≤ actionBound (Λ := Λ) :=
            le_trans (le_abs_self _) (actionDensity_abs_le σ ρ hd U)
          refine neg_le_neg ?_
          calc β * actionDensity σ ρ U ≤ |β * actionDensity σ ρ U| := le_abs_self _
            _ = |β| * actionDensity σ ρ U := by rw [abs_mul, abs_of_nonneg hAU]
            _ ≤ |β| * actionBound (Λ := Λ) :=
                mul_le_mul_of_nonneg_left hAle (abs_nonneg β))

/-- **The explicit first-order remainder constant**, built only from
the observable's bound `B` and Stage 0's action bound: the numerator
defect, the covariance-size term, and the denominator-defect term,
all divided by the partition function's lower bound
`exp(−actionBound)`. -/
noncomputable def firstOrderConst (B : ℝ) : ℝ :=
  Real.exp (actionBound (Λ := Λ))
    * (B * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))
      + 2 * B * actionBound (Λ := Λ) ^ 2
      + (B + 2 * B * actionBound (Λ := Λ))
        * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))))

/-- **The first-order expansion of a Gibbs expectation, with
explicit remainder.** For every bounded measurable observable `F`
and `|β| ≤ 1`:
`‖⟨F⟩_β − (⟨F⟩₀ − β·Cov₀(F, A))‖ ≤ firstOrderConst B · β²`. -/
theorem gibbsExpect_firstOrder
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) {β : ℝ} (hβ : |β| ≤ 1) :
    ‖gibbsExpect σ μG ρ β F - (gibbsMoment σ μG ρ F 0
        - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))‖
      ≤ firstOrderConst (Λ := Λ) B * β ^ 2 := by
  have hA : 0 ≤ actionBound (Λ := Λ) := actionBound_nonneg
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hFB (fun _ => 1))
  have hN := gibbsNum_firstOrder σ μG ρ hρcont hd hF hFB hβ
  have hD := gibbsPartition_firstOrder σ μG ρ hρcont hd hβ
  have hlow := gibbsPartition_lower σ μG ρ hρcont hd β
  have hDpos : 0 < gibbsPartition σ μG ρ β := (Real.exp_pos _).trans_le hlow
  have hDne : (gibbsPartition σ μG ρ β : ℂ) ≠ 0 := by
    exact_mod_cast hDpos.ne'
  have hDge : Real.exp (-(actionBound (Λ := Λ))) ≤ gibbsPartition σ μG ρ β :=
    le_trans (Real.exp_le_exp.mpr (neg_le_neg (by
      calc |β| * actionBound (Λ := Λ) ≤ 1 * actionBound (Λ := Λ) :=
            mul_le_mul_of_nonneg_right hβ hA
        _ = actionBound (Λ := Λ) := one_mul _))) hlow
  have hcov := norm_covZero_actionDensity_le σ μG ρ hρcont hd hF hFB
  have hm0 : ‖gibbsMoment σ μG ρ F 0‖ ≤ B := by
    have h := norm_gibbsMoment_le σ μG ρ hρcont hd hF hFB 0
    simpa using h
  have hT : ‖gibbsMoment σ μG ρ F 0
      - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))‖
      ≤ B + 2 * B * actionBound (Λ := Λ) := by
    refine le_trans (norm_sub_le _ _) (add_le_add hm0 ?_)
    rw [norm_smul, Real.norm_eq_abs]
    refine le_trans (mul_le_mul_of_nonneg_left hcov (abs_nonneg β)) ?_
    calc |β| * (2 * B * actionBound (Λ := Λ))
        ≤ 1 * (2 * B * actionBound (Λ := Λ)) :=
          mul_le_mul_of_nonneg_right hβ
            (mul_nonneg (mul_nonneg (by norm_num) hB) hA)
      _ = 2 * B * actionBound (Λ := Λ) := one_mul _
  have key : gibbsNum σ μG ρ F β
        - (gibbsMoment σ μG ρ F 0
          - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
          * (gibbsPartition σ μG ρ β : ℂ)
      = (gibbsNum σ μG ρ F β
          - (gibbsMoment σ μG ρ F 0 - (β : ℂ) * gibbsMoment σ μG ρ F 1))
        - ((β : ℂ) ^ 2
          * covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))
          * (actionMean σ μG ρ : ℂ))
        - (gibbsMoment σ μG ρ F 0
          - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
          * ((gibbsPartition σ μG ρ β - (1 - β * actionMean σ μG ρ) : ℝ) : ℂ) := by
    rw [covZero_actionDensity σ μG ρ F hρcont hd]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hY : ‖(β : ℂ) ^ 2
        * covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))
        * (actionMean σ μG ρ : ℂ)‖
      ≤ (2 * B * actionBound (Λ := Λ) ^ 2) * β ^ 2 := by
    have hnorm : ‖(β : ℂ) ^ 2
          * covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))
          * (actionMean σ μG ρ : ℂ)‖
        = β ^ 2 * ‖covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))‖
          * actionMean σ μG ρ := by
      rw [norm_mul, norm_mul, norm_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (actionMean_nonneg σ μG ρ hρcont hd), sq_abs]
    rw [hnorm]
    calc β ^ 2 * ‖covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))‖
          * actionMean σ μG ρ
        = β ^ 2 * (‖covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))‖
            * actionMean σ μG ρ) := by ring
      _ ≤ β ^ 2 * ((2 * B * actionBound (Λ := Λ)) * actionBound (Λ := Λ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hcov (actionMean_le σ μG ρ hρcont hd)
              (actionMean_nonneg σ μG ρ hρcont hd)
              (mul_nonneg (mul_nonneg (by norm_num) hB) hA))
            (sq_nonneg β)
      _ = (2 * B * actionBound (Λ := Λ) ^ 2) * β ^ 2 := by ring
  have hZ : ‖(gibbsMoment σ μG ρ F 0
        - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
        * ((gibbsPartition σ μG ρ β - (1 - β * actionMean σ μG ρ) : ℝ) : ℂ)‖
      ≤ ((B + 2 * B * actionBound (Λ := Λ))
        * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))) * β ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans (mul_le_mul hT hD (abs_nonneg _)
      (add_nonneg hB (mul_nonneg (mul_nonneg (by norm_num) hB) hA)))
      (le_of_eq (by ring))
  have hM : ‖gibbsNum σ μG ρ F β
        - (gibbsMoment σ μG ρ F 0
          - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
          * (gibbsPartition σ μG ρ β : ℂ)‖
      ≤ (B * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))
        + 2 * B * actionBound (Λ := Λ) ^ 2
        + (B + 2 * B * actionBound (Λ := Λ))
          * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))) * β ^ 2 := by
    rw [key]
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans (add_le_add (norm_sub_le _ _) hZ) ?_
    refine le_trans (add_le_add (add_le_add hN hY) (le_refl _)) ?_
    exact le_of_eq (by ring)
  have hEq : gibbsExpect σ μG ρ β F - (gibbsMoment σ μG ρ F 0
        - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
      = (gibbsNum σ μG ρ F β - (gibbsMoment σ μG ρ F 0
          - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
          * (gibbsPartition σ μG ρ β : ℂ)) / (gibbsPartition σ μG ρ β : ℂ) := by
    rw [gibbsExpect_eq_num_div]
    field_simp
  have hE : Real.exp (actionBound (Λ := Λ)) * Real.exp (-(actionBound (Λ := Λ))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hfin : (B * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))
        + 2 * B * actionBound (Λ := Λ) ^ 2
        + (B + 2 * B * actionBound (Λ := Λ))
          * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))) * β ^ 2 / Real.exp (-(actionBound (Λ := Λ)))
      = firstOrderConst (Λ := Λ) B * β ^ 2 := by
    unfold firstOrderConst
    rw [div_eq_iff (Real.exp_pos _).ne',
      show (Real.exp (actionBound (Λ := Λ)) * (B * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))
        + 2 * B * actionBound (Λ := Λ) ^ 2
        + (B + 2 * B * actionBound (Λ := Λ))
          * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ))))) * β ^ 2
          * Real.exp (-(actionBound (Λ := Λ)))
        = (Real.exp (actionBound (Λ := Λ)) * Real.exp (-(actionBound (Λ := Λ))))
          * ((B * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))
        + 2 * B * actionBound (Λ := Λ) ^ 2
        + (B + 2 * B * actionBound (Λ := Λ))
          * (actionBound (Λ := Λ) ^ 2 / 2 * Real.exp (actionBound (Λ := Λ)))) * β ^ 2) by ring,
      hE, one_mul]
  rw [hEq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos,
    ← hfin]
  refine le_trans (div_le_div_of_nonneg_left (norm_nonneg _) (Real.exp_pos _)
    hDge) ?_
  exact (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr hM

/-- **The derivative at `β = 0`.** For every bounded measurable
observable `F`,
`d/dβ ⟨F⟩_β |₀ = −Cov₀(F, A)`: the derivative-of-expectation
identity at fixed finite volume, from the Gibbs density. -/
theorem hasDerivAt_gibbsExpect_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) :
    HasDerivAt (fun β : ℝ => gibbsExpect σ μG ρ β F)
      (- covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))) 0 := by
  rw [hasDerivAt_iff_tendsto]
  have hE0 : gibbsExpect σ μG ρ 0 F = gibbsMoment σ μG ρ F 0 :=
    (gibbsMoment_zero σ μG ρ F).symm
  have hC : (0:ℝ) ≤ firstOrderConst (Λ := Λ) B := by
    rw [firstOrderConst]
    refine mul_nonneg (Real.exp_nonneg _) ?_
    have hA : 0 ≤ actionBound (Λ := Λ) := actionBound_nonneg
    have hB : 0 ≤ B := le_trans (norm_nonneg _) (hFB (fun _ => 1))
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg hB (mul_nonneg (div_nonneg (pow_nonneg hA 2) (by norm_num))
        (Real.exp_nonneg _))
    · exact mul_nonneg (mul_nonneg (by norm_num) hB) (pow_nonneg hA 2)
    · exact mul_nonneg (add_nonneg hB (mul_nonneg (mul_nonneg (by norm_num) hB) hA))
        (mul_nonneg (div_nonneg (pow_nonneg hA 2) (by norm_num)) (Real.exp_nonneg _))
  refine squeeze_zero_norm' (a := fun β : ℝ => firstOrderConst (Λ := Λ) B * |β|) ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0:ℝ) < 1 by norm_num)]
      with β hβ
    rw [Metric.mem_ball, dist_zero_right] at hβ
    simp only [sub_zero]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
    have hβle : |β| ≤ 1 := hβ.le
    by_cases hβ0 : β = 0
    · subst hβ0
      simp [hE0]
    · have hR := gibbsExpect_firstOrder σ μG ρ hρcont hd hF hFB hβle
      have hform : gibbsExpect σ μG ρ β F - gibbsExpect σ μG ρ 0 F
            - β • (- covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))
          = gibbsExpect σ μG ρ β F - (gibbsMoment σ μG ρ F 0
            - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))) := by
        rw [hE0, smul_neg]
        abel
      rw [hform]
      calc ‖β‖⁻¹ * ‖gibbsExpect σ μG ρ β F - (gibbsMoment σ μG ρ F 0
              - β • covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ)))‖
          ≤ ‖β‖⁻¹ * (firstOrderConst (Λ := Λ) B * β ^ 2) :=
            mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr (norm_nonneg _))
        _ = firstOrderConst (Λ := Λ) B * |β| := by
            have hβa : |β| ≠ 0 := (abs_pos.mpr hβ0).ne'
            rw [Real.norm_eq_abs, ← sq_abs]
            field_simp
  · have h1 : Filter.Tendsto (fun β : ℝ => |β|) (𝓝 (0:ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ))
    have h2 := h1.const_mul (firstOrderConst (Λ := Λ) B)
    simpa using h2

end FirstOrder

/-! ## §4. Analyticity at `β = 0`

The Gibbs weight `exp(−βA)` extends to an entire function of a
complex coupling `z` (the configuration space is a probability space
and `A` is bounded, so the exponential's power series converges
absolutely under the integral). Numerator and denominator are
therefore analytic, the denominator's value at `0` is `1`, and the
expectation — their ratio, restricted to real `β` — is analytic
at `0`. -/

section Analyticity

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The complex exponential as a convergent power series. -/
theorem complex_exp_hasSum (w : ℂ) :
    HasSum (fun k : ℕ => w ^ k / (Nat.factorial k : ℂ)) (Complex.exp w) := by
  rw [complex_exp_eq_tsum]
  exact (Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖w‖) (fun k =>
    le_of_eq (by rw [norm_div, Complex.norm_natCast, norm_pow]))).hasSum

/-- The numerator of the Gibbs expectation at a complex coupling:
`∫ exp(−zA)·F`. Entire in `z`. -/
noncomputable def gibbsNumeratorC (F : Config Λ G → ℂ) (z : ℂ) : ℂ :=
  ∫ U, Complex.exp (-(z * (actionDensity σ ρ U : ℂ))) * F U
    ∂(configMeasure μG)

/-- The denominator at a complex coupling: `∫ exp(−zA)`. Entire
in `z`. -/
noncomputable def gibbsDenominatorC (z : ℂ) : ℂ :=
  ∫ U, Complex.exp (-(z * (actionDensity σ ρ U : ℂ))) ∂(configMeasure μG)

/-- The power series of the complex numerator: the `k`-th Taylor
coefficient is `(−1)^k/k!` times the `k`-th Gibbs moment. -/
theorem gibbsNumeratorC_eq_tsum
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) (z : ℂ) :
    gibbsNumeratorC σ μG ρ F z
      = ∑' k : ℕ, ((-z) ^ k / (Nat.factorial k : ℂ)) * gibbsMoment σ μG ρ F k := by
  have hterm : ∀ k : ℕ, Integrable
      (fun U => ((-z) ^ k / (Nat.factorial k : ℂ))
        * (F U * (actionDensity σ ρ U : ℂ) ^ k)) (configMeasure μG) :=
    fun k => (integrable_mul_actionDensity_pow σ μG ρ hρcont hd hF hFB k).const_mul _
  have hsum : Summable (fun k : ℕ =>
      ∫ U, ‖((-z) ^ k / (Nat.factorial k : ℂ))
        * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖ ∂(configMeasure μG)) := by
    refine Summable.of_norm_bounded
      (g := fun k : ℕ => B * ((‖z‖ * actionBound (Λ := Λ)) ^ k
        / (Nat.factorial k : ℝ)))
      ((Real.summable_pow_div_factorial _).mul_left B) fun k => ?_
    calc ‖∫ U, ‖((-z) ^ k / (Nat.factorial k : ℂ))
            * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖ ∂(configMeasure μG)‖
        ≤ ∫ U, ‖‖((-z) ^ k / (Nat.factorial k : ℂ))
            * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖‖ ∂(configMeasure μG) :=
          norm_integral_le_integral_norm _
      _ = ∫ U, ‖((-z) ^ k / (Nat.factorial k : ℂ))
            * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖ ∂(configMeasure μG) :=
          integral_congr_ae (ae_of_all _ fun U => by
            show ‖‖((-z) ^ k / (Nat.factorial k : ℂ))
                * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖‖
              = ‖((-z) ^ k / (Nat.factorial k : ℂ))
                * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
      _ ≤ ∫ _U : Config Λ G, B * ((‖z‖ * actionBound (Λ := Λ)) ^ k
            / (Nat.factorial k : ℝ)) ∂(configMeasure μG) :=
          integral_mono_ae (hterm k).norm (integrable_const _) (ae_of_all _ fun U => by
            show ‖((-z) ^ k / (Nat.factorial k : ℂ))
                * (F U * (actionDensity σ ρ U : ℂ) ^ k)‖
              ≤ B * ((‖z‖ * actionBound (Λ := Λ)) ^ k / (Nat.factorial k : ℝ))
            rw [norm_mul, norm_mul, norm_div, norm_pow, norm_neg,
              Complex.norm_natCast, norm_pow, Complex.norm_real]
            refine le_trans (mul_le_mul_of_nonneg_left
              (mul_le_mul (hFB U) (pow_le_pow_left₀ (abs_nonneg _)
                (actionDensity_abs_le σ ρ hd U) k)
                (pow_nonneg (abs_nonneg _) k)
                (le_trans (norm_nonneg _) (hFB U)))
              (div_nonneg (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))) ?_
            rw [mul_pow]
            have hkf : (Nat.factorial k : ℝ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
            field_simp [hkf]
            exact le_of_eq (by ring))
      _ = B * ((‖z‖ * actionBound (Λ := Λ)) ^ k / (Nat.factorial k : ℝ)) := by
          simp
  have hHas := hasSum_integral_of_summable_integral_norm hterm hsum
  have hpt : ∀ U : Config Λ G,
      ∑' k : ℕ, ((-z) ^ k / (Nat.factorial k : ℂ))
          * (F U * (actionDensity σ ρ U : ℂ) ^ k)
        = Complex.exp (-(z * (actionDensity σ ρ U : ℂ))) * F U := by
    intro U
    have h1 : ∀ k : ℕ, ((-z) ^ k / (Nat.factorial k : ℂ))
          * (F U * (actionDensity σ ρ U : ℂ) ^ k)
        = ((-(z * (actionDensity σ ρ U : ℂ))) ^ k / (Nat.factorial k : ℂ)) * F U := by
      intro k
      rw [show (-(z * (actionDensity σ ρ U : ℂ))) = (-z) * (actionDensity σ ρ U : ℂ)
        by ring, mul_pow]
      ring
    rw [tsum_congr h1, tsum_mul_right]
    exact congrArg (· * F U) (complex_exp_eq_tsum _).symm
  unfold gibbsNumeratorC gibbsMoment
  rw [tsum_congr (fun k => (integral_const_mul _ _).symm), hHas.tsum_eq]
  exact integral_congr_ae (ae_of_all _ fun U => (hpt U).symm)

/-- The Taylor series of the complex numerator, as a formal
multilinear series. -/
noncomputable def gibbsSeries (F : Config Λ G → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun k => (-1 : ℂ) ^ k / (Nat.factorial k : ℂ) * gibbsMoment σ μG ρ F k)

/-- The numerator has the Gibbs series as a power series on a ball
of explicit radius `(2·max(actionBound, 1))⁻¹` around `0`. -/
theorem hasFPowerSeriesOnBall_gibbsNumeratorC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) :
    HasFPowerSeriesOnBall (gibbsNumeratorC σ μG ρ F) (gibbsSeries σ μG ρ F) 0
      (ENNReal.ofNNReal ⟨(2 * max (actionBound (Λ := Λ)) 1)⁻¹,
        inv_nonneg.mpr (mul_nonneg (by norm_num)
          (le_trans zero_le_one (le_max_right _ _)))⟩) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hFB (fun _ => 1))
  have hA : 0 ≤ actionBound (Λ := Λ) := actionBound_nonneg
  have hM1 : (1:ℝ) ≤ max (actionBound (Λ := Λ)) 1 := le_max_right _ _
  have hAM : actionBound (Λ := Λ) ≤ max (actionBound (Λ := Λ)) 1 := le_max_left _ _
  have h2M : (0:ℝ) < 2 * max (actionBound (Λ := Λ)) 1 := by linarith [hM1]
  refine ⟨?_, ?_, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ B
      (r := ⟨(2 * max (actionBound (Λ := Λ)) 1)⁻¹,
        inv_nonneg.mpr (mul_nonneg (by norm_num)
          (le_trans zero_le_one (le_max_right _ _)))⟩) fun n => ?_
    show ‖gibbsSeries σ μG ρ F n‖
        * ((2 * max (actionBound (Λ := Λ)) 1)⁻¹) ^ n ≤ B
    have hcoef : ‖gibbsSeries σ μG ρ F n‖
        ≤ B * actionBound (Λ := Λ) ^ n / (Nat.factorial n : ℝ) := by
      unfold gibbsSeries
      rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_div,
        norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
        div_eq_inv_mul, div_eq_inv_mul, mul_one]
      exact mul_le_mul_of_nonneg_left
        (norm_gibbsMoment_le σ μG ρ hρcont hd hF hFB n)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    refine le_trans (mul_le_mul_of_nonneg_right hcoef
      (pow_nonneg (inv_nonneg.mpr h2M.le) n)) ?_
    have hr : actionBound (Λ := Λ) * (2 * max (actionBound (Λ := Λ)) 1)⁻¹
        ≤ 1 / 2 := by
      calc actionBound (Λ := Λ) * (2 * max (actionBound (Λ := Λ)) 1)⁻¹
          ≤ max (actionBound (Λ := Λ)) 1 * (2 * max (actionBound (Λ := Λ)) 1)⁻¹ :=
            mul_le_mul_of_nonneg_right hAM (inv_nonneg.mpr h2M.le)
        _ = 1 / 2 := by
            field_simp
    have hkf : (Nat.factorial n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
    calc (B * actionBound (Λ := Λ) ^ n / (Nat.factorial n : ℝ))
          * ((2 * max (actionBound (Λ := Λ)) 1)⁻¹) ^ n
        = B * ((actionBound (Λ := Λ) * (2 * max (actionBound (Λ := Λ)) 1)⁻¹) ^ n
            / (Nat.factorial n : ℝ)) := by
          rw [mul_pow]
          field_simp
      _ ≤ B * ((1 / 2) ^ n / (Nat.factorial n : ℝ)) :=
          mul_le_mul_of_nonneg_left
            ((div_le_div_iff_of_pos_right (by positivity)).mpr
              (pow_le_pow_left₀ (mul_nonneg hA (inv_nonneg.mpr h2M.le)) hr n)) hB
      _ ≤ B * 1 :=
          mul_le_mul_of_nonneg_left
            (le_trans (div_le_self (pow_nonneg (by norm_num) n)
              (by exact_mod_cast Nat.factorial_pos n))
              (pow_le_one₀ (by norm_num) (by norm_num))) hB
      _ = B := mul_one _
  · exact ENNReal.coe_pos.mpr (by exact_mod_cast inv_pos.mpr h2M)
  · intro y _
    rw [zero_add]
    have hsumm : Summable (fun k : ℕ =>
        ((-y) ^ k / (Nat.factorial k : ℂ)) * gibbsMoment σ μG ρ F k) := by
      refine Summable.of_norm_bounded
        (g := fun k : ℕ => B * ((‖y‖ * actionBound (Λ := Λ)) ^ k
          / (Nat.factorial k : ℝ)))
        ((Real.summable_pow_div_factorial _).mul_left B) fun k => ?_
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      refine le_trans (mul_le_mul_of_nonneg_left
        (norm_gibbsMoment_le σ μG ρ hρcont hd hF hFB k)
        (div_nonneg (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))) ?_
      have hkf : (Nat.factorial k : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
      refine le_of_eq ?_
      rw [mul_pow]
      field_simp [hkf]
      rw [norm_neg]
      ring
    have hHasSum : HasSum (fun k : ℕ =>
        ((-y) ^ k / (Nat.factorial k : ℂ)) * gibbsMoment σ μG ρ F k)
        (gibbsNumeratorC σ μG ρ F y) := by
      rw [gibbsNumeratorC_eq_tsum σ μG ρ hρcont hd hF hFB y]
      exact hsumm.hasSum
    have hfun : (fun n => gibbsSeries σ μG ρ F n (fun _ => y))
        = (fun k : ℕ => ((-y) ^ k / (Nat.factorial k : ℂ))
          * gibbsMoment σ μG ρ F k) := by
      funext n
      unfold gibbsSeries
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      ring_nf
    rw [hfun]
    exact hHasSum

/-- **Analyticity of the numerator** at `z = 0`. -/
theorem analyticAt_gibbsNumeratorC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) :
    AnalyticAt ℂ (gibbsNumeratorC σ μG ρ F) 0 := by
  have h := hasFPowerSeriesOnBall_gibbsNumeratorC σ μG ρ hρcont hd hF hFB
  have hAt : HasFPowerSeriesAt (gibbsNumeratorC σ μG ρ F)
      (gibbsSeries σ μG ρ F) 0 := ⟨_, h⟩
  exact hAt.analyticAt

/-- The complex denominator is the numerator of the constant
observable `1`. -/
theorem gibbsDenominatorC_eq (z : ℂ) :
    gibbsDenominatorC σ μG ρ z = gibbsNumeratorC σ μG ρ (fun _ => 1) z := by
  simp [gibbsDenominatorC, gibbsNumeratorC]

/-- The complex denominator at `0` is `1`. -/
theorem gibbsDenominatorC_zero : gibbsDenominatorC σ μG ρ 0 = 1 := by
  simp [gibbsDenominatorC]

/-- **Analyticity of the denominator** at `z = 0`. -/
theorem analyticAt_gibbsDenominatorC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) :
    AnalyticAt ℂ (gibbsDenominatorC σ μG ρ) 0 := by
  rw [funext (gibbsDenominatorC_eq σ μG ρ)]
  exact analyticAt_gibbsNumeratorC σ μG ρ hρcont hd measurable_const (B := 1)
    (fun U => by simp)

/-- At real `β`, the Gibbs expectation is the ratio of the complex
numerator and denominator evaluated at `β`. -/
theorem gibbsExpect_eq_numC_div
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (F : Config Λ G → ℂ) :
    gibbsExpect σ μG ρ β F
      = gibbsNumeratorC σ μG ρ F β / gibbsDenominatorC σ μG ρ β := by
  unfold gibbsExpect gibbsNumeratorC gibbsDenominatorC
  congr 1
  · refine integral_congr_ae (ae_of_all _ fun U => ?_)
    show (Real.exp (-wilsonAction σ ρ β U) : ℂ) * F U
      = Complex.exp (-(β * (actionDensity σ ρ U : ℂ))) * F U
    rw [Complex.ofReal_exp, wilsonAction_eq σ ρ β U]
    congr 1
    push_cast
    ring
  · rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    show (Real.exp (-wilsonAction σ ρ β U) : ℂ)
      = Complex.exp (-(β * (actionDensity σ ρ U : ℂ)))
    rw [Complex.ofReal_exp, wilsonAction_eq σ ρ β U]
    congr 1
    push_cast
    ring

/-- **Analyticity of the expectation at `β = 0`** (Stage 1c-0,
part (i)): for every bounded measurable observable `F`, the
function `β ↦ ⟨F⟩_β` is real-analytic at `β = 0`. -/
theorem analyticAt_gibbsExpect
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) :
    AnalyticAt ℝ (fun β : ℝ => gibbsExpect σ μG ρ β F) 0 := by
  have hC : AnalyticAt ℂ (fun z => gibbsNumeratorC σ μG ρ F z
      / gibbsDenominatorC σ μG ρ z) 0 :=
    (analyticAt_gibbsNumeratorC σ μG ρ hρcont hd hF hFB).div
      (analyticAt_gibbsDenominatorC σ μG ρ hρcont hd)
      (by rw [gibbsDenominatorC_zero]; exact one_ne_zero)
  have hCR : AnalyticAt ℝ (fun z => gibbsNumeratorC σ μG ρ F z
      / gibbsDenominatorC σ μG ρ z) (0 : ℂ) := hC.restrictScalars
  have hreal : AnalyticAt ℝ ((fun z => gibbsNumeratorC σ μG ρ F z
      / gibbsDenominatorC σ μG ρ z) ∘ ⇑Complex.ofRealCLM) 0 :=
    hCR.comp (f := (⇑Complex.ofRealCLM : ℝ → ℂ)) (Complex.ofRealCLM.analyticAt (0 : ℝ))
  refine hreal.congr ?_
  filter_upwards with β
  simp only [Function.comp_apply]
  exact (gibbsExpect_eq_numC_div σ μG ρ hρcont hd β F).symm

end Analyticity

/-! ## §5. The reduction: only link-sharing plaquettes contribute

At `β = 0` the Gibbs measure is the product Haar measure, so by
Stage 1a's factorization an observable's covariance with the action
density collapses to the plaquettes whose link support meets the
observable's support: every other plaquette is independent of the
observable at `β = 0` and contributes exactly its mean-field term,
which the covariance subtracts. -/

section Reduction

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The link support of a plaquette: the four links of its step
path. -/
def plaquetteLinks (x : Λ) (μ ν : Fin 4) : Finset (Link Λ) :=
  loopLinks σ x (plaquetteSteps μ ν)

/-- The plaquette's links, explicitly (commuting shifts): the
bottom, right, top and left links of the square. -/
theorem plaquetteLinks_eq
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    plaquetteLinks σ x μ ν
      = {(x, μ), (σ μ x, ν), (σ ν x, μ), (x, ν)} := by
  have h1 : (σ μ).symm (σ ν (σ μ x)) = σ ν x := by
    rw [← hσ μ ν x]
    exact Equiv.symm_apply_apply (σ μ) (σ ν x)
  simp [plaquetteLinks, loopLinks, plaquetteSteps, h1]

/-- A plaquette has at most four links. -/
theorem card_plaquetteLinks_le
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    (plaquetteLinks σ x μ ν).card ≤ 4 := by
  rw [plaquetteLinks_eq σ hσ x μ ν]
  calc ({(x, μ), (σ μ x, ν), (σ ν x, μ), (x, ν)} : Finset (Link Λ)).card
      ≤ ({(σ μ x, ν), (σ ν x, μ), (x, ν)} : Finset (Link Λ)).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ ({(σ ν x, μ), (x, ν)} : Finset (Link Λ)).card + 1 + 1 :=
        add_le_add_left (Finset.card_insert_le _ _) 1
    _ ≤ ({(x, ν)} : Finset (Link Λ)).card + 1 + 1 + 1 :=
        add_le_add_left (add_le_add_left (Finset.card_insert_le _ _) 1) 1
    _ = 4 := by rw [Finset.card_singleton]

/-- A plaquette density, as a complex observable, depends only on
the plaquette's links. -/
theorem plaquetteDensity_dependsOnlyOn
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (y : Λ) (κ₁ κ₂ : Fin 4) :
    DependsOnlyOn (fun U => (plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ))
      (plaquetteLinks σ y κ₁ κ₂) := by
  obtain ⟨fW, hfW⟩ := wilsonLoop_dependsOnlyOn σ ρ y (plaquetteSteps κ₁ κ₂)
  refine ⟨fun w => (1 : ℂ) - ((fW w).re : ℂ) / (d : ℂ), fun U => ?_⟩
  have hU : wilsonLoop σ ρ U y (plaquetteSteps κ₁ κ₂)
      = fW (fun ℓ : ↥(loopLinks σ y (plaquetteSteps κ₁ κ₂)) => U ℓ.1) := hfW U
  calc (plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ)
      = (1 : ℂ) - ((wilsonLoop σ ρ U y (plaquetteSteps κ₁ κ₂)).re : ℂ) / (d : ℂ) := by
        unfold plaquetteDensity wilsonLoop
        rw [loopProd_plaquetteSteps σ hσ]
        push_cast
        ring
    _ = (1 : ℂ) - ((fW (fun ℓ : ↥(loopLinks σ y (plaquetteSteps κ₁ κ₂))
          => U ℓ.1)).re : ℂ) / (d : ℂ) := by rw [hU]

/-- Plaquette densities are measurable complex observables. -/
theorem measurable_plaquetteDensityC
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (y : Λ) (κ₁ κ₂ : Fin 4) :
    Measurable (fun U => (plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ)) := by
  have hfun : (fun U => (plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ))
      = fun U => (1 : ℂ)
        - ((wilsonLoop σ ρ U y (plaquetteSteps κ₁ κ₂)).re : ℂ) / (d : ℂ) := by
    funext U
    unfold plaquetteDensity wilsonLoop
    rw [loopProd_plaquetteSteps σ hσ]
    push_cast
    ring
  rw [hfun]
  exact (measurable_const.sub
    ((Complex.continuous_ofReal.measurable.comp
      (measurable_wilsonLoop_re σ ρ hρcont y (plaquetteSteps κ₁ κ₂))).div_const _))

/-- Pointwise bound `‖(D_q : ℂ)‖ ≤ 2` for a plaquette density. -/
theorem norm_plaquetteDensityC_le (hd : 0 < d) (y : Λ) (κ₁ κ₂ : Fin 4)
    (U : Config Λ G) :
    ‖(plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ)‖ ≤ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h := Set.mem_Icc.mp (plaquetteDensity_mem_Icc σ ρ hd U y κ₁ κ₂)
  exact abs_le.mpr ⟨by linarith, h.2⟩

/-- Plaquette densities are integrable against the product
measure. -/
theorem integrable_plaquetteDensityC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (y : Λ) (κ₁ κ₂ : Fin 4) :
    Integrable (fun U => (plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ))
      (configMeasure μG) :=
  Integrable.of_bound
    (measurable_plaquetteDensityC σ ρ hρcont hσ y κ₁ κ₂).aestronglyMeasurable 2
    (ae_of_all _ (norm_plaquetteDensityC_le σ ρ hd y κ₁ κ₂))

/-- Products of a bounded observable with a plaquette density are
integrable. -/
theorem integrable_mul_plaquetteDensityC
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B) (y : Λ) (κ₁ κ₂ : Fin 4) :
    Integrable (fun U => F U * (plaquetteDensity σ ρ U y κ₁ κ₂ : ℂ))
      (configMeasure μG) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hFB (fun _ => 1))
  refine Integrable.of_bound
    ((hF.mul (measurable_plaquetteDensityC σ ρ hρcont hσ y κ₁ κ₂)).aestronglyMeasurable)
    (B * 2) (ae_of_all _ fun U => ?_)
  rw [norm_mul]
  exact mul_le_mul (hFB U) (norm_plaquetteDensityC_le σ ρ hd y κ₁ κ₂ U)
    (norm_nonneg _) hB

/-- The action density as a sum over unordered plaquette triples
`(x, μ, ν)` with `μ < ν`. -/
theorem actionDensity_eq_sum_triples (U : Config Λ G) :
    actionDensity σ ρ U
      = ∑ q ∈ Finset.univ.filter (fun q : Λ × Fin 4 × Fin 4 => q.2.1 < q.2.2),
          plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 := by
  have hIoi : ∀ μ : Fin 4, Finset.Ioi μ
      = Finset.univ.filter (fun ν : Fin 4 => μ < ν) := fun μ => by
    ext ν
    simp [Finset.mem_Ioi]
  rw [actionDensity]
  simp only [hIoi, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fintype.sum_prod_type]

/-- The plaquettes sharing at least one link with the support
`s`: the only ones that can contribute to a covariance at
`β = 0`. -/
def sharingPlaquettes (s : Finset (Link Λ)) :
    Finset (Λ × Fin 4 × Fin 4) :=
  Finset.univ.filter (fun q : Λ × Fin 4 × Fin 4 =>
    q.2.1 < q.2.2 ∧ (plaquetteLinks σ q.1 q.2.1 q.2.2 ∩ s).Nonempty)

/-- **The reduction.** For any observable `F` depending only on
the links in `s`, its `β = 0` covariance with the action density
is the sum of its covariances with the densities of the
link-sharing plaquettes alone. All other plaquettes factorize at
`β = 0` and their contributions cancel against the mean-field
term. -/
theorem covZero_eq_sum_sharing
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    {F : Config Λ G → ℂ} (hF : Measurable F) {B : ℝ}
    (hFB : ∀ U, ‖F U‖ ≤ B)
    {s : Finset (Link Λ)} (hFdep : DependsOnlyOn F s) :
    covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))
      = ∑ q ∈ sharingPlaquettes σ s, covZero σ μG ρ F
          (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)) := by
  classical
  set univ33 := Finset.univ.filter (fun q : Λ × Fin 4 × Fin 4 => q.2.1 < q.2.2)
    with huniv33
  set Q : Λ × Fin 4 × Fin 4 → Prop :=
    fun q => (plaquetteLinks σ q.1 q.2.1 q.2.2 ∩ s).Nonempty with hQ
  have hsh : sharingPlaquettes σ s = univ33.filter Q := by
    ext q
    simp only [sharingPlaquettes, huniv33, hQ, Finset.mem_filter, Finset.mem_univ,
      true_and, and_assoc]
  have hFD : ∀ q : Λ × Fin 4 × Fin 4, Integrable
      (fun U => F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ))
      (configMeasure μG) :=
    fun q => integrable_mul_plaquetteDensityC σ μG ρ hρcont hd hσ hF hFB q.1 q.2.1 q.2.2
  have hD : ∀ q : Λ × Fin 4 × Fin 4, Integrable
      (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ))
      (configMeasure μG) :=
    fun q => integrable_plaquetteDensityC σ μG ρ hρcont hd hσ q.1 q.2.1 q.2.2
  have hpt : ∀ U, F U * (actionDensity σ ρ U : ℂ)
      = ∑ q ∈ univ33, (F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)) := by
    intro U
    rw [actionDensity_eq_sum_triples, ← huniv33]
    push_cast
    rw [Finset.mul_sum]
  have hpt0 : ∀ U, (actionDensity σ ρ U : ℂ)
      = ∑ q ∈ univ33, ((plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)) := by
    intro U
    rw [actionDensity_eq_sum_triples, ← huniv33, Complex.ofReal_sum]
  have hIntA : ∫ U, F U * (actionDensity σ ρ U : ℂ) ∂(configMeasure μG)
      = ∑ q ∈ univ33, ∫ U, F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
          ∂(configMeasure μG) := by
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ (fun q _ => hFD q)]
  have hMeanA : ∫ U, (actionDensity σ ρ U : ℂ) ∂(configMeasure μG)
      = ∑ q ∈ univ33, ∫ U, (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
          ∂(configMeasure μG) := by
    rw [integral_congr_ae (ae_of_all _ hpt0),
      integral_finsetSum _ (fun q _ => hD q)]
  have hfact : ∀ q ∈ univ33.filter (fun q => ¬ Q q),
      ∫ U, F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
          ∂(configMeasure μG)
        = (∫ U, F U ∂(configMeasure μG))
          * ∫ U, (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
            ∂(configMeasure μG) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hdisj : Disjoint (plaquetteLinks σ q.1 q.2.1 q.2.2) s := by
      rw [Finset.disjoint_left]
      intro ℓ hℓ hℓs
      exact hq.2 ⟨ℓ, Finset.mem_inter.mpr ⟨hℓ, hℓs⟩⟩
    have h := gibbsExpect_zero_mul_of_disjoint σ μG ρ F
      (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ))
      s (plaquetteLinks σ q.1 q.2.1 q.2.2) hdisj.symm hFdep
      (plaquetteDensity_dependsOnlyOn σ ρ hσ q.1 q.2.1 q.2.2)
    rwa [gibbsExpect_zero, gibbsExpect_zero, gibbsExpect_zero] at h
  have hcov : ∀ q : Λ × Fin 4 × Fin 4, covZero σ μG ρ F
        (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ))
      = (∫ U, F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
          ∂(configMeasure μG))
        - (∫ U, F U ∂(configMeasure μG))
          * ∫ U, (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
            ∂(configMeasure μG) := by
    intro q
    unfold covZero
    rw [gibbsExpect_zero, gibbsExpect_zero, gibbsExpect_zero]
  have hmain : covZero σ μG ρ F (fun U => (actionDensity σ ρ U : ℂ))
      = (∫ U, F U * (actionDensity σ ρ U : ℂ) ∂(configMeasure μG))
        - (∫ U, F U ∂(configMeasure μG))
          * ∫ U, (actionDensity σ ρ U : ℂ) ∂(configMeasure μG) := by
    unfold covZero
    rw [gibbsExpect_zero, gibbsExpect_zero, gibbsExpect_zero]
  rw [hsh, hmain, hIntA, hMeanA,
    ← Finset.sum_filter_add_sum_filter_not univ33 Q
      (fun q => ∫ U, F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
        ∂(configMeasure μG)),
    ← Finset.sum_filter_add_sum_filter_not univ33 Q
      (fun q => ∫ U, (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
        ∂(configMeasure μG))]
  have hnsh : ∑ q ∈ univ33.filter (fun q => ¬ Q q),
        ∫ U, F U * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
          ∂(configMeasure μG)
      = (∫ U, F U ∂(configMeasure μG))
        * ∑ q ∈ univ33.filter (fun q => ¬ Q q),
          ∫ U, (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
            ∂(configMeasure μG) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q hq => hfact q hq)
  have hsumcov : ∑ q ∈ univ33.filter Q, covZero σ μG ρ F
        (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ))
      = ∑ q ∈ univ33.filter Q, (∫ U, F U
          * (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ) ∂(configMeasure μG)
          - (∫ U, F U ∂(configMeasure μG))
            * ∫ U, (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)
              ∂(configMeasure μG)) :=
    Finset.sum_congr rfl (fun q _ => hcov q)
  rw [hnsh, hsumcov, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- A covariance bound from pointwise bounds: if `‖F‖ ≤ B` and
`‖H‖ ≤ C` pointwise, then `‖Cov₀(F, H)‖ ≤ 2BC`. -/
theorem covZero_norm_le_of_bounds
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {F H : Config Λ G → ℂ} (hF : Measurable F) (hH : Measurable H)
    {B C : ℝ} (hFB : ∀ U, ‖F U‖ ≤ B) (hHC : ∀ U, ‖H U‖ ≤ C)
    (hFHB : ∀ U, ‖F U * H U‖ ≤ B * C) :
    ‖covZero σ μG ρ F H‖ ≤ B * C + B * C := by
  have h1 : ‖gibbsMoment σ μG ρ (fun U => F U * H U) 0‖ ≤ B * C := by
    have h := norm_gibbsMoment_le σ μG ρ hρcont hd (hF.mul hH) hFHB 0
    rwa [pow_zero, mul_one] at h
  have h2 : ‖gibbsMoment σ μG ρ F 0‖ ≤ B := by
    have h := norm_gibbsMoment_le σ μG ρ hρcont hd hF hFB 0
    rwa [pow_zero, mul_one] at h
  have h3 : ‖gibbsMoment σ μG ρ H 0‖ ≤ C := by
    have h := norm_gibbsMoment_le σ μG ρ hρcont hd hH hHC 0
    rwa [pow_zero, mul_one] at h
  have hEq : covZero σ μG ρ F H
      = gibbsMoment σ μG ρ (fun U => F U * H U) 0
        - gibbsMoment σ μG ρ F 0 * gibbsMoment σ μG ρ H 0 := by
    unfold covZero gibbsMoment
    rw [gibbsExpect_zero, gibbsExpect_zero, gibbsExpect_zero]
    simp
  rw [hEq]
  exact le_trans (norm_sub_le _ _)
    (add_le_add h1 (le_trans (norm_mul_le _ _) (mul_le_mul h2 h3
      (norm_nonneg _) (le_trans (norm_nonneg _) h2))))

/-- **The plaquette coefficient as a link-sharing sum.** The
first-order coefficient of a plaquette Wilson loop is the sum,
over the plaquettes sharing a link with it, of the per-plaquette
covariances. -/
theorem covZero_plaquetteLoop_eq_sum
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (actionDensity σ ρ U : ℂ))
      = ∑ q ∈ sharingPlaquettes σ (plaquetteLinks σ x μ ν),
          covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
            (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)) :=
  covZero_eq_sum_sharing σ μG ρ hρcont hd hσ
    (measurable_wilsonLoop σ ρ hρcont x (plaquetteSteps μ ν))
    (fun U => norm_wilsonLoop_le σ ρ hd U x (plaquetteSteps μ ν))
    (wilsonLoop_dependsOnlyOn σ ρ x (plaquetteSteps μ ν))

/-- **The first derivative of a plaquette expectation, as a
link-sharing sum:** `d/dβ ⟨W_p⟩_β |₀ = −∑_{q ∼ p} Cov₀(W_p, D_q)`. -/
theorem deriv_plaquetteLoop_eq
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    deriv (fun β : ℝ => gibbsExpect σ μG ρ β
        (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))) 0
      = -∑ q ∈ sharingPlaquettes σ (plaquetteLinks σ x μ ν),
          covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
            (fun U => (plaquetteDensity σ ρ U q.1 q.2.1 q.2.2 : ℂ)) := by
  have h := (hasDerivAt_gibbsExpect_zero σ μG ρ hρcont hd
    (measurable_wilsonLoop σ ρ hρcont x (plaquetteSteps μ ν))
    (fun U => norm_wilsonLoop_le σ ρ hd U x (plaquetteSteps μ ν))).deriv
  rw [h, covZero_plaquetteLoop_eq_sum σ μG ρ hρcont hd hσ x μ ν]

end Reduction

/-! ## §6. The perimeter law at first order (torus)

On the torus, a plaquette sharing a given link is one of at most
twelve: the link can occupy four slots of the plaquette, and in
each slot the plaquette is determined by the link and a free
choice of the second direction (three options). Hence the set of
plaquettes sharing links with a support `s` has cardinality at
most `12·|s|` — the first-order response of an observable sees
the *perimeter* of its support, linearly, never its area. -/

section Perimeter

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- Directions other than a given one: exactly three. -/
theorem card_filter_ne (a : Fin 4) :
    (Finset.univ.filter (fun b : Fin 4 => b ≠ a)).card = 3 := by
  have h : Finset.univ.filter (fun b : Fin 4 => b ≠ a) = Finset.univ \ {a} := by
    ext b
    simp
  rw [h, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin, Finset.card_singleton]

/-- The candidate plaquettes through a link `ℓ`: the four slots
(bottom, right, top, left), each with a free second direction. -/
def candSet (N : ℕ) (ℓ : Link (Fin 4 → ZMod N)) :
    Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image (fun a => (ℓ.1, ℓ.2, a))
  ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))
  ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))
  ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => (ℓ.1, a, ℓ.2))

/-- At most twelve plaquettes pass through a given link. -/
theorem card_candSet_le (N : ℕ) (ℓ : Link (Fin 4 → ZMod N)) :
    (candSet N ℓ).card ≤ 12 := by
  have hI : ∀ f : Fin 4 → (Fin 4 → ZMod N) × Fin 4 × Fin 4,
      ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image f).card ≤ 3 :=
    fun f => (Finset.card_image_le).trans (le_of_eq (card_filter_ne ℓ.2))
  unfold candSet
  calc ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card
      ≤ (((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))).card)
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card := Finset.card_union_le _ _
    _ ≤ (((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))).card
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))).card)
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card :=
          add_le_add (Finset.card_union_le _ _) (le_refl _)
    _ ≤ (((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))).card
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))).card
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))).card)
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card :=
          add_le_add (add_le_add (Finset.card_union_le _ _) (le_refl _)) (le_refl _)
    _ ≤ ((3 + 3) + 3) + 3 :=
          add_le_add (add_le_add (add_le_add (hI _) (hI _)) (hI _)) (hI _)
    _ = 12 := rfl

/-- Every plaquette through a link is among the candidates:
membership in the plaquette's link set forces one of the four
slots, and the slot determines the plaquette from the link. -/
theorem mem_candSet_of_mem_plaquetteLinks (N : ℕ) [NeZero N]
    {y : Fin 4 → ZMod N} {κ ν : Fin 4} (hκν : κ ≠ ν)
    {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ plaquetteLinks (torusShift N) y κ ν) :
    (y, κ, ν) ∈ candSet N ℓ := by
  rw [plaquetteLinks_eq (torusShift N) (torusShift_comm N) y κ ν] at hℓ
  have hA : ∀ a : Fin 4, a ≠ ℓ.2 → (ℓ.1, ℓ.2, a) ∈ candSet N ℓ :=
    fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)))
  have hB : ∀ a : Fin 4, a ≠ ℓ.2 → ((torusShift N a).symm ℓ.1, a, ℓ.2)
      ∈ candSet N ℓ :=
    fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)))
  have hC : ∀ a : Fin 4, a ≠ ℓ.2 → ((torusShift N a).symm ℓ.1, ℓ.2, a)
      ∈ candSet N ℓ :=
    fun a ha => Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩))
  have hD : ∀ a : Fin 4, a ≠ ℓ.2 → (ℓ.1, a, ℓ.2) ∈ candSet N ℓ :=
    fun a ha => Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)
  rcases Finset.mem_insert.mp hℓ with h | hℓ
  · subst h
    exact hA ν (fun hh => hκν hh.symm)
  rcases Finset.mem_insert.mp hℓ with h | hℓ
  · subst h
    have hmem := hB κ hκν
    rw [Equiv.symm_apply_apply] at hmem
    exact hmem
  rcases Finset.mem_insert.mp hℓ with h | hℓ
  · subst h
    have hmem := hC ν (fun hh => hκν hh.symm)
    rw [Equiv.symm_apply_apply] at hmem
    exact hmem
  · have h : ℓ = (y, ν) := Finset.mem_singleton.mp hℓ
    subst h
    exact hD κ hκν

/-- **Perimeter counting:** the plaquettes sharing a link with a
support `s` number at most `12·|s|`. -/
theorem card_sharingPlaquettes_le (N : ℕ) [NeZero N] (s : Finset (Link (Fin 4 → ZMod N))) :
    (sharingPlaquettes (torusShift N) s).card ≤ 12 * s.card := by
  refine le_trans (Finset.card_le_card ?_)
    (le_trans ((Finset.card_biUnion_le (s := s) (t := candSet N))) ?_)
  · intro q hq
    simp only [sharingPlaquettes, Finset.mem_filter, Finset.mem_univ, true_and]
      at hq
    obtain ⟨ℓ, hℓ⟩ := hq.2
    rw [Finset.mem_inter] at hℓ
    exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ.2,
      mem_candSet_of_mem_plaquetteLinks N (ne_of_lt hq.1) hℓ.1⟩
  · refine le_trans (Finset.sum_le_sum fun ℓ _ => card_candSet_le N ℓ) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The perimeter bound.** The first-order coefficient of a
Wilson loop on the torus is bounded by `48·d` times the number
of links in the loop: the response is a perimeter law at first
order. (`48 = 12` candidates per link times the per-plaquette
covariance bound `4d`.) -/
theorem covZero_wilsonLoop_perimeter_bound
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (N : ℕ) [NeZero N] (s : Fin 4 → ZMod N) (steps : List Step) :
    ‖covZero (torusShift N) μG ρ
        (fun U => wilsonLoop (torusShift N) ρ U s steps)
        (fun U => (actionDensity (torusShift N) ρ U : ℂ))‖
      ≤ (48 * (d : ℝ)) * (loopLinks (torusShift N) s steps).card := by
  have hB : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  rw [covZero_eq_sum_sharing (torusShift N) μG ρ hρcont hd (torusShift_comm N)
    (measurable_wilsonLoop (torusShift N) ρ hρcont s steps)
    (fun U => norm_wilsonLoop_le (torusShift N) ρ hd U s steps)
    (wilsonLoop_dependsOnlyOn (torusShift N) ρ s steps)]
  have hterm : ∀ q ∈ sharingPlaquettes (torusShift N)
        (loopLinks (torusShift N) s steps),
      ‖covZero (torusShift N) μG ρ
          (fun U => wilsonLoop (torusShift N) ρ U s steps)
          (fun U => (plaquetteDensity (torusShift N) ρ U q.1 q.2.1 q.2.2 : ℂ))‖
        ≤ 4 * (d : ℝ) := by
    intro q _
    refine le_trans (covZero_norm_le_of_bounds (torusShift N) μG ρ hρcont hd
      (measurable_wilsonLoop (torusShift N) ρ hρcont s steps)
      (measurable_plaquetteDensityC (torusShift N) ρ hρcont (torusShift_comm N)
        q.1 q.2.1 q.2.2)
      (fun U => norm_wilsonLoop_le (torusShift N) ρ hd U s steps)
      (fun U => norm_plaquetteDensityC_le (torusShift N) ρ hd q.1 q.2.1 q.2.2 U)
      (fun U => ?_)) (le_of_eq (by ring))
    rw [norm_mul]
    exact mul_le_mul (norm_wilsonLoop_le (torusShift N) ρ hd U s steps)
      (norm_plaquetteDensityC_le (torusShift N) ρ hd q.1 q.2.1 q.2.2 U)
      (norm_nonneg _) (le_trans (norm_nonneg _)
        (norm_wilsonLoop_le (torusShift N) ρ hd U s steps))
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  · rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (card_sharingPlaquettes_le N (loopLinks (torusShift N) s steps)))
      (mul_nonneg (by norm_num) hB)) (le_of_eq ?_)
    push_cast
    ring

/-- For a single plaquette the bound reads `‖κ_p‖ ≤ 192·d`
(`48·d` times the four links of the plaquette). -/
theorem covZero_plaquetteLoop_norm_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (N : ℕ) [NeZero N] (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    ‖covZero (torusShift N) μG ρ
        (fun U => wilsonLoop (torusShift N) ρ U x (plaquetteSteps μ ν))
        (fun U => (actionDensity (torusShift N) ρ U : ℂ))‖
      ≤ 192 * (d : ℝ) := by
  refine le_trans (covZero_wilsonLoop_perimeter_bound μG ρ hρcont hd N x
    (plaquetteSteps μ ν)) ?_
  have h4 : ((loopLinks (torusShift N) x (plaquetteSteps μ ν)).card : ℝ)
      ≤ 4 := by
    exact_mod_cast card_plaquetteLinks_le (torusShift N) (torusShift_comm N)
      x μ ν
  calc (48 * (d : ℝ)) * ((loopLinks (torusShift N) x (plaquetteSteps μ ν)).card : ℝ)
      ≤ (48 * (d : ℝ)) * 4 :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = 192 * (d : ℝ) := by ring

end Perimeter

/-! ## §7. The circle instance: `κ_p = -1/2`

For the circle group with its fundamental representation (`d = 1`)
on the torus with `N ≥ 2`, the per-plaquette covariances are
evaluated exactly: the only nonzero one is the plaquette's own,
`Cov₀(W_p, D_p) = -1/2`, so `κ_p = -1/2` and the plaquette
expectation begins `⟨W_p⟩_β = β/2 + O(β²)` — matching the
vacuum-portrait sampler's small-β measurement (`≈ 0.124` at
`β = 0.25` against the predicted `0.125`). -/

section CircleEval

variable {N : ℕ} [NeZero N]

/-- For a circle element, conjugation is inversion. -/
theorem conj_circle_coe (z : Circle) :
    starRingEnd ℂ (z : ℂ) = ((z : ℂ))⁻¹ :=
  (Circle.coe_inv_eq_conj z).symm.trans (Circle.coe_inv z)

/-- A circle element times its conjugate is `1`. -/
theorem circle_coe_mul_conj (z : Circle) :
    (z : ℂ) * starRingEnd ℂ (z : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe z]
  norm_num

/-- **Character orthogonality on the circle**, proved by
translation invariance: if `w^k ≠ 1` for some circle element
`w`, the `k`-th character integrates to zero. -/
theorem integral_circle_pow_eq_zero {k : ℕ} (w : Circle) (hw : (w : ℂ) ^ k ≠ 1) :
    ∫ z : Circle, ((z : ℂ)) ^ k ∂(haarProb Circle) = 0 := by
  have hInv : ∫ z : Circle, ((z : ℂ)) ^ k ∂(haarProb Circle)
      = (w : ℂ) ^ k * ∫ z : Circle, ((z : ℂ)) ^ k ∂(haarProb Circle) := by
    calc ∫ z : Circle, ((z : ℂ)) ^ k ∂(haarProb Circle)
        = ∫ z : Circle, ((w * z : Circle) : ℂ) ^ k ∂(haarProb Circle) :=
          (integral_mul_left_eq_self (fun z : Circle => ((z : ℂ)) ^ k) w).symm
      _ = ∫ z : Circle, (w : ℂ) ^ k * ((z : ℂ)) ^ k ∂(haarProb Circle) :=
          integral_congr_ae (ae_of_all _ fun z => by
            show ((w * z : Circle) : ℂ) ^ k = (w : ℂ) ^ k * ((z : ℂ)) ^ k
            rw [Circle.coe_mul, mul_pow])
      _ = (w : ℂ) ^ k * ∫ z : Circle, ((z : ℂ)) ^ k ∂(haarProb Circle) :=
          integral_const_mul _ _
  have h2 : ((w : ℂ) ^ k - 1) * ∫ z : Circle, ((z : ℂ)) ^ k ∂(haarProb Circle)
      = 0 := by
    rw [sub_mul, one_mul, ← hInv, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hw)

/-- The first character integrates to zero. -/
theorem integral_circle_coe : ∫ z : Circle, (z : ℂ) ∂(haarProb Circle) = 0 := by
  have h := integral_circle_pow_eq_zero (k := 1) ⟨-1, by exact mem_sphere_zero_iff_norm.mpr (by simp)⟩ (by
    show ((-1 : ℂ)) ^ 1 ≠ 1
    rw [pow_one]
    intro hI
    have h2 := congrArg Complex.re hI
    simp only [Complex.neg_re, Complex.one_re] at h2
    norm_num at h2)
  simpa using h

/-- The second character integrates to zero. -/
theorem integral_circle_coe_sq :
    ∫ z : Circle, ((z : ℂ)) ^ 2 ∂(haarProb Circle) = 0 :=
  integral_circle_pow_eq_zero (k := 2) ⟨Complex.I, by exact mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩ (by
    show (Complex.I : ℂ) ^ 2 ≠ 1
    rw [pow_two, Complex.I_mul_I]
    intro hI
    have h2 := congrArg Complex.re hI
    norm_num [Complex.neg_re, Complex.one_re] at h2)

/-- The inverse character integrates to zero. -/
theorem integral_circle_coe_inv :
    ∫ z : Circle, ((z : ℂ))⁻¹ ∂(haarProb Circle) = 0 := by
  rw [integral_congr_ae (ae_of_all _ fun z => (conj_circle_coe z).symm),
    integral_conj, integral_circle_coe]
  exact map_zero (starRingEnd ℂ)

/-- The inverse-square character integrates to zero. -/
theorem integral_circle_coe_sq_inv :
    ∫ z : Circle, (((z : ℂ)) ^ 2)⁻¹ ∂(haarProb Circle) = 0 := by
  have hpt : ∀ z : Circle, (((z : ℂ)) ^ 2)⁻¹
      = starRingEnd ℂ (((z : ℂ)) ^ 2) := by
    intro z
    have h1 : ((z : ℂ)) ^ 2 * starRingEnd ℂ (((z : ℂ)) ^ 2) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
        Circle.norm_coe z]
      norm_num
    exact (eq_inv_of_mul_eq_one_right h1).symm
  rw [integral_congr_ae (ae_of_all _ hpt), integral_conj, integral_circle_coe_sq]
  exact map_zero (starRingEnd ℂ)

/-- The trace of the circle representation is the coercion. -/
theorem trace_repMatrix_circleRep (g : Circle) :
    Matrix.trace (repMatrix circleRep g) = (g : ℂ) := by
  have h : repMatrix circleRep g = Matrix.of (fun _ _ => (g : ℂ)) := rfl
  rw [h, Matrix.trace]
  simp [Matrix.diag, Fin.sum_univ_one, Matrix.of_apply]

/-- A circle Wilson loop is the coercion of its loop product. -/
theorem wilsonLoop_circleRep (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (U : Config (Fin 4 → ZMod N) Circle) (s : Fin 4 → ZMod N)
    (steps : List Step) :
    wilsonLoop σ circleRep U s steps
      = ((loopProd σ U s steps : Circle) : ℂ) := by
  unfold wilsonLoop
  exact trace_repMatrix_circleRep _

/-- The four links of a torus plaquette are pairwise distinct
(`N ≥ 2`, distinct directions): bottom ≠ right ≠ top ≠ left in
the six comparisons. -/
theorem plaquette_four_links_distinct (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ ≠ ν) :
    (x, μ) ≠ ((torusShift N μ) x, ν) ∧ (x, μ) ≠ ((torusShift N ν) x, μ)
      ∧ (x, μ) ≠ (x, ν) ∧ ((torusShift N μ) x, ν) ≠ ((torusShift N ν) x, μ)
      ∧ ((torusShift N μ) x, ν) ≠ (x, ν) ∧ ((torusShift N ν) x, μ) ≠ (x, ν) :=
  ⟨fun h => hμν (Prod.ext_iff.mp h).2,
   fun h => (torusShift_ne_self N hN ν x) (Prod.ext_iff.mp h).1.symm,
   fun h => hμν (Prod.ext_iff.mp h).2,
   fun h => (fun hh : ν = μ => hμν hh.symm) (Prod.ext_iff.mp h).2,
   fun h => (torusShift_ne_self N hN μ x) (Prod.ext_iff.mp h).1,
   fun h => hμν (Prod.ext_iff.mp h).2⟩

/-- The per-link factor of a plaquette character: `z` on the two
forward links, `z⁻¹` on the two backward links, `1` elsewhere. -/
noncomputable def phiFactor (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (ℓ : Link (Fin 4 → ZMod N))
    (z : Circle) : ℂ :=
  if ℓ = (y, κ) then (z : ℂ)
  else if ℓ = ((σ κ) y, ν) then (z : ℂ)
  else if ℓ = ((σ ν) y, κ) then ((z : ℂ))⁻¹
  else if ℓ = (y, ν) then ((z : ℂ))⁻¹
  else 1

theorem phiFactor_fst (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (z : Circle) :
    phiFactor σ y κ ν (y, κ) z = (z : ℂ) := by
  unfold phiFactor
  rw [if_pos rfl]

theorem phiFactor_snd (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (z : Circle)
    (h1 : ((σ κ) y, ν) ≠ (y, κ)) :
    phiFactor σ y κ ν ((σ κ) y, ν) z = (z : ℂ) := by
  unfold phiFactor
  rw [if_neg h1, if_pos rfl]

theorem phiFactor_thd (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (z : Circle)
    (h1 : ((σ ν) y, κ) ≠ (y, κ)) (h2 : ((σ ν) y, κ) ≠ ((σ κ) y, ν)) :
    phiFactor σ y κ ν ((σ ν) y, κ) z = ((z : ℂ))⁻¹ := by
  unfold phiFactor
  rw [if_neg h1, if_neg h2, if_pos rfl]

theorem phiFactor_fth (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (z : Circle)
    (h1 : (y, ν) ≠ (y, κ)) (h2 : (y, ν) ≠ ((σ κ) y, ν))
    (h3 : (y, ν) ≠ ((σ ν) y, κ)) :
    phiFactor σ y κ ν (y, ν) z = ((z : ℂ))⁻¹ := by
  unfold phiFactor
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos rfl]

/-- Away from the two backward links, a plaquette factor is the
character or `1` (as a function of the link value). -/
theorem phiFactor_eq_or_one (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (ℓ : Link (Fin 4 → ZMod N))
    (h1 : ℓ ≠ ((σ ν) y, κ)) (h2 : ℓ ≠ (y, ν)) :
    (∀ z : Circle, phiFactor σ y κ ν ℓ z = (z : ℂ))
      ∨ (∀ z : Circle, phiFactor σ y κ ν ℓ z = 1) := by
  by_cases h3 : ℓ = (y, κ)
  · exact Or.inl (fun z => h3 ▸ phiFactor_fst σ y κ ν z)
  by_cases h4 : ℓ = ((σ κ) y, ν)
  · exact Or.inl (fun z => h4 ▸ phiFactor_snd σ y κ ν z (h4 ▸ h3))
  · refine Or.inr (fun z => ?_)
    unfold phiFactor
    rw [if_neg h3, if_neg h4, if_neg h1, if_neg h2]

/-- Away from the two forward links, a plaquette factor is the
inverse character or `1`. -/
theorem phiFactor_eq_inv_or_one (σ : Fin 4 → Equiv.Perm (Fin 4 → ZMod N))
    (y : Fin 4 → ZMod N) (κ ν : Fin 4) (ℓ : Link (Fin 4 → ZMod N))
    (h1 : ℓ ≠ (y, κ)) (h2 : ℓ ≠ ((σ κ) y, ν)) :
    (∀ z : Circle, phiFactor σ y κ ν ℓ z = ((z : ℂ))⁻¹)
      ∨ (∀ z : Circle, phiFactor σ y κ ν ℓ z = 1) := by
  by_cases h3 : ℓ = ((σ ν) y, κ)
  · exact Or.inl (fun z => h3 ▸ phiFactor_thd σ y κ ν z (h3 ▸ h1) (h3 ▸ h2))
  by_cases h4 : ℓ = (y, ν)
  · exact Or.inl (fun z => h4 ▸ phiFactor_fth σ y κ ν z (h4 ▸ h1) (h4 ▸ h2)
      (h4 ▸ h3))
  · refine Or.inr (fun z => ?_)
    unfold phiFactor
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- **The plaquette character as a product of per-link factors**
over all links of the lattice. -/
theorem wilsonLoop_plaquette_eq_prod (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ ≠ ν) (U : Config (Fin 4 → ZMod N) Circle) :
    wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
      = ∏ ℓ : Link (Fin 4 → ZMod N),
          phiFactor (torusShift N) x μ ν ℓ (U ℓ) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := plaquette_four_links_distinct hN x hμν
  have hprod : ∏ ℓ : Link (Fin 4 → ZMod N),
        phiFactor (torusShift N) x μ ν ℓ (U ℓ)
      = ∏ ℓ ∈ plaquetteLinks (torusShift N) x μ ν,
          phiFactor (torusShift N) x μ ν ℓ (U ℓ) := by
    refine (Finset.prod_subset (Finset.subset_univ _) (fun ℓ _ hℓ => ?_)).symm
    rw [plaquetteLinks_eq (torusShift N) (torusShift_comm N) x μ ν] at hℓ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ
    unfold phiFactor
    rw [if_neg hℓ.1, if_neg hℓ.2.1, if_neg hℓ.2.2.1, if_neg hℓ.2.2.2]
  rw [wilsonLoop_circleRep, loopProd_plaquetteSteps (torusShift N)
    (torusShift_comm N)]
  show ((plaquette (torusShift N) U x μ ν : Circle) : ℂ) = _
  unfold plaquette
  simp only [Circle.coe_mul, Circle.coe_inv]
  rw [hprod, plaquetteLinks_eq (torusShift N) (torusShift_comm N) x μ ν,
    Finset.prod_insert (by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨d1, d2, d3⟩),
    Finset.prod_insert (by
      rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨d4, d5⟩),
    Finset.prod_insert (by
      rw [Finset.mem_singleton]
      exact d6),
    Finset.prod_singleton,
    phiFactor_fst, phiFactor_snd _ _ _ _ _ (Ne.symm d1),
    phiFactor_thd _ _ _ _ _ (Ne.symm d2) (Ne.symm d4),
    phiFactor_fth _ _ _ _ _ (Ne.symm d3) (Ne.symm d5) (Ne.symm d6)]
  ring


/-- `1 ≠ 0` in `ZMod N` for `N ≥ 2`. -/
theorem one_ne_zero_zmod (hN : 2 ≤ N) : (1 : ZMod N) ≠ 0 := by
  intro h
  have hdvd : N ∣ 1 := (ZMod.natCast_eq_zero_iff 1 N).mp (by exact_mod_cast h)
  have hle := Nat.le_of_dvd one_pos hdvd
  omega

/-- The product of two plaquette characters integrates link by
link. -/
theorem integral_wilsonLoop_mul (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ ≠ ν) (y : Fin 4 → ZMod N)
    {κ₁ κ₂ : Fin 4} (hκ : κ₁ ≠ κ₂) :
    ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
        ∂(configMeasure (haarProb Circle))
      = ∏ ℓ : Link (Fin 4 → ZMod N), ∫ z : Circle,
          phiFactor (torusShift N) x μ ν ℓ z
            * phiFactor (torusShift N) y κ₁ κ₂ ℓ z ∂(haarProb Circle) := by
  have h1 : ∀ U : Config (Fin 4 → ZMod N) Circle,
      wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
      = ∏ ℓ : Link (Fin 4 → ZMod N), (phiFactor (torusShift N) x μ ν ℓ (U ℓ)
          * phiFactor (torusShift N) y κ₁ κ₂ ℓ (U ℓ)) := by
    intro U
    rw [wilsonLoop_plaquette_eq_prod hN x hμν U,
      wilsonLoop_plaquette_eq_prod hN y hκ U, ← Finset.prod_mul_distrib]
  rw [integral_congr_ae (ae_of_all _ h1)]
  show ∫ U, ∏ ℓ : Link (Fin 4 → ZMod N), (phiFactor (torusShift N) x μ ν ℓ (U ℓ)
        * phiFactor (torusShift N) y κ₁ κ₂ ℓ (U ℓ))
      ∂(Measure.pi (fun _ : Link (Fin 4 → ZMod N) => haarProb Circle)) = _
  exact integral_fintype_prod_eq_prod
    (μ := fun _ : Link (Fin 4 → ZMod N) => haarProb Circle)
    (fun ℓ (z : Circle) => phiFactor (torusShift N) x μ ν ℓ z
      * phiFactor (torusShift N) y κ₁ κ₂ ℓ z)

/-- The product of a plaquette character with a conjugate
plaquette character integrates link by link. -/
theorem integral_wilsonLoop_mul_conj (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ ≠ ν) (y : Fin 4 → ZMod N)
    {κ₁ κ₂ : Fin 4} (hκ : κ₁ ≠ κ₂) :
    ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
            (plaquetteSteps κ₁ κ₂))
        ∂(configMeasure (haarProb Circle))
      = ∏ ℓ : Link (Fin 4 → ZMod N), ∫ z : Circle,
          phiFactor (torusShift N) x μ ν ℓ z
            * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ z)
            ∂(haarProb Circle) := by
  have h1 : ∀ U : Config (Fin 4 → ZMod N) Circle,
      wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
            (plaquetteSteps κ₁ κ₂))
      = ∏ ℓ : Link (Fin 4 → ZMod N), (phiFactor (torusShift N) x μ ν ℓ (U ℓ)
          * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ (U ℓ))) := by
    intro U
    rw [wilsonLoop_plaquette_eq_prod hN x hμν U,
      wilsonLoop_plaquette_eq_prod hN y hκ U, map_prod]
    exact Finset.prod_mul_distrib.symm
  rw [integral_congr_ae (ae_of_all _ h1)]
  show ∫ U, ∏ ℓ : Link (Fin 4 → ZMod N), (phiFactor (torusShift N) x μ ν ℓ (U ℓ)
        * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ (U ℓ)))
      ∂(Measure.pi (fun _ : Link (Fin 4 → ZMod N) => haarProb Circle)) = _
  exact integral_fintype_prod_eq_prod
    (μ := fun _ : Link (Fin 4 → ZMod N) => haarProb Circle)
    (fun ℓ (z : Circle) => phiFactor (torusShift N) x μ ν ℓ z
      * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ z))

/-- Per-link vanishing, plain product: at a forward link of the
second plaquette that is not a backward link of the first, the
combined character is `z²` or `z`. -/
theorem integral_phiFactor_mul_eq_zero (x : Fin 4 → ZMod N) {μ ν : Fin 4}
    (y : Fin 4 → ZMod N) {κ₁ κ₂ : Fin 4} (ℓ : Link (Fin 4 → ZMod N))
    (hp : (∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z = (z : ℂ))
      ∨ (∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z = 1))
    (hq : ∀ z : Circle, phiFactor (torusShift N) y κ₁ κ₂ ℓ z = (z : ℂ)) :
    ∫ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * phiFactor (torusShift N) y κ₁ κ₂ ℓ z ∂(haarProb Circle) = 0 := by
  rcases hp with hp | hp
  · have hpt : ∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * phiFactor (torusShift N) y κ₁ κ₂ ℓ z = ((z : ℂ)) ^ 2 :=
      fun z => by rw [hp z, hq z, pow_two]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact integral_circle_coe_sq
  · have hpt : ∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * phiFactor (torusShift N) y κ₁ κ₂ ℓ z = (z : ℂ) :=
      fun z => by rw [hp z, hq z, one_mul]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact integral_circle_coe

/-- Per-link vanishing, conjugate product: the combined character
is `(z²)⁻¹` or `z⁻¹`. -/
theorem integral_phiFactor_mul_conj_eq_zero (x : Fin 4 → ZMod N) {μ ν : Fin 4}
    (y : Fin 4 → ZMod N) {κ₁ κ₂ : Fin 4} (ℓ : Link (Fin 4 → ZMod N))
    (hp : (∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z = ((z : ℂ))⁻¹)
      ∨ (∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z = 1))
    (hq : ∀ z : Circle, phiFactor (torusShift N) y κ₁ κ₂ ℓ z = (z : ℂ)) :
    ∫ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ z)
        ∂(haarProb Circle) = 0 := by
  rcases hp with hp | hp
  · have hpt : ∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ z)
        = (((z : ℂ)) ^ 2)⁻¹ :=
      fun z => by rw [hp z, hq z, conj_circle_coe, ← mul_inv_rev, ← pow_two]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact integral_circle_coe_sq_inv
  · have hpt : ∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * starRingEnd ℂ (phiFactor (torusShift N) y κ₁ κ₂ ℓ z) = ((z : ℂ))⁻¹ :=
      fun z => by rw [hp z, hq z, conj_circle_coe, one_mul]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact integral_circle_coe_inv

/-- **Vanishing of the plain mixed moment for every ordered pair
of plaquettes** (including `q = p`): one of the second
plaquette's forward links always carries a character whose
integral against the first plaquette's factor vanishes. The
case analysis uses only the link combinatorics of the torus. -/
theorem integral_wilsonLoop_mul_eq_zero (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {κ₁ κ₂ : Fin 4} (hκ : κ₁ < κ₂) :
    ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
        ∂(configMeasure (haarProb Circle)) = 0 := by
  rw [integral_wilsonLoop_mul hN x (ne_of_lt hμν) y (ne_of_lt hκ)]
  obtain ⟨dq1, -, -, -, -, -⟩ := plaquette_four_links_distinct hN y (ne_of_lt hκ)
  by_cases hA : (y, κ₁) = ((torusShift N ν) x, μ) ∨ (y, κ₁) = (x, ν)
  · rcases hA with hA | hA
    · simp only [Prod.mk.injEq] at hA
      obtain ⟨hf1, hs1⟩ := hA
      by_cases hB : ((torusShift N κ₁) y, κ₂) = ((torusShift N ν) x, μ)
          ∨ ((torusShift N κ₁) y, κ₂) = (x, ν)
      · rcases hB with hB | hB
        · simp only [Prod.mk.injEq] at hB
          rw [hs1, hf1] at hB
          exact absurd hB.1 (torusShift_ne_self N hN μ ((torusShift N ν) x))
        · simp only [Prod.mk.injEq] at hB
          have hB1 := hB.1
          rw [hs1, hf1] at hB1
          have hcoord := congrFun hB1 μ
          rw [torusShift_apply, Pi.add_apply, torusShift_apply, Pi.add_apply,
            Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt hμν)]
            at hcoord
          simp only [zero_add] at hcoord
          have h10' : (1 : ZMod N) = 0 := by
            have h := congrArg (fun t : ZMod N => t - x μ) hcoord
            simpa using h
          exact absurd h10' (one_ne_zero_zmod hN)
      · push_neg at hB
        refine Finset.prod_eq_zero
          (Finset.mem_univ ((torusShift N κ₁) y, κ₂)) ?_
        exact integral_phiFactor_mul_eq_zero x y _
          (phiFactor_eq_or_one _ _ _ _ _ hB.1 hB.2)
          (fun z => phiFactor_snd _ _ _ _ z (Ne.symm dq1))
    · simp only [Prod.mk.injEq] at hA
      obtain ⟨hf1, hs1⟩ := hA
      by_cases hB : ((torusShift N κ₁) y, κ₂) = ((torusShift N ν) x, μ)
          ∨ ((torusShift N κ₁) y, κ₂) = (x, ν)
      · rcases hB with hB | hB
        · simp only [Prod.mk.injEq] at hB
          have hlt : ν < μ := hB.2 ▸ (hs1 ▸ hκ)
          exact absurd hlt (not_lt.mpr (le_of_lt hμν))
        · simp only [Prod.mk.injEq] at hB
          have hB1 := hB.1
          rw [hs1, hf1] at hB1
          exact absurd hB1 (torusShift_ne_self N hN ν x)
      · push_neg at hB
        refine Finset.prod_eq_zero
          (Finset.mem_univ ((torusShift N κ₁) y, κ₂)) ?_
        exact integral_phiFactor_mul_eq_zero x y _
          (phiFactor_eq_or_one _ _ _ _ _ hB.1 hB.2)
          (fun z => phiFactor_snd _ _ _ _ z (Ne.symm dq1))
  · push_neg at hA
    refine Finset.prod_eq_zero (Finset.mem_univ (y, κ₁)) ?_
    exact integral_phiFactor_mul_eq_zero x y _
      (phiFactor_eq_or_one _ _ _ _ _ hA.1 hA.2)
      (fun z => phiFactor_fst _ _ _ _ z)

/-- **Vanishing of the conjugate mixed moment for `q ≠ p`**: one
of the second plaquette's forward links, conjugated, always
carries an inverse character whose integral against the first
plaquette's factor vanishes. -/
theorem integral_wilsonLoop_mul_conj_eq_zero (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {κ₁ κ₂ : Fin 4} (hκ : κ₁ < κ₂) (hqp : (y, κ₁, κ₂) ≠ (x, μ, ν)) :
    ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
            (plaquetteSteps κ₁ κ₂))
        ∂(configMeasure (haarProb Circle)) = 0 := by
  rw [integral_wilsonLoop_mul_conj hN x (ne_of_lt hμν) y (ne_of_lt hκ)]
  obtain ⟨dq1, -, -, -, -, -⟩ := plaquette_four_links_distinct hN y (ne_of_lt hκ)
  by_cases hA : (y, κ₁) = (x, μ) ∨ (y, κ₁) = ((torusShift N μ) x, ν)
  · rcases hA with hA | hA
    · simp only [Prod.mk.injEq] at hA
      obtain ⟨hf1, hs1⟩ := hA
      by_cases hB : ((torusShift N κ₁) y, κ₂) = (x, μ)
          ∨ ((torusShift N κ₁) y, κ₂) = ((torusShift N μ) x, ν)
      · rcases hB with hB | hB
        · simp only [Prod.mk.injEq] at hB
          have hB1 := hB.1
          rw [hs1, hf1] at hB1
          exact absurd hB1 (torusShift_ne_self N hN μ x)
        · simp only [Prod.mk.injEq] at hB
          have htriple : (y, κ₁, κ₂) = (x, μ, ν) := by rw [hf1, hs1, hB.2]
          exact absurd htriple hqp
      · push_neg at hB
        refine Finset.prod_eq_zero
          (Finset.mem_univ ((torusShift N κ₁) y, κ₂)) ?_
        exact integral_phiFactor_mul_conj_eq_zero x y _
          (phiFactor_eq_inv_or_one _ _ _ _ _ hB.1 hB.2)
          (fun z => phiFactor_snd _ _ _ _ z (Ne.symm dq1))
    · simp only [Prod.mk.injEq] at hA
      obtain ⟨hf1, hs1⟩ := hA
      by_cases hB : ((torusShift N κ₁) y, κ₂) = (x, μ)
          ∨ ((torusShift N κ₁) y, κ₂) = ((torusShift N μ) x, ν)
      · rcases hB with hB | hB
        · simp only [Prod.mk.injEq] at hB
          have hB1 := hB.1
          rw [hs1, hf1] at hB1
          have hcoord := congrFun hB1 μ
          rw [torusShift_apply, Pi.add_apply,
            Pi.single_eq_of_ne (ne_of_lt hμν), torusShift_apply,
            Pi.add_apply, Pi.single_eq_same] at hcoord
          simp only [zero_add] at hcoord
          have h10' : (1 : ZMod N) = 0 := by
            have h := congrArg (fun t : ZMod N => t - x μ) hcoord
            simpa using h
          exact absurd h10' (one_ne_zero_zmod hN)
        · simp only [Prod.mk.injEq] at hB
          have heq : κ₁ = κ₂ := hs1.trans hB.2.symm
          exact absurd heq (ne_of_lt hκ)
      · push_neg at hB
        refine Finset.prod_eq_zero
          (Finset.mem_univ ((torusShift N κ₁) y, κ₂)) ?_
        exact integral_phiFactor_mul_conj_eq_zero x y _
          (phiFactor_eq_inv_or_one _ _ _ _ _ hB.1 hB.2)
          (fun z => phiFactor_snd _ _ _ _ z (Ne.symm dq1))
  · push_neg at hA
    refine Finset.prod_eq_zero (Finset.mem_univ (y, κ₁)) ?_
    exact integral_phiFactor_mul_conj_eq_zero x y _
      (phiFactor_eq_inv_or_one _ _ _ _ _ hA.1 hA.2)
      (fun z => phiFactor_fst _ _ _ _ z)

/-- The circle plaquette expectation vanishes at `β = 0` (the
Stage-0 circle instance, in Wilson-loop form). -/
theorem gibbsExpect_zero_circle_plaquette (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    gibbsExpect (torusShift N) (haarProb Circle) circleRep 0
      (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
      = 0 := by
  have hfun : (fun U => wilsonLoop (torusShift N) circleRep U x
        (plaquetteSteps μ ν))
      = (fun U => Matrix.trace (repMatrix circleRep
          (plaquette (torusShift N) U x μ ν))) := by
    funext U
    rw [wilsonLoop_circleRep, loopProd_plaquetteSteps (torusShift N)
      (torusShift_comm N), trace_repMatrix_circleRep]
  rw [hfun]
  exact gibbsExpect_zero_plaquette_eq_zero (torusShift N) (haarProb Circle)
    circleRep circleRep_continuous x (ne_of_lt hμν)
    (torusShift_ne_self N hN μ x) (torusShift_ne_self N hN ν x)
    circleRep_no_fixed

/-- The real part as a complex number, via conjugation. -/
theorem ofReal_re_eq (z : ℂ) :
    ((z.re : ℝ) : ℂ) = (z + starRingEnd ℂ z) / 2 := by
  have h := Complex.add_conj z
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat] at h
  rw [h]
  exact (mul_div_cancel_left₀ _ two_ne_zero).symm

/-- **The per-plaquette circle covariance**: `Cov₀(W_p, D_q)` is
`-1/2` for `q = p` and `0` otherwise. -/
theorem covZero_circle_plaquette_density (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {κ₁ κ₂ : Fin 4} (hκ : κ₁ < κ₂) :
    covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂
          : ℝ) : ℂ))
      = if (y, κ₁, κ₂) = (x, μ, ν) then (-1 / 2 : ℂ) else 0 := by
  have hnormW : ∀ (s : Fin 4 → ZMod N) (steps : List Step)
      (U : Config (Fin 4 → ZMod N) Circle),
      ‖wilsonLoop (torusShift N) circleRep U s steps‖ = 1 := by
    intro s steps U
    rw [wilsonLoop_circleRep]
    exact Circle.norm_coe _
  have hDD : ∀ U : Config (Fin 4 → ZMod N) Circle,
      ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂ : ℝ) : ℂ)
        = 1 - (wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
            + starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
                (plaquetteSteps κ₁ κ₂))) / 2 := by
    intro U
    have htr : Matrix.trace (repMatrix circleRep
          (plaquette (torusShift N) U y κ₁ κ₂))
        = wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂) := by
      rw [wilsonLoop_circleRep, loopProd_plaquetteSteps (torusShift N)
        (torusShift_comm N), trace_repMatrix_circleRep]
    unfold plaquetteDensity
    rw [htr]
    simp only [Nat.cast_one, div_one]
    rw [Complex.ofReal_sub, Complex.ofReal_one, ofReal_re_eq]
  have hInt1 : Integrable
      (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
      (configMeasure (haarProb Circle)) :=
    Integrable.of_bound
      (measurable_wilsonLoop (torusShift N) circleRep circleRep_continuous x
        (plaquetteSteps μ ν)).aestronglyMeasurable 1
      (ae_of_all _ fun U => (hnormW x _ U).le)
  have hIntpp : Integrable
      (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂))
      (configMeasure (haarProb Circle)) :=
    Integrable.of_bound
      ((measurable_wilsonLoop (torusShift N) circleRep circleRep_continuous x
        (plaquetteSteps μ ν)).mul
        (measurable_wilsonLoop (torusShift N) circleRep circleRep_continuous y
          (plaquetteSteps κ₁ κ₂))).aestronglyMeasurable 1
      (ae_of_all _ fun U => by
        rw [norm_mul, hnormW x _ U, hnormW y _ U]
        norm_num)
  have hfunconj : (fun U => wilsonLoop (torusShift N) circleRep U x
        (plaquetteSteps μ ν)
        * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
            (plaquetteSteps κ₁ κ₂)))
      = (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
          * (wilsonLoop (torusShift N) circleRep U y
              (plaquetteSteps κ₁ κ₂))⁻¹) := by
    funext U
    rw [wilsonLoop_circleRep (torusShift N) U y (plaquetteSteps κ₁ κ₂),
      conj_circle_coe]
  have hIntpc : Integrable
      (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
        * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
            (plaquetteSteps κ₁ κ₂)))
      (configMeasure (haarProb Circle)) := by
    rw [hfunconj]
    refine Integrable.of_bound
      ((measurable_wilsonLoop (torusShift N) circleRep circleRep_continuous x
        (plaquetteSteps μ ν)).mul
        (measurable_wilsonLoop (torusShift N) circleRep circleRep_continuous y
          (plaquetteSteps κ₁ κ₂)).inv).aestronglyMeasurable 1
      (ae_of_all _ fun U => ?_)
    rw [norm_mul, norm_inv, hnormW y _ U, hnormW x _ U]
    norm_num
  have hInt0 : ∫ U, wilsonLoop (torusShift N) circleRep U x
        (plaquetteSteps μ ν) ∂(configMeasure (haarProb Circle)) = 0 := by
    rw [← gibbsExpect_zero]
    exact gibbsExpect_zero_circle_plaquette hN x hμν
  have hcov : covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂
          : ℝ) : ℂ))
      = ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
          * ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂ : ℝ) : ℂ)
          ∂(configMeasure (haarProb Circle)) := by
    unfold covZero
    rw [gibbsExpect_zero_circle_plaquette hN x hμν, zero_mul, sub_zero,
      gibbsExpect_zero]
  rw [hcov]
  have hExpand : ∫ U, wilsonLoop (torusShift N) circleRep U x
        (plaquetteSteps μ ν)
        * ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂ : ℝ) : ℂ)
        ∂(configMeasure (haarProb Circle))
      = ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
          ∂(configMeasure (haarProb Circle))
        - (∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
            * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
            ∂(configMeasure (haarProb Circle))
          + ∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
            * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
                (plaquetteSteps κ₁ κ₂))
            ∂(configMeasure (haarProb Circle))) * (2 : ℂ)⁻¹ := by
    have hpt : ∀ U : Config (Fin 4 → ZMod N) Circle,
        wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
          * ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂ : ℝ) : ℂ)
        = wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
          - (wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
              * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
            + wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
              * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
                  (plaquetteSteps κ₁ κ₂))) * (2 : ℂ)⁻¹ := by
      intro U
      rw [hDD U]
      ring
    have e2 : (∫ U, (wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
            * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
          + wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
            * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
                (plaquetteSteps κ₁ κ₂))) * (2 : ℂ)⁻¹
          ∂(configMeasure (haarProb Circle)))
        = ((∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
              * wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
              ∂(configMeasure (haarProb Circle)))
            + (∫ U, wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
              * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U y
                  (plaquetteSteps κ₁ κ₂)) ∂(configMeasure (haarProb Circle))))
          * (2 : ℂ)⁻¹ :=
      (integral_mul_const (2 : ℂ)⁻¹ _).trans
        (congrArg (· * (2 : ℂ)⁻¹) (integral_add hIntpp hIntpc))
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact (integral_sub hInt1 ((hIntpp.add hIntpc).mul_const (2 : ℂ)⁻¹)).trans
      (congrArg (HSub.hSub (∫ U, wilsonLoop (torusShift N) circleRep U x
        (plaquetteSteps μ ν) ∂(configMeasure (haarProb Circle)))) e2)
  rw [hExpand, hInt0, zero_sub]
  by_cases hqp : (y, κ₁, κ₂) = (x, μ, ν)
  · rw [if_pos hqp]
    obtain ⟨rfl, rfl, rfl⟩ := hqp
    rw [integral_wilsonLoop_mul_eq_zero hN x hμν x hμν]
    have hself : ∫ U, wilsonLoop (torusShift N) circleRep U x
          (plaquetteSteps μ ν)
          * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U x
              (plaquetteSteps μ ν)) ∂(configMeasure (haarProb Circle))
        = 1 := by
      have hpt : ∀ U : Config (Fin 4 → ZMod N) Circle,
          wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)
            * starRingEnd ℂ (wilsonLoop (torusShift N) circleRep U x
                (plaquetteSteps μ ν)) = 1 := by
        intro U
        rw [wilsonLoop_circleRep (torusShift N) U x (plaquetteSteps μ ν)]
        exact circle_coe_mul_conj _
      rw [integral_congr_ae (ae_of_all _ hpt)]
      simp [integral_const]
    rw [hself]
    norm_num
  · rw [if_neg hqp,
      integral_wilsonLoop_mul_eq_zero hN x hμν y hκ,
      integral_wilsonLoop_mul_conj_eq_zero hN x hμν y hκ hqp]
    norm_num

/-- **The circle link-sharing sum is `-1/2`**: the diagonal term
is the only survivor. -/
theorem sum_sharing_circle (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    ∑ q ∈ sharingPlaquettes (torusShift N)
        (plaquetteLinks (torusShift N) x μ ν),
      covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => ((plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2
          : ℝ) : ℂ))
      = -1 / 2 := by
  have hmem : (x, μ, ν) ∈ sharingPlaquettes (torusShift N)
      (plaquetteLinks (torusShift N) x μ ν) := by
    rw [sharingPlaquettes, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hμν, ?_⟩
    refine ⟨(x, μ), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;>
      · rw [plaquetteLinks_eq (torusShift N) (torusShift_comm N)]
        exact Finset.mem_insert_self _ _
  have h₀ : ∀ q ∈ sharingPlaquettes (torusShift N)
        (plaquetteLinks (torusShift N) x μ ν), q ≠ (x, μ, ν) →
      covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => ((plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2
          : ℝ) : ℂ)) = 0 := by
    intro q hq hqne
    rw [sharingPlaquettes, Finset.mem_filter] at hq
    have hqκ : q.2.1 < q.2.2 := hq.2.1
    rw [covZero_circle_plaquette_density hN x hμν q.1 hqκ]
    exact if_neg (fun h => hqne h)
  rw [Finset.sum_eq_single (x, μ, ν) h₀ (fun h => (h hmem).elim)]
  show covZero (torusShift N) (haarProb Circle) circleRep
      (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
      (fun U => ((plaquetteDensity (torusShift N) circleRep U x μ ν : ℝ) : ℂ))
    = -1 / 2
  rw [covZero_circle_plaquette_density hN x hμν x hμν, if_pos rfl]

/-- **Headline (ii), circle instance: `κ_p = -1/2`** — the exact
first-order plaquette coefficient for the circle/fundamental
representation. -/
theorem kappa_circle_plaquette (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => ((actionDensity (torusShift N) circleRep U : ℝ) : ℂ))
      = -1 / 2 :=
  (covZero_plaquetteLoop_eq_sum (torusShift N) (haarProb Circle) circleRep
    circleRep_continuous (by norm_num) (torusShift_comm N) x μ ν).trans
    (sum_sharing_circle hN x hμν)

/-- **The circle plaquette's first-order response is `β/2`**:
the derivative of the plaquette expectation at `β = 0`. -/
theorem deriv_circle_plaquette (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    deriv (fun β : ℝ => gibbsExpect (torusShift N) (haarProb Circle) circleRep β
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν)))
        0
      = 1 / 2 := by
  rw [deriv_plaquetteLoop_eq (torusShift N) (haarProb Circle) circleRep
    circleRep_continuous (by norm_num) (torusShift_comm N) x μ ν,
    sum_sharing_circle hN x hμν]
  norm_num

/-- **The circle plaquette expansion with the explicit
remainder**: `⟨W_p⟩_β = β/2 + O(β²)` at the §3 constant — the
form the vacuum-portrait sampler's small-β measurement
(`⟨Re U_p⟩ ≈ 0.124` at `β = 0.25`) corroborates against the
predicted `0.125`. -/
theorem gibbsExpect_circle_plaquette_firstOrder (hN : 2 ≤ N)
    (x : Fin 4 → ZMod N) {μ ν : Fin 4} (hμν : μ < ν) {β : ℝ} (hβ : |β| ≤ 1) :
    ‖gibbsExpect (torusShift N) (haarProb Circle) circleRep β
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
      - (β : ℂ) * (1 / 2)‖
      ≤ firstOrderConst (Λ := Fin 4 → ZMod N) (1 : ℝ) * β ^ 2 := by
  have h := gibbsExpect_firstOrder (torusShift N) (haarProb Circle) circleRep
    circleRep_continuous (by norm_num : (0 : ℕ) < 1)
    (measurable_wilsonLoop (torusShift N) circleRep circleRep_continuous x
      (plaquetteSteps μ ν))
    (fun U => by
      have hb := norm_wilsonLoop_le (torusShift N) circleRep (by norm_num) U x
        (plaquetteSteps μ ν)
      rwa [Nat.cast_one] at hb) hβ
  have hmom : gibbsMoment (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        0 = 0 :=
    (gibbsMoment_zero (torusShift N) (haarProb Circle) circleRep _).trans
      (gibbsExpect_zero_circle_plaquette hN x hμν)
  rw [hmom, kappa_circle_plaquette hN x hμν] at h
  have h2 : (0 : ℂ) - β • (-1 / 2 : ℂ) = (β : ℂ) * (1 / 2) := by
    rw [Complex.real_smul]
    ring
  rwa [h2] at h


end CircleEval
