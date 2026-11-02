/-
# GATE-B1 - the disc coefficient layer at the sharp scale (SHELF-7b-disc, brick 1)

Brick GATE-B1 of the SHELF line (refresh scoping
`whitepaper/shelf-7b-refresh-scoping-2026-11-02.md`, section (g);
pack `routeb-general-scratch/pack-gate-b1.md`). Verdict against
the four B1 target Props frozen in `ThetLogos.Shelf7bPin`:
B1a (coefficient radius-independence), B1b (Cauchy-estimate
summability at every interior scale) and B1d (summability at
the spectral-radius scale; its pre-registered PARTIAL seam does
NOT trigger) are DISCHARGED. B1c (`Shelf7bB1ScalarEval`) is
FALSE as frozen - it presents the coefficients at the boundary
radius, whose values the open-disc holomorphicity hypothesis
does not constrain - and is NOT discharged: section 3 lands
the interior-presented scalar evaluation at full rank and
proves the kill (`shelf7bB1ScalarEval_not`).

Face fence: 7b-disc is NOT 7b-in-full. This module proves the
disc coefficient layer only; the FULL gate (winding number,
general contour systems, germ algebra) is untouched. NO CLAIM;
dials 0/4. Consumes nothing from GATE-A / SHELF-8b.

Pin citations verified by grep against the vendored pin
(Mathlib v4.35.0-rc3) before use:
* annulus Cauchy-Goursat:
  `Mathlib/Analysis/Complex/CauchyIntegral.lean:352`
  (`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`);
* Cauchy estimate: `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:652`
  (`norm_cauchyPowerSeries_le`);
* scalar HasSum form: `CircleIntegral.lean:718`
  (`hasSum_cauchyPowerSeries_integral`); the packaged
  `HasFPowerSeriesOnBall` forms used below sit at
  `CauchyIntegral.lean:668` (`Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`)
  and `:686` (`DiffContOnCl.hasFPowerSeriesOnBall`) / `:697`
  (`DifferentiableOn.hasFPowerSeriesOnBall`) - the refresh's
  `:671/:688` citations are off by a few lines (finding, reported);
* Gelfand's formula: `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean:122`
  (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`)
  and `:133` (`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`).
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import ThetLogos.Shelf7bPin

namespace ThetLogos

open Filter Real
open scoped NNReal ENNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## 1. `Shelf7bB1CoeffIndep` - coefficients independent of the radius -/

/-- The scalar Cauchy kernel `(z)⁻¹ⁿ⁺¹ • f z` (written with the
`(z - 0)⁻¹` factors as in `cauchyPowerSeries_apply`) is complex
differentiable at every nonzero point of the disc of
holomorphicity. -/
theorem differentiableAt_discKernel {f : ℂ → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (n : ℕ)
    {z : ℂ} (hz0 : z ≠ 0) (hzR : ‖z‖ < R) :
    DifferentiableAt ℂ
      (fun w => ((w - 0)⁻¹) ^ n • (w - 0)⁻¹ • f w) z := by
  have hinv : DifferentiableAt ℂ (fun w => (w - 0)⁻¹) z :=
    (differentiableAt_id.sub_const (0 : ℂ)).inv (by simpa using hz0)
  have hfz : DifferentiableAt ℂ f z := by
    have hzmem : z ∈ Metric.ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzR
    exact (hf (x := z) hzmem).differentiableAt (Metric.isOpen_ball.mem_nhds hzmem)
  exact (hinv.pow n).smul (hinv.smul hfz)

/-- Annulus Cauchy-Goursat for the scalar kernel: its circle
integrals at two radii inside the disc of holomorphicity agree.
This is the pin's `CauchyIntegral.lean:352` form applied to
`(z)⁻¹ⁿ⁺¹ • f`. -/
theorem circleIntegral_discKernel_eq {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R) (n : ℕ)
    {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₁₂ : R₁ ≤ R₂) (h₂ : R₂ < R) :
    (∮ z in C(0, R₂), ((z - 0)⁻¹) ^ n • (z - 0)⁻¹ • f z)
      = ∮ z in C(0, R₁), ((z - 0)⁻¹) ^ n • (z - 0)⁻¹ • f z := by
  obtain ⟨hR, hdiff⟩ := hf
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    h₁ h₁₂ (s := ∅) Set.countable_empty ?_ ?_
  · intro z hz
    obtain ⟨hzc, hzb⟩ := hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hzc
    have hzR : ‖z‖ < R := hzc.trans_lt h₂
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hzb (by simpa using h₁)
    exact (differentiableAt_discKernel hdiff n hz0 hzR).continuousAt.continuousWithinAt
  · intro z hz
    obtain ⟨⟨hzball, hznot⟩, -⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzball
    have hzR : ‖z‖ < R := hzball.trans h₂
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hznot (by simpa using h₁.le)
    exact differentiableAt_discKernel hdiff n hz0 hzR

/-- B1a, worker form: `discCoeff` does not depend on the
presenting radius. -/
theorem discCoeff_indep {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R)
    {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₁R : R₁ < R) (h₂ : 0 < R₂) (h₂R : R₂ < R) :
    discCoeff f R₁ = discCoeff f R₂ := by
  have key : ∀ u v : ℝ, 0 < u → u ≤ v → v < R →
      discCoeff f v = discCoeff f u := by
    intro u v hu huv hvR
    funext n
    show cauchyPowerSeries f 0 v n (fun _ => (1 : ℂ))
      = cauchyPowerSeries f 0 u n (fun _ => (1 : ℂ))
    rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
    simp only [one_div]
    rw [circleIntegral_discKernel_eq hf n hu huv hvR]
  rcases le_total R₁ R₂ with h | h
  · exact (key R₁ R₂ h₁ h h₂R).symm
  · exact key R₂ R₁ h₂ h h₁R

/-- B1a: discharges the pin Prop `Shelf7bB1CoeffIndep`. -/
theorem shelf7bB1CoeffIndep_proved (f : ℂ → ℂ) (R : ℝ) :
    Shelf7bB1CoeffIndep f R := by
  intro hf R₁ R₂ h₁ h₁R h₂ h₂R
  exact discCoeff_indep hf h₁ h₁R h₂ h₂R

/-! ## 2. `Shelf7bB1Summable` - Cauchy-estimate summability -/

/-- The Cauchy-estimate constant at presenting radius `R`:
`(2π)⁻¹` times the circle integral of `‖f‖`. -/
theorem cauchyConst_nonneg (f : ℂ → ℂ) (R : ℝ) :
    0 ≤ (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap 0 R θ)‖ :=
  mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le)
    (intervalIntegral.integral_nonneg Real.two_pi_pos.le
      (fun _ _ => norm_nonneg _))

/-- The Cauchy estimate for `discCoeff`, from the pin's
`norm_cauchyPowerSeries_le` (`CircleIntegral.lean:652`), using
`‖p n‖ = ‖p.coeff n‖` for the formal multilinear series `p`. -/
theorem norm_discCoeff_le (f : ℂ → ℂ) (R : ℝ) (n : ℕ) :
    ‖discCoeff f R n‖ ≤
      ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap 0 R θ)‖) * |R|⁻¹ ^ n := by
  have h1 : ‖discCoeff f R n‖ = ‖cauchyPowerSeries f 0 R n‖ := by
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
    simp only [discCoeff, FormalMultilinearSeries.coeff, Pi.one_def]
  rw [h1]
  exact norm_cauchyPowerSeries_le f 0 R n

/-- B1b, worker form: Cauchy-estimate summability of
`discCoeff f R` at every interior scale `s < R`, by geometric
comparison against the Cauchy estimate at scale `R`. -/
theorem discSummable_discCoeff {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R) {s : ℝ} (hs : 0 ≤ s) (hsR : s < R) :
    DiscSummable s (discCoeff f R) := by
  obtain ⟨hR, -⟩ := hf
  set C := (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap 0 R θ)‖ with hCdef
  have hC : 0 ≤ C := cauchyConst_nonneg f R
  have hratio : s / R < 1 := (div_lt_one hR).mpr hsR
  have hratio0 : 0 ≤ s / R := div_nonneg hs hR.le
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hratio0 hratio).mul_left C) (fun n => ?_)
  show ‖‖discCoeff f R n‖ * s ^ n‖ ≤ C * (s / R) ^ n
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hs n))]
  calc ‖discCoeff f R n‖ * s ^ n
      ≤ (C * |R|⁻¹ ^ n) * s ^ n :=
        mul_le_mul_of_nonneg_right (norm_discCoeff_le f R n) (pow_nonneg hs n)
    _ = C * (s / R) ^ n := by
        rw [abs_of_pos hR, div_pow, div_eq_mul_inv, ← inv_pow]; ring

/-- B1b: discharges the pin Prop `Shelf7bB1Summable`. -/
theorem shelf7bB1Summable_proved (f : ℂ → ℂ) (R : ℝ) :
    Shelf7bB1Summable f R := by
  intro hf s hs hsR
  exact discSummable_discCoeff hf hs hsR

/-! ## 3. `Shelf7bB1ScalarEval` - FINDING: false as frozen; the
interior form lands

The pin Prop `Shelf7bB1ScalarEval` presents the coefficients at
the boundary radius `R` itself: `discCoeff f R`. But
`DiscHolomorphic f R` constrains `f` only on the *open* ball,
while `discCoeff f R` integrates `f` over the boundary circle
`‖z‖ = R`, whose values are unconstrained. The frozen Prop is
therefore FALSE: the counterexample below (`f = 0` on the open
unit disc, `f = 1` on `‖z‖ = 1`) is `DifferentiableOn` the ball
with `discCoeff f 1 0 = 1`, so `scalarEval (discCoeff f 1) 0
= 1 ≠ 0 = f 0`. What the pin's cited forms
(`hasSum_cauchyPowerSeries_integral`, `CircleIntegral.lean:718`;
`DifferentiableOn.hasFPowerSeriesOnBall`,
`CauchyIntegral.lean:697`) actually prove is the
interior-presented form, landed here at full rank: for every
presenting radius `R' < R`, `scalarEval (discCoeff f R') z
= f z` on `‖z‖ < R'`. By B1a all interior presentations agree,
so the scalar series value on the disc is `f`; only the
boundary presentation in the frozen Prop fails. -/

/-- Interior HasSum form (via the pin's packaged
`DifferentiableOn.hasFPowerSeriesOnBall`,
`CauchyIntegral.lean:697`): the series with interior-presented
coefficients `discCoeff f R'` sums to `f z` for `‖z‖ < R'`. -/
theorem hasSum_discCoeff_of_lt {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R) {R' : ℝ} (hR' : 0 < R') (hR'R : R' < R)
    {z : ℂ} (hz : ‖z‖ < R') :
    HasSum (fun n => discCoeff f R' n * z ^ n) (f z) := by
  obtain ⟨-, hdiff⟩ := hf
  let rnn : ℝ≥0 := ⟨R', hR'.le⟩
  have hrnnR : (rnn : ℝ) = R' := rfl
  have hclosed : DifferentiableOn ℂ f (Metric.closedBall 0 (rnn : ℝ)) :=
    hdiff.mono (Metric.closedBall_subset_ball hR'R)
  have hser : HasFPowerSeriesOnBall f
      (cauchyPowerSeries f 0 (rnn : ℝ)) 0 (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall hclosed hR'
  have hy : z ∈ Metric.eball (0 : ℂ) (rnn : ℝ≥0∞) := by
    simpa [Metric.mem_eball, hrnnR] using hz
  have hsum := hser.hasSum hy
  rw [zero_add] at hsum
  have hterm : (fun n => cauchyPowerSeries f 0 (rnn : ℝ) n (fun _ => z))
      = (fun n => discCoeff f R' n * z ^ n) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
      mul_comm (z ^ n) _, hrnnR]
    rfl
  rw [hterm] at hsum
  exact hsum

/-- Interior scalar evaluation (the B1c content the pin's forms
support): `scalarEval (discCoeff f R') z = f z` for every
interior presenting radius `R' < R` and `‖z‖ < R'`. -/
theorem scalarEval_discCoeff_eq_of_lt {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R) {R' : ℝ} (hR' : 0 < R') (hR'R : R' < R)
    {z : ℂ} (hz : ‖z‖ < R') :
    scalarEval (discCoeff f R') z = f z :=
  (hasSum_discCoeff_of_lt hf hR' hR'R hz).tsum_eq

/-- Interior scalar evaluation, presentation-free form: by
B1a, *every* interior presenting radius `R₁` gives the same
coefficients, and by the interior evaluation they sum to `f`
at every `z` inside some (equivalently any smaller) interior
radius `R₂`. -/
theorem scalarEval_discCoeff_eq_of_indep {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R) {R₁ R₂ : ℝ}
    (h₁ : 0 < R₁) (h₁R : R₁ < R) (h₂ : 0 < R₂) (h₂R : R₂ < R)
    {z : ℂ} (hz : ‖z‖ < R₂) :
    scalarEval (discCoeff f R₁) z = f z := by
  rw [discCoeff_indep hf h₁ h₁R h₂ h₂R]
  exact scalarEval_discCoeff_eq_of_lt hf h₂ h₂R hz

/-- The boundary counterexample's zeroth coefficient: for
`f = 0` off `‖z‖ = 1` and `f = 1` on `‖z‖ = 1`,
`discCoeff f 1 0 = 1` (the boundary circle integral sees the
boundary values, not the interior ones). -/
theorem discCoeff_boundary_counterexample :
    discCoeff (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1 0 = 1 := by
  show cauchyPowerSeries (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0)
    0 1 0 (fun _ => (1 : ℂ)) = 1
  rw [cauchyPowerSeries_apply]
  simp only [pow_zero, one_smul]
  have hint : (∮ z in C(0, 1),
        (z - 0)⁻¹ • (if ‖z‖ = 1 then (1 : ℂ) else 0))
      = 2 * π * Complex.I := by
    have hcongr : (∮ z in C(0, 1),
          (z - 0)⁻¹ • (if ‖z‖ = 1 then (1 : ℂ) else 0))
        = ∮ z in C(0, 1), (z - 0)⁻¹ := by
      refine circleIntegral.integral_congr zero_le_one (fun z hz => ?_)
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [show (if ‖z‖ = 1 then (1 : ℂ) else 0) = 1 by simp [hz],
        smul_eq_mul, mul_one]
    rw [hcongr]
    simpa using circleIntegral.integral_sub_inv_of_mem_ball
      (c := (0 : ℂ)) (w := (0 : ℂ)) (R := (1 : ℝ)) (by simp)
  rw [hint]
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  rw [smul_eq_mul, inv_mul_cancel₀ hne]

/-- KILL, at full rank: the frozen pin Prop
`Shelf7bB1ScalarEval` is false as stated (boundary presentation
of the coefficients). The interior form above is the landed
replacement content; the frozen Prop is NOT discharged. -/
theorem shelf7bB1ScalarEval_not :
    ¬ Shelf7bB1ScalarEval
      (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1 := by
  intro h
  have hdiff : DiscHolomorphic
      (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1 := by
    refine ⟨one_pos, ?_⟩
    refine (differentiableOn_const (0 : ℂ)).congr (fun z hz => ?_)
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    rw [show (if ‖z‖ = 1 then (1 : ℂ) else 0) = 0 by simp [ne_of_lt hz]]
  have hspec : scalarEval
        (discCoeff (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1) 0
      = (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 0 :=
    h hdiff 0 (by simp)
  have hscal : scalarEval
        (discCoeff (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1) 0
      = 1 := by
    show (∑' n, discCoeff (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0)
      1 n * (0 : ℂ) ^ n) = 1
    rw [tsum_eq_single 0]
    · simpa using discCoeff_boundary_counterexample
    · intro n hn
      rw [zero_pow hn, mul_zero]
  rw [hscal] at hspec
  have hf0 : (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 0 = 0 := by simp
  rw [hf0] at hspec
  exact one_ne_zero hspec

/-! ## 4. `Shelf7bB1Sharp` - summability at the spectral-radius scale -/

omit [Nontrivial A] in
/-- The spectral radius is finite: it is bounded by `‖a‖₊`
(`spectralRadius_le_nnnorm`). -/
theorem discSpectralRadius_ne_top (a : A) :
    spectralRadius ℂ a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm a)

omit [Nontrivial A] in
/-- The real hypothesis `(spectralRadius ℂ a).toReal < ρ` in
`ℝ≥0∞` form, via `ENNReal.ofReal_toReal`. -/
theorem discSpectralRadius_lt_ofReal {a : A} {ρ : ℝ}
    (hρ : (spectralRadius ℂ a).toReal < ρ) (hρ0 : 0 < ρ) :
    spectralRadius ℂ a < ENNReal.ofReal ρ := by
  rw [← ENNReal.ofReal_toReal (discSpectralRadius_ne_top a)]
  exact (ENNReal.ofReal_lt_ofReal_iff hρ0).mpr hρ

omit [Nontrivial A] in
/-- Gelfand comparison: at any scale `ρ` above the spectral
radius, `‖a ^ n‖ ≤ ρ ^ n` eventually. This is Gelfand's formula
(the pin's `GelfandFormula.lean:133`, the `‖a ^ n‖` form)
read through `ENNReal.ofReal`. -/
theorem eventually_norm_pow_le_of_discSpectralRadius_lt {a : A} {ρ : ℝ}
    (hρ : (spectralRadius ℂ a).toReal < ρ) :
    ∀ᶠ n in atTop, ‖a ^ n‖ ≤ ρ ^ n := by
  have hρ0 : 0 < ρ := ENNReal.toReal_nonneg.trans_lt hρ
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev : ∀ᶠ (n : ℕ) in atTop,
      ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ))) < ENNReal.ofReal ρ :=
    hG.eventually (Iio_mem_nhds (discSpectralRadius_lt_ofReal hρ hρ0))
  filter_upwards [hev, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩]
    with n hn hn1
  have hroot : ‖a ^ n‖ ^ (1 / (n : ℝ)) < ρ :=
    (ENNReal.ofReal_lt_ofReal_iff hρ0).mp hn
  have hn0 : n ≠ 0 := by omega
  have hpow : (‖a ^ n‖ ^ ((n : ℝ)⁻¹)) ^ n = ‖a ^ n‖ :=
    Real.rpow_inv_natCast_pow (norm_nonneg _) hn0
  calc ‖a ^ n‖ = (‖a ^ n‖ ^ (1 / (n : ℝ))) ^ n := by
        rw [one_div]; exact hpow.symm
    _ ≤ ρ ^ n :=
        pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hroot.le n

/-- B1d, worker form (the sharp form of 8a's
`summable_smul_pow`): summability of `‖discCoeff f R n • a ^ n‖`
at the spectral-radius scale. Route: Gelfand comparison at the
intermediate scale `ρ` with
`(spectralRadius ℂ a).toReal < ρ < R`, consuming B1b at `ρ`. -/
theorem summable_smul_pow_of_spectralRadius_lt {f : ℂ → ℂ} {R : ℝ}
    (hf : DiscHolomorphic f R) (a : A)
    (hsr : (spectralRadius ℂ a).toReal < R) :
    Summable fun n => ‖discCoeff f R n • a ^ n‖ := by
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_between hsr
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg.trans hρ1.le
  have hDisc : DiscSummable ρ (discCoeff f R) :=
    discSummable_discCoeff hf hρ0 hρ2
  refine Summable.of_norm_bounded_eventually_nat hDisc ?_
  filter_upwards [eventually_norm_pow_le_of_discSpectralRadius_lt hρ1]
    with n hn
  show ‖‖discCoeff f R n • a ^ n‖‖ ≤ ‖discCoeff f R n‖ * ρ ^ n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖discCoeff f R n • a ^ n‖
      ≤ ‖discCoeff f R n‖ * ‖a ^ n‖ := norm_smul_le _ _
    _ ≤ ‖discCoeff f R n‖ * ρ ^ n :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)

/-- B1d: discharges the pin Prop `Shelf7bB1Sharp`. The
pre-registered PARTIAL seam at B1d does NOT trigger: the
Gelfand comparison lands inside the brick. -/
theorem shelf7bB1Sharp_proved (a : A) (f : ℂ → ℂ) (R : ℝ) :
    Shelf7bB1Sharp a f R := by
  intro hf hsr
  exact summable_smul_pow_of_spectralRadius_lt hf a hsr

end

end ThetLogos
