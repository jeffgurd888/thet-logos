import ThetLogos.DiscCoeffProduct
import ThetLogos.HfcDiscSpectralMapping

/-!
# B4-UNIT — a zero-free factor gives a unit calculus value
(SHELF-7b-disc chain, GATE-B discharge)

Brick B4-UNIT of the SHELF line (pack
`routeb-general-scratch/pack-gate-b4-unit.md`; scoping
`whitepaper/scoping-gate-b4-2026-11-02.md` SS2a/2c).

Headline, self-contained: for `h` disc-holomorphic on the
disc of radius `R`, zero-free on the closed disc of radius
`R₂` with `R₀ < R₂ < R`, and `(spectralRadius ℂ a).toReal < R₀`,
the calculus value `hfcDisc a (discCoeff h R₀)` is a unit.

Route: the reciprocal `k z = (h z)⁻¹` is disc-holomorphic at
an intermediate radius `R₁`, `R₀ < R₁ < R₂`
(`DifferentiableOn.inv` from the zero-free hypothesis);
`h * k = 1` on the presenting circle of radius `R₀`, so
`discCoeff (h * k) R₀` is the delta sequence (circle-integral
congruence + B3′'s `discCoeff_const`); B4-PROD
(`discCoeff_mul_of_lt_radius`) at presenting radius `R₀`
identifies that with the convolution of the coefficients;
B3′'s `hfcDisc_mul_of_summable` at the sharp summabilities
(B2′'s `summable_norm_smul_pow_discCoeff_interior`) evaluates
the product to `1`, and 8a's `commute_hfcDisc_hfcDisc` makes
it two-sided.

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter
open scoped NNReal ENNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## Step 1 — the reciprocal is disc-holomorphic -/

/-- The reciprocal of a disc-holomorphic function that is
zero-free on the closed disc of radius `R₂` is
disc-holomorphic at every intermediate radius `R₁ < R₂`. -/
theorem discHolomorphic_inv_of_zeroFree {h : ℂ → ℂ} {R R₁ R₂ : ℝ}
    (hhol : DiscHolomorphic h R) (hR₂R : R₂ < R)
    (hzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R₂, h z ≠ 0)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂) :
    DiscHolomorphic (fun z => (h z)⁻¹) R₁ := by
  refine ⟨hR₁, ?_⟩
  have hdiff : DifferentiableOn ℂ h (Metric.ball 0 R₁) :=
    hhol.2.mono (Metric.ball_subset_ball (hR₁₂.trans hR₂R).le)
  have hinv := hdiff.inv (fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    exact hzero z (by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hz.le.trans hR₁₂.le))
  exact hinv

/-! ## Step 2 — the product's coefficients are the delta sequence -/

/-- The coefficients of the product `h * (1/h)`, presented at
`R₀`, are the delta sequence: on the presenting circle
`‖z‖ = R₀ < R₂` the product is `1`, so its circle integrals
agree with those of the constant function `1`, and B3′'s
`discCoeff_const` evaluates those. -/
theorem discCoeff_mul_inv {h : ℂ → ℂ} {R₀ R₂ : ℝ}
    (hR₀ : 0 < R₀) (hR₀₂ : R₀ < R₂)
    (hzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R₂, h z ≠ 0) (n : ℕ) :
    discCoeff (fun z => h z * (h z)⁻¹) R₀ n
      = if n = 0 then (1 : ℂ) else 0 := by
  have hcongr : discCoeff (fun z => h z * (h z)⁻¹) R₀ n
      = discCoeff (fun _ => (1 : ℂ)) R₀ n := by
    show cauchyPowerSeries (fun z => h z * (h z)⁻¹) 0 R₀ n (fun _ => (1 : ℂ))
      = cauchyPowerSeries (fun _ => (1 : ℂ)) 0 R₀ n (fun _ => (1 : ℂ))
    rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
    congr 1
    refine circleIntegral.integral_congr hR₀.le (fun z hz => ?_)
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    have hz0 : h z ≠ 0 :=
      hzero z (by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hz]
        exact hR₀₂.le)
    simp [mul_inv_cancel₀ hz0]
  rw [hcongr]
  exact discCoeff_const 1 hR₀ n

/-! ## Steps 3–4 — the convolution is delta, and its value is `1` -/

/-- **Headline (B4-UNIT).** A zero-free factor gives a unit
calculus value: for `h` disc-holomorphic on the disc of
radius `R`, zero-free on the closed disc of radius `R₂`,
with `(spectralRadius ℂ a).toReal < R₀ < R₂ < R`, the value
`hfcDisc a (discCoeff h R₀)` is a unit in `A`. -/
theorem isUnit_hfcDisc_of_zeroFree (a : A) (h : ℂ → ℂ) {R R₀ R₂ : ℝ}
    (hR₀ : (spectralRadius ℂ a).toReal < R₀) (hR₀₂ : R₀ < R₂)
    (hhol : DiscHolomorphic h R) (hR₂R : R₂ < R)
    (hzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R₂, h z ≠ 0) :
    IsUnit (hfcDisc a (discCoeff h R₀)) := by
  have hR₀pos : 0 < R₀ := ENNReal.toReal_nonneg.trans_lt hR₀
  obtain ⟨R₁, hR₀₁, hR₁₂⟩ := exists_between hR₀₂
  have hR₁pos : 0 < R₁ := hR₀pos.trans hR₀₁
  have hR₁R : R₁ < R := hR₁₂.trans hR₂R
  have hk : DiscHolomorphic (fun z => (h z)⁻¹) R₁ :=
    discHolomorphic_inv_of_zeroFree hhol hR₂R hzero hR₁pos hR₁₂
  have hh₁ : DiscHolomorphic h R₁ :=
    discHolomorphic_of_lt hhol hR₁pos hR₁R
  -- Step 3: B4-PROD at presenting radius `R₀`, then step 2.
  have hconv : discConv (discCoeff h R₀) (discCoeff (fun z => (h z)⁻¹) R₀)
      = fun n => if n = 0 then (1 : ℂ) else 0 := by
    have hprod := discCoeff_mul_of_lt_radius hh₁ hk hR₀pos hR₀₁
    funext n
    rw [← hprod]
    exact discCoeff_mul_inv hR₀pos hR₀₂ hzero n
  -- Step 4: sharp summabilities, multiplicativity, two-sided unit.
  have hsum_h : Summable fun n => ‖discCoeff h R₀ n • a ^ n‖ :=
    summable_norm_smul_pow_discCoeff_interior a hhol (hR₀₂.trans hR₂R) hR₀
  have hsum_k : Summable fun n => ‖discCoeff (fun z => (h z)⁻¹) R₀ n • a ^ n‖ :=
    summable_norm_smul_pow_discCoeff_interior a hk hR₀₁ hR₀
  have hmul : hfcDisc a (discCoeff h R₀)
      * hfcDisc a (discCoeff (fun z => (h z)⁻¹) R₀) = 1 := by
    rw [← hfcDisc_mul_of_summable hsum_h hsum_k, hconv, hfcDisc_const]
    simp
  have hmul' : hfcDisc a (discCoeff (fun z => (h z)⁻¹) R₀)
      * hfcDisc a (discCoeff h R₀) = 1 := by
    rw [← (commute_hfcDisc_hfcDisc (discCoeff h R₀)
      (discCoeff (fun z => (h z)⁻¹) R₀)).eq]
    exact hmul
  exact ⟨⟨hfcDisc a (discCoeff h R₀), hfcDisc a (discCoeff (fun z => (h z)⁻¹) R₀),
    hmul, hmul'⟩, rfl⟩

end

end ThetLogos
