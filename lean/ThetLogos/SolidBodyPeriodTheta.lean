import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import ThetLogos.SolidBodyPeriodDiv

/-!
# ThetLogos.SolidBodyPeriodTheta — N3: the two-sided `Θ(|log τ|)` rate

Stage N3 of the nonlinear rigid-body program (scoping memo
`nonlinear-rigid-scoping-2026-10-26.md` §1), built on N2's
divergence lower bound (`SolidBodyPeriodDiv`), N1's quadrature
period (`SolidBodyPeriodQuad`) and N0's affine package
(`SolidBodyPolhode`). Fixed body, frozen coefficients, abstract
body only.

## ⚠ Honesty fence — read first

The period here is the **quadrature period** of N1: the return
time read off the first integrals by quadrature. That this number
*is* the return time of actual Euler trajectories is stage **N4**
(deferred; L hypothesis-fed / L+ full) and is **not** proved here —
the identification is classical T4. Every use of the word "period"
in this file means the quadrature period.

## What is proved (T1, from definitions/hypotheses; classical core T4)

The matching **upper** bound to N2's lower bound. For a body with
`0 < I₁ < I₂ < I₃` and `Λ > 0`, in either open band, on the
neighbourhood `τ = |E − E_sep| ∈ (0, 1]` with roots gap `≤ Λ/4`
(strictly inside N2's neighbourhood, so the two bounds share it):

* `periodQuad b Λ E ≤ upCoeff b Λ · |log τ| + C₂`, with
  `upCoeff b Λ = (2/quadCoeff)·(Λ·slope1·slope3/2)^(−1/2)`
  explicit — and `upCoeff = √2 · divCoeff`, so the two-sided rate
  has leading constants `divCoeff` (below, N2) and `√2·divCoeff`
  (above, here);
* hence the assembled `Θ` statements (`periodQuad_theta_top`,
  `periodQuad_theta_bot`): `periodQuad(E) = Θ(|log τ|)` as
  `E → E_sep` from either band, as a pair of explicit bounds.

The proof is comparison, no elliptic machinery. Split the
quadrature range at the fixed width `w = Λ/4` below `uMax`. Away
from the saddle both roots stay `≥ w` away, giving a pointwise
`u^(−1/2)` majorant whose integral is uniformly bounded. On the
saddle window, with `t = uMax − u` and `g` the roots gap, the
integrand is `≤ C₀·(t(t+g))^(−1/2)` (the factor `u ≥ Λ/2` there);
splitting at `t = g` bounds this by `C₀·g^(−1/2)·t^(−1/2)` on the
inner piece (integral `2C₀`) and by `C₀·t^(−1)` on the outer piece
(integral `C₀·(log w − log g)`), and `g = Λτ/(2B)` converts
`log(w/g)` into `log(B/2) + |log τ|`.

## Fences

Frozen coefficients throughout; no dynamics; no identification
with trajectory return times (stage N4). The linearized period's
inverse-square-root divergence of Bricks 1/4 (moments approaching
a tie) and this file's logarithmic divergence (energy approaching
`E_sep` at fixed moments) are **different theorems about
different limits** and are not merged here. Abstract body only.
NO CLAIM. Parts of any official (Clay) statement closed by this
file: 0.
-/

open MeasureTheory Filter Topology

namespace ThetLogos

/-! ## Explicit constants -/

/-- The upper-bound leading constant:
`C₁ = (2/c)·(Λ·slope1·slope3/2)^(−1/2)` — N2's `divCoeff` with
the saddle-window factor `u ≥ Λ/2` in place of `u ≤ Λ`, which is
exactly where the extra `√2` against `divCoeff` comes from. -/
noncomputable def upCoeff (b : SolidBody) (Λ : ℝ) : ℝ :=
  (2 / quadCoeff b) * (Λ * slope1 b * slope3 b / 2) ^ (-(1 / 2 : ℝ))

/-- The top band's explicit additive constant `C₂` for the upper
bound: the uniform away-from-saddle contribution plus the window
contribution's `τ`-independent part. -/
noncomputable def upC2top (b : SolidBody) (Λ : ℝ) : ℝ :=
  (2 / quadCoeff b) * (8 * (Λ * slope1 b * slope3 b) ^ (-(1 / 2 : ℝ))
    + (Λ * slope1 b * slope3 b / 2) ^ (-(1 / 2 : ℝ))
      * (2 + Real.log (topBandB b Λ / 2)))

/-- The bottom band's explicit additive constant `C₂`. -/
noncomputable def upC2bot (b : SolidBody) (Λ : ℝ) : ℝ :=
  (2 / quadCoeff b) * (8 * (Λ * slope1 b * slope3 b) ^ (-(1 / 2 : ℝ))
    + (Λ * slope1 b * slope3 b / 2) ^ (-(1 / 2 : ℝ))
      * (2 + Real.log (botBandB b Λ / 2)))

theorem upCoeff_pos (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) : 0 < upCoeff b Λ :=
  mul_pos (div_pos (by norm_num) (quadCoeff_pos b h12 h23))
    (Real.rpow_pos_of_pos
      (div_pos (mul_pos (mul_pos hΛ (slope1_pos b h12 h23))
        (slope3_pos b h12 h23)) (by norm_num)) _)

/-- The upper leading constant is exactly `√2` times N2's lower
leading constant: the `√2` is the price of the saddle-window
factor `u ≥ Λ/2` (upper) against `u ≤ Λ` (lower). -/
theorem upCoeff_eq_sqrt_two_mul_divCoeff (b : SolidBody)
    (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) :
    upCoeff b Λ = Real.sqrt 2 * divCoeff b Λ := by
  have hs : (0 : ℝ) < Λ * slope1 b * slope3 b :=
    mul_pos (mul_pos hΛ (slope1_pos b h12 h23)) (slope3_pos b h12 h23)
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (1 / (2 : ℝ)) * (-1 : ℝ) = -(1 / 2 : ℝ) by norm_num]
  unfold upCoeff divCoeff
  rw [Real.div_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2), h2,
    div_inv_eq_mul]
  ring

/-! ## Helper: the `u^(−1/2)` integral from `0` -/

/-- `∫₀^a u^(−1/2) du = 2·√a` for `a ≥ 0`. -/
theorem integral_inv_sqrt_from_zero (a : ℝ) (_ha : 0 ≤ a) :
    ∫ u in (0 : ℝ)..a, u ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt a := by
  have e1 : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2))), e1,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero,
    Real.sqrt_eq_rpow,
    div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring
/-! ## The band-generic upper-bound engine -/

/-- Band-generic upper comparison. Hypotheses: the saddle sits at
`u = U` (the far endpoint of the quadrature range, `uMax = U`); the
integrand's base factorises as `(sV * sO) * (u * (U - u) * (U + g - u))`
with `g > 0` the roots gap; the band geometry gives `U ≤ Λ` and
`Λ ≤ U + g` (so `U ≥ Λ - g ≥ 3Λ/4` under `g ≤ Λ/4`). Conclusion:
`periodQuad ≤ (2/c) * (8 * (Λ * (sV*sO))^(−1/2) + C₀ * (2 + log ((Λ/4)/g)))`
with `C₀ = ((sV*sO) * (Λ/2))^(−1/2)`. The `8 * (Λ * (sV*sO))^(−1/2)`
is the away part, the `C₀ * (2 + log ((Λ/4)/g))` the saddle window. -/
theorem periodQuad_le_aux (b : SolidBody) (Λ E U g sV sO : ℝ)
    (hsV : 0 < sV) (hsO : 0 < sO) (hg : 0 < g) (hg4 : g ≤ Λ / 4)
    (hΛ : 0 < Λ) (hUΛ : U ≤ Λ) (hUge : Λ ≤ U + g)
    (hc : 0 < quadCoeff b) (hU : uMax b Λ E = U)
    (hfact : ∀ u, u * m1SqOfU b Λ E u * m3SqOfU b Λ E u
              = (sV * sO) * (u * (U - u) * (U + g - u)))
    (hint : IntervalIntegrable (quadIntegrand b Λ E) volume 0 U) :
    periodQuad b Λ E ≤ (2 / quadCoeff b) *
      (8 * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ))
        + ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * (2 + Real.log ((Λ / 4) / g))) := by
  have hs : 0 < sV * sO := mul_pos hsV hsO
  have hw : (0 : ℝ) < Λ / 4 := by linarith
  have hΛ2 : (0 : ℝ) < Λ / 2 := by linarith
  have hUw : Λ / 2 ≤ U - Λ / 4 := by linarith
  have hUw0 : (0 : ℝ) ≤ U - Λ / 4 := by linarith
  have hU0 : 0 < U := by linarith
  have haU : U - Λ / 4 ≤ U := by linarith
  -- integrability splits
  have hintA : IntervalIntegrable (quadIntegrand b Λ E) volume 0
      (U - Λ / 4) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hUw0, Set.uIcc_of_le hU0.le]
      exact Set.Icc_subset_Icc le_rfl haU)
  have hintW : IntervalIntegrable (quadIntegrand b Λ E) volume
      (U - Λ / 4) U :=
    hint.mono_set (by
      rw [Set.uIcc_of_le haU, Set.uIcc_of_le hU0.le]
      exact Set.Icc_subset_Icc hUw0 le_rfl)
  -- ═══ AWAY PART: `[0, U − Λ/4]`, both vanishing factors `≥ Λ/4` ═══
  have hrintA : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ)))
      volume 0 (U - Λ / 4) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hmajA : IntervalIntegrable
      (fun u => ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
        * u ^ (-(1 / 2 : ℝ))) volume 0 (U - Λ / 4) :=
    hrintA.const_mul _
  have hptA : ∀ u ∈ Set.Ioo (0 : ℝ) (U - Λ / 4),
      quadIntegrand b Λ E u
        ≤ ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
          * u ^ (-(1 / 2 : ℝ)) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hv : Λ / 4 ≤ U - u := by linarith [hu.2]
    have hgv : Λ / 4 ≤ U + g - u := by linarith [hu.2]
    have hX0 : (0 : ℝ) < (sV * sO) * (u * (Λ / 4) * (Λ / 4)) :=
      mul_pos hs (mul_pos (mul_pos hu0 hw) hw)
    have hXY : (sV * sO) * (u * (Λ / 4) * (Λ / 4))
        ≤ u * m1SqOfU b Λ E u * m3SqOfU b Λ E u := by
      rw [hfact u]
      apply mul_le_mul_of_nonneg_left _ hs.le
      calc u * (Λ / 4) * (Λ / 4) ≤ u * (U - u) * (Λ / 4) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hv hu0.le) hw.le
        _ ≤ u * (U - u) * (U + g - u) :=
            mul_le_mul_of_nonneg_left hgv
              (mul_nonneg hu0.le (sub_nonneg.mpr (le_trans hu.2.le haU)))
    have hrp : (u * m1SqOfU b Λ E u * m3SqOfU b Λ E u) ^ (-(1 / 2 : ℝ))
        ≤ ((sV * sO) * (u * (Λ / 4) * (Λ / 4))) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hX0 hXY (by norm_num)
    have hsplit : ((sV * sO) * (u * (Λ / 4) * (Λ / 4))) ^ (-(1 / 2 : ℝ))
        = ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
          * u ^ (-(1 / 2 : ℝ)) := by
      rw [show (sV * sO) * (u * (Λ / 4) * (Λ / 4))
            = ((sV * sO) * (Λ / 4) ^ 2) * u by ring,
        Real.mul_rpow (mul_nonneg hs.le (pow_nonneg hw.le 2)) hu0.le]
    unfold quadIntegrand
    exact hsplit ▸ hrp
  have hAwayC : ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
        * (2 * Real.sqrt Λ)
      = 8 * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) := by
    have hw2 : ((Λ / 4 : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) = (Λ / 4)⁻¹ := by
      rw [Real.rpow_neg (pow_nonneg hw.le 2), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq hw.le]
    have hsqrtΛ : Real.sqrt Λ / Λ = Λ ^ (-(1 / 2 : ℝ)) := by
      have e : (-(1 / 2 : ℝ)) = 1 / (2 : ℝ) - 1 := by norm_num
      rw [e, Real.rpow_sub hΛ, Real.rpow_one, Real.sqrt_eq_rpow]
    calc ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ)) * (2 * Real.sqrt Λ)
        = (sV * sO) ^ (-(1 / 2 : ℝ)) * (4 / Λ) * (2 * Real.sqrt Λ) := by
          rw [Real.mul_rpow hs.le (pow_nonneg hw.le 2), hw2, inv_div]
      _ = 8 * (Λ ^ (-(1 / 2 : ℝ)) * (sV * sO) ^ (-(1 / 2 : ℝ))) := by
          rw [← hsqrtΛ]
          field_simp
          ring
      _ = 8 * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.mul_rpow hΛ.le hs.le]
  have hAway : (∫ u in (0 : ℝ)..(U - Λ / 4), quadIntegrand b Λ E u)
      ≤ 8 * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) := by
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hUw0
      hintA hmajA hptA
    have hval : (∫ u in (0 : ℝ)..(U - Λ / 4),
          ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
            * u ^ (-(1 / 2 : ℝ)))
        = ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
          * (2 * Real.sqrt (U - Λ / 4)) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_sqrt_from_zero _ hUw0]
    have hC : ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
          * (2 * Real.sqrt (U - Λ / 4))
        ≤ 8 * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) := by
      have h1 : ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
            * (2 * Real.sqrt (U - Λ / 4))
          ≤ ((sV * sO) * (Λ / 4) ^ 2) ^ (-(1 / 2 : ℝ))
            * (2 * Real.sqrt Λ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (by linarith : U - Λ / 4 ≤ Λ))
            (by norm_num : (0 : ℝ) ≤ 2))
          (Real.rpow_nonneg
            (mul_nonneg hs.le (pow_nonneg hw.le 2)) _)
      rwa [hAwayC] at h1
    rw [hval] at hmono
    exact le_trans hmono hC
  -- ═══ WINDOW PART: `[U − Λ/4, U]`, substitute `t = U − u` ═══
  have hΦint : IntervalIntegrable
      (fun t => quadIntegrand b Λ E (U - t)) volume 0 (Λ / 4) := by
    have h2 := hintW.comp_sub_left U
    rw [show U - (U - Λ / 4) = Λ / 4 by ring,
      show U - U = (0 : ℝ) by ring] at h2
    exact h2.symm
  have hwin_eq : (∫ u in (U - Λ / 4)..U, quadIntegrand b Λ E u)
      = ∫ t in (0 : ℝ)..(Λ / 4), quadIntegrand b Λ E (U - t) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := quadIntegrand b Λ E) (a := (0 : ℝ)) (b := Λ / 4) (d := U)
    rw [show U - (0 : ℝ) = U by ring] at h
    exact h.symm
  have hΦ : ∀ t : ℝ, quadIntegrand b Λ E (U - t)
      = ((sV * sO) * (U - t) * t * (g + t)) ^ (-(1 / 2 : ℝ)) := by
    intro t
    unfold quadIntegrand
    rw [hfact (U - t),
      show (sV * sO) * ((U - t) * (U - (U - t)) * (U + g - (U - t)))
        = (sV * sO) * (U - t) * t * (g + t) by ring]
  have hΦ1 : IntervalIntegrable
      (fun t => quadIntegrand b Λ E (U - t)) volume 0 g :=
    hΦint.mono_set (by
      rw [Set.uIcc_of_le hg.le, Set.uIcc_of_le hw.le]
      exact Set.Icc_subset_Icc le_rfl hg4)
  have hΦ2 : IntervalIntegrable
      (fun t => quadIntegrand b Λ E (U - t)) volume g (Λ / 4) :=
    hΦint.mono_set (by
      rw [Set.uIcc_of_le hg4, Set.uIcc_of_le hw.le]
      exact Set.Icc_subset_Icc hg.le le_rfl)
  -- window piece 1: `t ∈ (0, g)`, majorant `C₀ · g^(−1/2) · t^(−1/2)`
  have hpt1 : ∀ t ∈ Set.Ioo (0 : ℝ) g,
      quadIntegrand b Λ E (U - t)
        ≤ (((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * g ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htU : Λ / 2 ≤ U - t := by linarith [ht.2]
    have hsmall : (0 : ℝ) < (sV * sO) * (Λ / 2) * t * g :=
      mul_pos (mul_pos (mul_pos hs hΛ2) ht0) hg
    have hle : (sV * sO) * (Λ / 2) * t * g
        ≤ (sV * sO) * (U - t) * t * (g + t) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htU hs.le) ht0.le)
        (by linarith : g ≤ g + t) hg.le
        (mul_nonneg (mul_pos hs (lt_of_lt_of_le hΛ2 htU)).le ht0.le)
    have hrp : ((sV * sO) * (U - t) * t * (g + t)) ^ (-(1 / 2 : ℝ))
        ≤ ((sV * sO) * (Λ / 2) * t * g) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hsmall hle (by norm_num)
    have hsplit : ((sV * sO) * (Λ / 2) * t * g) ^ (-(1 / 2 : ℝ))
        = (((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * g ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow
          (mul_nonneg (mul_nonneg hs.le hΛ2.le) ht0.le) hg.le,
        Real.mul_rpow (mul_nonneg hs.le hΛ2.le) ht0.le]
      ring
    rw [hΦ t]
    exact hsplit ▸ hrp
  have hmaj1 : IntervalIntegrable
      (fun t => (((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
          * g ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ))) volume 0 g :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul _
  have hI1 : (∫ t in (0 : ℝ)..g, quadIntegrand b Λ E (U - t))
      ≤ ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * 2 := by
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hg.le
      hΦ1 hmaj1 hpt1
    have hg1 : g ^ (-(1 / 2 : ℝ)) * Real.sqrt g = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hg,
        show (-(1 / 2 : ℝ)) + 1 / (2 : ℝ) = 0 by norm_num,
        Real.rpow_zero]
    have hval : (∫ t in (0 : ℝ)..g,
          (((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * g ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ)))
        = ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * 2 := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_sqrt_from_zero _ hg.le]
      calc ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * g ^ (-(1 / 2 : ℝ))
            * (2 * Real.sqrt g)
          = ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * 2
            * (g ^ (-(1 / 2 : ℝ)) * Real.sqrt g) := by ring
        _ = ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * 2 := by
            rw [hg1, mul_one]
    rwa [hval] at hmono
  -- window piece 2: `t ∈ (g, Λ/4)`, majorant `C₀ · t⁻¹`
  have hpt2 : ∀ t ∈ Set.Ioo g (Λ / 4),
      quadIntegrand b Λ E (U - t)
        ≤ ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := lt_trans hg ht.1
    have htU : Λ / 2 ≤ U - t := by linarith [ht.2]
    have hsmall : (0 : ℝ) < (sV * sO) * (Λ / 2) * t * t :=
      mul_pos (mul_pos (mul_pos hs hΛ2) ht0) ht0
    have hle : (sV * sO) * (Λ / 2) * t * t
        ≤ (sV * sO) * (U - t) * t * (g + t) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htU hs.le) ht0.le)
        (by linarith : t ≤ g + t) ht0.le
        (mul_nonneg (mul_pos hs (lt_of_lt_of_le hΛ2 htU)).le ht0.le)
    have hrp : ((sV * sO) * (U - t) * t * (g + t)) ^ (-(1 / 2 : ℝ))
        ≤ ((sV * sO) * (Λ / 2) * t * t) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hsmall hle (by norm_num)
    have hsplit : ((sV * sO) * (Λ / 2) * t * t) ^ (-(1 / 2 : ℝ))
        = ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * t⁻¹ := by
      rw [show (sV * sO) * (Λ / 2) * t * t
            = ((sV * sO) * (Λ / 2)) * (t * t) by ring,
        Real.mul_rpow (mul_nonneg hs.le hΛ2.le)
          (mul_nonneg ht0.le ht0.le),
        Real.mul_rpow ht0.le ht0.le, ← Real.rpow_add ht0,
        show (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    rw [hΦ t]
    exact hsplit ▸ hrp
  have hmaj2 : IntervalIntegrable
      (fun t => ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * t⁻¹)
      volume g (Λ / 4) := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc g (Λ / 4)) := by
      rw [Set.uIcc_of_le hg4]
      exact continuousOn_id.inv₀
        (fun t ht => ne_of_gt (lt_of_lt_of_le hg ht.1))
    exact hcont.intervalIntegrable.const_mul _
  have hI2 : (∫ t in g..(Λ / 4), quadIntegrand b Λ E (U - t))
      ≤ ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
        * (Real.log (Λ / 4) - Real.log g) := by
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hg4
      hΦ2 hmaj2 hpt2
    have hval : (∫ t in g..(Λ / 4),
          ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * t⁻¹)
        = ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
          * (Real.log (Λ / 4) - Real.log g) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_of_pos hg hw, Real.log_div hw.ne' hg.ne']
    rwa [hval] at hmono
  have hWin : (∫ u in (U - Λ / 4)..U, quadIntegrand b Λ E u)
      ≤ ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
        * (2 + Real.log ((Λ / 4) / g)) := by
    rw [hwin_eq,
      ← intervalIntegral.integral_add_adjacent_intervals hΦ1 hΦ2]
    have hlog : Real.log (Λ / 4) - Real.log g
        = Real.log ((Λ / 4) / g) :=
      (Real.log_div hw.ne' hg.ne').symm
    calc (∫ t in (0 : ℝ)..g, quadIntegrand b Λ E (U - t))
          + ∫ t in g..(Λ / 4), quadIntegrand b Λ E (U - t)
        ≤ ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ)) * 2
          + ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * (Real.log (Λ / 4) - Real.log g) :=
        add_le_add hI1 hI2
      _ = ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * (2 + Real.log ((Λ / 4) / g)) := by
          rw [hlog]; ring
  -- ═══ ASSEMBLY ═══
  have hsum : (∫ u in (0 : ℝ)..(U - Λ / 4), quadIntegrand b Λ E u)
        + ∫ u in (U - Λ / 4)..U, quadIntegrand b Λ E u
      ≤ 8 * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ))
        + ((sV * sO) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
          * (2 + Real.log ((Λ / 4) / g)) :=
    add_le_add hAway hWin
  unfold periodQuad
  rw [hU, ← intervalIntegral.integral_add_adjacent_intervals
    hintA hintW]
  exact mul_le_mul_of_nonneg_left hsum
    (div_nonneg (by norm_num) hc.le)

/-! ## Headline: the upper bound, top band -/

/-- **N3 upper bound, top band, `|log τ|` form.** For `E` in the
top band with roots gap `≤ Λ/4` (implied range `τ ≤ B/8`) and
`τ = E - E_sep ≤ 1`:
`periodQuad ≤ upCoeff * |log τ| + upC2top`, where
`upCoeff = √2 * divCoeff` and `upC2top` is explicit (both in
`Λ, b` only). Together with N2's `periodQuad_ge_abs_log_top`
(whose gap hypothesis `≤ Λ/2` is implied), this makes the rate
two-sided `Θ(|log τ|)`. QUADRATURE period throughout. -/
theorem periodQuad_le_abs_log_top (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inTopBand b Λ E)
    (hnear : uRoot1 b Λ E - uRoot3 b Λ E ≤ Λ / 4)
    (hτ1 : E - sepEnergy b Λ ≤ 1) :
    periodQuad b Λ E
      ≤ upCoeff b Λ * |Real.log (E - sepEnergy b Λ)|
        + upC2top b Λ := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hτ : 0 < E - sepEnergy b Λ := by linarith [hband.1]
  have hK : 0 < b.I1 * b.I2 / (b.I2 - b.I1) :=
    div_pos (mul_pos b.I1_pos b.I2_pos) (sub_pos.mpr h12)
  have hs1 := slope1_pos b h12 h23
  have hid2 : slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E)
      = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * (E - sepEnergy b Λ)) := by
    rw [slope1_mul_root_diff b h12 h23 Λ E]; congr 1; rw [← hsep2]; ring
  have hg : 0 < uRoot1 b Λ E - uRoot3 b Λ E := by
    have hδ : 0 < 2 * (E - sepEnergy b Λ) := by linarith
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonneg_of_nonpos hs1.le hcon
    linarith [hid2, mul_pos hK hδ]
  have hgid : uRoot1 b Λ E - uRoot3 b Λ E
      = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * (E - sepEnergy b Λ))
        / slope1 b := by
    rw [eq_div_iff hs1.ne', mul_comm]; exact hid2
  have hfact : ∀ u, u * m1SqOfU b Λ E u * m3SqOfU b Λ E u
      = (slope3 b * slope1 b) * (u * (uRoot3 b Λ E - u) *
          (uRoot3 b Λ E + (uRoot1 b Λ E - uRoot3 b Λ E) - u)) := by
    intro u
    rw [m1SqOfU_eq_slope1_mul b h12 h23,
      m3SqOfU_eq_slope3_mul b h12 h23]
    ring
  have hint : IntervalIntegrable (quadIntegrand b Λ E) volume 0
      (uRoot3 b Λ E) := by
    have h := periodQuad_intervalIntegrable_top b h12 h23 Λ E hband
    rwa [uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband] at h
  have haux := periodQuad_le_aux b Λ E (uRoot3 b Λ E)
    (uRoot1 b Λ E - uRoot3 b Λ E) (slope3 b) (slope1 b)
    (slope3_pos b h12 h23) hs1 hg hnear hΛ
    (uRoot3_lt_of_topBand b h12 Λ E hband).le
    (by have h := le_uRoot1_of_topBand b h23 Λ E hband; linarith)
    (quadCoeff_pos b h12 h23)
    (uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband) hfact hint
  have hB := topBandB_pos b h12 h23 Λ hΛ
  have hfrac : (Λ / 4) / (uRoot1 b Λ E - uRoot3 b Λ E)
      = topBandB b Λ / (2 * (E - sepEnergy b Λ)) := by
    rw [hgid]; unfold topBandB; field_simp
  have hlog : Real.log ((Λ / 4) / (uRoot1 b Λ E - uRoot3 b Λ E))
      = Real.log (topBandB b Λ / 2)
        + |Real.log (E - sepEnergy b Λ)| := by
    have hlogτ : Real.log (E - sepEnergy b Λ) ≤ 0 :=
      Real.log_nonpos hτ.le hτ1
    have e1 : Real.log (topBandB b Λ / (2 * (E - sepEnergy b Λ)))
        = Real.log (topBandB b Λ / 2)
          - Real.log (E - sepEnergy b Λ) := by
      rw [show topBandB b Λ / (2 * (E - sepEnergy b Λ))
            = (topBandB b Λ / 2) / (E - sepEnergy b Λ)
            from (div_div _ _ _).symm,
        Real.log_div (div_pos hB (by norm_num : (0 : ℝ) < 2)).ne'
          hτ.ne']
    rw [hfrac, e1, abs_of_nonpos hlogτ]; ring
  have e1 : Λ * (slope3 b * slope1 b) = Λ * slope1 b * slope3 b := by
    ring
  have e2 : (slope3 b * slope1 b) * (Λ / 2)
      = Λ * slope1 b * slope3 b / 2 := by ring
  have hmass : (2 / quadCoeff b)
        * (8 * (Λ * (slope3 b * slope1 b)) ^ (-(1 / 2 : ℝ))
          + ((slope3 b * slope1 b) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * (2 + Real.log ((Λ / 4)
                / (uRoot1 b Λ E - uRoot3 b Λ E))))
      = upCoeff b Λ * |Real.log (E - sepEnergy b Λ)|
        + upC2top b Λ := by
    rw [e1, e2, hlog]
    unfold upCoeff upC2top
    ring
  exact hmass ▸ haux

/-! ## Headline: the upper bound, bottom band -/

/-- **N3 upper bound, bottom band, `|log τ|` form.** Mirror of
`periodQuad_le_abs_log_top` with `τ = E_sep - E`, saddle root
`uRoot1`, band constant `botBandB`. -/
theorem periodQuad_le_abs_log_bot (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inBotBand b Λ E)
    (hnear : uRoot3 b Λ E - uRoot1 b Λ E ≤ Λ / 4)
    (hτ1 : sepEnergy b Λ - E ≤ 1) :
    periodQuad b Λ E
      ≤ upCoeff b Λ * |Real.log (sepEnergy b Λ - E)|
        + upC2bot b Λ := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hτ : 0 < sepEnergy b Λ - E := by linarith [hband.2]
  have hK : 0 < b.I2 * b.I3 / (b.I3 - b.I2) :=
    div_pos (mul_pos b.I2_pos b.I3_pos) (sub_pos.mpr h23)
  have hs3 := slope3_pos b h12 h23
  have hid2 : slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E)
      = (b.I2 * b.I3 / (b.I3 - b.I2)) * (2 * (sepEnergy b Λ - E)) := by
    rw [slope3_mul_root_diff b h12 h23 Λ E]; congr 1; rw [← hsep2]; ring
  have hg : 0 < uRoot3 b Λ E - uRoot1 b Λ E := by
    have hδ : 0 < 2 * (sepEnergy b Λ - E) := by linarith
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonneg_of_nonpos hs3.le hcon
    linarith [hid2, mul_pos hK hδ]
  have hgid : uRoot3 b Λ E - uRoot1 b Λ E
      = (b.I2 * b.I3 / (b.I3 - b.I2)) * (2 * (sepEnergy b Λ - E))
        / slope3 b := by
    rw [eq_div_iff hs3.ne', mul_comm]; exact hid2
  have hfact : ∀ u, u * m1SqOfU b Λ E u * m3SqOfU b Λ E u
      = (slope1 b * slope3 b) * (u * (uRoot1 b Λ E - u) *
          (uRoot1 b Λ E + (uRoot3 b Λ E - uRoot1 b Λ E) - u)) := by
    intro u
    rw [m1SqOfU_eq_slope1_mul b h12 h23,
      m3SqOfU_eq_slope3_mul b h12 h23]
    ring
  have hint : IntervalIntegrable (quadIntegrand b Λ E) volume 0
      (uRoot1 b Λ E) := by
    have h := periodQuad_intervalIntegrable_bot b h12 h23 Λ E hband
    rwa [uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband] at h
  have haux := periodQuad_le_aux b Λ E (uRoot1 b Λ E)
    (uRoot3 b Λ E - uRoot1 b Λ E) (slope1 b) (slope3 b)
    (slope1_pos b h12 h23) hs3 hg hnear hΛ
    (uRoot1_lt_of_botBand b h23 Λ E hband).le
    (by have h := le_uRoot3_of_botBand b h12 Λ E hband; linarith)
    (quadCoeff_pos b h12 h23)
    (uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband) hfact hint
  have hB := botBandB_pos b h12 h23 Λ hΛ
  have hfrac : (Λ / 4) / (uRoot3 b Λ E - uRoot1 b Λ E)
      = botBandB b Λ / (2 * (sepEnergy b Λ - E)) := by
    rw [hgid]; unfold botBandB; field_simp
  have hlog : Real.log ((Λ / 4) / (uRoot3 b Λ E - uRoot1 b Λ E))
      = Real.log (botBandB b Λ / 2)
        + |Real.log (sepEnergy b Λ - E)| := by
    have hlogτ : Real.log (sepEnergy b Λ - E) ≤ 0 :=
      Real.log_nonpos hτ.le hτ1
    have e1 : Real.log (botBandB b Λ / (2 * (sepEnergy b Λ - E)))
        = Real.log (botBandB b Λ / 2)
          - Real.log (sepEnergy b Λ - E) := by
      rw [show botBandB b Λ / (2 * (sepEnergy b Λ - E))
            = (botBandB b Λ / 2) / (sepEnergy b Λ - E)
            from (div_div _ _ _).symm,
        Real.log_div (div_pos hB (by norm_num : (0 : ℝ) < 2)).ne'
          hτ.ne']
    rw [hfrac, e1, abs_of_nonpos hlogτ]; ring
  have e1 : Λ * (slope1 b * slope3 b) = Λ * slope1 b * slope3 b := by
    ring
  have e2 : (slope1 b * slope3 b) * (Λ / 2)
      = Λ * slope1 b * slope3 b / 2 := by ring
  have hmass : (2 / quadCoeff b)
        * (8 * (Λ * (slope1 b * slope3 b)) ^ (-(1 / 2 : ℝ))
          + ((slope1 b * slope3 b) * (Λ / 2)) ^ (-(1 / 2 : ℝ))
            * (2 + Real.log ((Λ / 4)
                / (uRoot3 b Λ E - uRoot1 b Λ E))))
      = upCoeff b Λ * |Real.log (sepEnergy b Λ - E)|
        + upC2bot b Λ := by
    rw [e1, e2, hlog]
    unfold upCoeff upC2bot
    ring
  exact hmass ▸ haux

/-! ## The two-sided rate -/

/-- **N3 headline, top band: the QUADRATURE period is
`Θ(|log τ|)`** as `E → E_sep` from the top band — the explicit
pair: N2's lower bound below, this module's upper bound above,
same hypotheses (roots gap `≤ Λ/4`, which implies N2's `≤ Λ/2`;
`τ = E - E_sep ≤ 1`). Leading constants: `divCoeff` below,
`√2 * divCoeff` above. -/
theorem periodQuad_theta_top (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inTopBand b Λ E)
    (hnear : uRoot1 b Λ E - uRoot3 b Λ E ≤ Λ / 4)
    (hτ1 : E - sepEnergy b Λ ≤ 1) :
    divCoeff b Λ * |Real.log (E - sepEnergy b Λ)|
        - divCoeff b Λ * |Real.log (topBandB b Λ)|
      ≤ periodQuad b Λ E ∧
    periodQuad b Λ E
      ≤ upCoeff b Λ * |Real.log (E - sepEnergy b Λ)|
        + upC2top b Λ :=
  ⟨periodQuad_ge_abs_log_top b h12 h23 Λ hΛ E hband
      (le_trans hnear (by linarith)) hτ1,
    periodQuad_le_abs_log_top b h12 h23 Λ hΛ E hband hnear hτ1⟩

/-- **N3 headline, bottom band: the QUADRATURE period is
`Θ(|log τ|)`** as `E → E_sep` from the bottom band. Mirror of
`periodQuad_theta_top` with `τ = E_sep - E`. -/
theorem periodQuad_theta_bot (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inBotBand b Λ E)
    (hnear : uRoot3 b Λ E - uRoot1 b Λ E ≤ Λ / 4)
    (hτ1 : sepEnergy b Λ - E ≤ 1) :
    divCoeff b Λ * |Real.log (sepEnergy b Λ - E)|
        - divCoeff b Λ * |Real.log (botBandB b Λ)|
      ≤ periodQuad b Λ E ∧
    periodQuad b Λ E
      ≤ upCoeff b Λ * |Real.log (sepEnergy b Λ - E)|
        + upC2bot b Λ :=
  ⟨periodQuad_ge_abs_log_bot b h12 h23 Λ hΛ E hband
      (le_trans hnear (by linarith)) hτ1,
    periodQuad_le_abs_log_bot b h12 h23 Λ hΛ E hband hnear hτ1⟩
