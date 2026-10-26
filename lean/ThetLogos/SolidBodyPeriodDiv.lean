import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import ThetLogos.SolidBodyPeriodQuad

/-!
# ThetLogos.SolidBodyPeriodDiv — N2: the quadrature period diverges at `E_sep`

Stage N2 of the nonlinear rigid-body program (scoping memo
`nonlinear-rigid-scoping-2026-10-26.md` §1), built on N1's
quadrature period (`SolidBodyPeriodQuad`), N0's affine package
(`SolidBodyPolhode`) and the portrait brick. Fixed body, frozen
coefficients, abstract body only.

## ⚠ Honesty fence — read first

The period here is the **quadrature period** of N1: the return
time read off the first integrals by quadrature. That this number
*is* the return time of actual Euler trajectories is stage **N4**
(deferred; L hypothesis-fed / L+ full) and is **not** proved here —
the identification is classical T4. Every use of the word "period"
in this file means the quadrature period.

## What is proved (T1, from definitions/hypotheses; classical core T4)

For a body with `0 < I₁ < I₂ < I₃` and `Λ > 0`, as `E → E_sep`
**from either open band**, the quadrature period diverges at
least logarithmically:

* `periodQuad b Λ E ≥ divCoeff b Λ · |log |E − E_sep|| − c₂`,
  with `divCoeff b Λ = (2/quadCoeff b)·(Λ·slope1·slope3)^(−1/2) > 0`
  explicit and `c₂ = divCoeff · |log B|` with `B` the explicit
  band constant (`topBandB`, `botBandB`) — in the sharper form
  `periodQuad ≥ divCoeff · log (1 + B/|E − E_sep|)`
  (`periodQuad_ge_log_top`, `periodQuad_ge_log_bot`);
* hence `Tendsto (periodQuad b Λ) atTop` as `E → E_sep` within
  either side (`periodQuad_tendsto_atTop_top`,
  `periodQuad_tendsto_atTop_bot`).

The proof is the memo's comparison, no elliptic machinery: on a
window of fixed width `Λ/2` below `uMax`, with `v = uMax − u` and
`g` the gap between the two roots (`g = κ·|E − E_sep|`, `κ > 0`),
the integrand dominates `(Λ·slope1·slope3)^(−1/2)·(g + v)⁻¹`
pointwise, whose antiderivative is `log` — plain FTC via
`integral_comp_sub_left` and `integral_inv_of_pos`.

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

/-- The divergence coefficient: `c₁ = (2/c)·(Λ·slope1·slope3)^(−1/2)`,
the `(2/quadCoeff)` of `periodQuad` times the comparison constant
from the saddle window. -/
noncomputable def divCoeff (b : SolidBody) (Λ : ℝ) : ℝ :=
  (2 / quadCoeff b) * (Λ * slope1 b * slope3 b) ^ (-(1 / 2 : ℝ))

/-- The top band's scale constant: with `τ = E − E_sep > 0` and
roots gap `g = uRoot1 − uRoot3 = κ·τ`, one has `Λ/(2g) =
topBandB / τ`. -/
noncomputable def topBandB (b : SolidBody) (Λ : ℝ) : ℝ :=
  Λ * slope1 b / (4 * (b.I1 * b.I2 / (b.I2 - b.I1)))

/-- The bottom band's scale constant: with `τ = E_sep − E > 0` and
roots gap `g = uRoot3 − uRoot1 = κ·τ`, one has `Λ/(2g) =
botBandB / τ`. -/
noncomputable def botBandB (b : SolidBody) (Λ : ℝ) : ℝ :=
  Λ * slope3 b / (4 * (b.I2 * b.I3 / (b.I3 - b.I2)))

theorem divCoeff_pos (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) : 0 < divCoeff b Λ :=
  mul_pos (div_pos (by norm_num) (quadCoeff_pos b h12 h23))
    (Real.rpow_pos_of_pos
      (mul_pos (mul_pos hΛ (slope1_pos b h12 h23)) (slope3_pos b h12 h23)) _)

theorem topBandB_pos (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) : 0 < topBandB b Λ :=
  div_pos (mul_pos hΛ (slope1_pos b h12 h23))
    (mul_pos (by norm_num)
      (div_pos (mul_pos b.I1_pos b.I2_pos) (sub_pos.mpr h12)))

theorem botBandB_pos (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) : 0 < botBandB b Λ :=
  div_pos (mul_pos hΛ (slope3_pos b h12 h23))
    (mul_pos (by norm_num)
      (div_pos (mul_pos b.I2_pos b.I3_pos) (sub_pos.mpr h23)))

/-- `2 * E_sep = Λ/I₂`, the separatrix as the middle level. -/
theorem two_mul_sepEnergy (b : SolidBody) (Λ : ℝ) :
    2 * sepEnergy b Λ = Λ / b.I2 := by
  unfold sepEnergy
  field_simp

/-- Pure field-algebra identity behind the nearness windows:
with the roots-gap constant `K ≠ 0`, the window half-width
`Λ·s/(4K)` satisfies `K · (2 · (Λ·s/(4K))) = Λ/2 · s`. Proved
with `K` opaque so `field_simp` stays tame. -/
theorem aux_mul_two_div (Λ s K : ℝ) (hK : K ≠ 0) :
    K * (2 * (Λ * s / (4 * K))) = Λ / 2 * s := by
  calc K * (2 * (Λ * s / (4 * K)))
      = K * (2 * (Λ * s)) / (4 * K) := by
        rw [← mul_div_assoc, mul_div_assoc']
    _ = (4 * K) * (Λ / 2 * s) / (4 * K) := by
        congr 1
        ring
    _ = Λ / 2 * s :=
        mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hK)

/-! ## The comparison core (band-generic) -/

/-- **The window comparison.** Abstract form of the N2 estimate.
Given the factored product identity
`u·m1·m3 = (sV·sO)·(u·(U−u)·(U+g−u))` (the `U`-factor vanishes at
the window's right end `U`, the other factor is `U+g−u` with gap
`g > 0`), `U < Λ`, `Λ ≤ U + g`, `g ≤ Λ/2`, and integrability of the
quadrature integrand on `0..U` (N1), the period is at least
`(2/c)·(Λ·sV·sO)^(−1/2)·(log (g + Λ/2) − log g)`. -/
theorem periodQuad_ge_log_aux (b : SolidBody) (Λ E U g sV sO : ℝ)
    (hsV : 0 < sV) (hsO : 0 < sO) (hg : 0 < g) (hg2 : g ≤ Λ / 2)
    (hΛ : 0 < Λ) (hUΛ : U < Λ) (hUge : Λ ≤ U + g)
    (hc : 0 < quadCoeff b) (hU : uMax b Λ E = U)
    (hfact : ∀ u, u * m1SqOfU b Λ E u * m3SqOfU b Λ E u
              = (sV * sO) * (u * (U - u) * (U + g - u)))
    (hint : IntervalIntegrable (quadIntegrand b Λ E) volume 0 U) :
    (2 / quadCoeff b) * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) *
        (Real.log (g + Λ / 2) - Real.log g) ≤ periodQuad b Λ E := by
  have hP : 0 < sV * sO := mul_pos hsV hsO
  have hUw : 0 ≤ U - Λ / 2 := by linarith
  have hU0 : 0 < U := by linarith
  have haU : U - Λ / 2 ≤ U := by linarith
  have hint1 : IntervalIntegrable (quadIntegrand b Λ E) volume 0 (U - Λ / 2) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hUw, Set.uIcc_of_le hU0.le]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have hint2 : IntervalIntegrable (quadIntegrand b Λ E) volume (U - Λ / 2) U :=
    hint.mono_set (by
      rw [Set.uIcc_of_le haU, Set.uIcc_of_le hU0.le]
      exact Set.Icc_subset_Icc (by linarith) le_rfl)
  -- The integrand is nonnegative on the left piece.
  have hI1 : 0 ≤ ∫ u in (0 : ℝ)..(U - Λ / 2), quadIntegrand b Λ E u := by
    apply intervalIntegral.integral_nonneg hUw
    intro u hu
    unfold quadIntegrand
    rw [hfact u]
    apply Real.rpow_nonneg
    exact mul_nonneg hP.le
      (mul_nonneg (mul_nonneg hu.1 (by linarith [hu.2, hΛ]))
        (by linarith [hu.2, hg, hΛ]))
  -- Pointwise comparison on the open window.
  have hpt : ∀ u ∈ Set.Ioo (U - Λ / 2) U,
      (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) * (U + g - u)⁻¹
        ≤ quadIntegrand b Λ E u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hv : 0 < U - u := sub_pos.mpr hu.2
    have hgv : 0 < U + g - u := by linarith
    have huΛ : u < Λ := lt_trans hu.2 hUΛ
    have hX0 : 0 < u * m1SqOfU b Λ E u * m3SqOfU b Λ E u := by
      rw [hfact u]
      exact mul_pos hP (mul_pos (mul_pos hu0 hv) hgv)
    have hXY : u * m1SqOfU b Λ E u * m3SqOfU b Λ E u
        ≤ (Λ * (sV * sO)) * (U + g - u) ^ 2 := by
      rw [hfact u]
      have h1 : u * (U - u) ≤ Λ * (U + g - u) :=
        mul_le_mul huΛ.le (by linarith : U - u ≤ U + g - u) hv.le hΛ.le
      have h2 : u * (U - u) * (U + g - u)
          ≤ Λ * (U + g - u) * (U + g - u) :=
        mul_le_mul h1 (le_refl _) hgv.le (mul_nonneg hΛ.le hgv.le)
      calc (sV * sO) * (u * (U - u) * (U + g - u))
          ≤ (sV * sO) * (Λ * (U + g - u) * (U + g - u)) :=
            mul_le_mul_of_nonneg_left h2 hP.le
        _ = (Λ * (sV * sO)) * (U + g - u) ^ 2 := by ring
    have hrp : ((Λ * (sV * sO)) * (U + g - u) ^ 2) ^ (-(1 / 2 : ℝ))
        ≤ quadIntegrand b Λ E u := by
      unfold quadIntegrand
      exact Real.rpow_le_rpow_of_nonpos hX0 hXY (by norm_num)
    have hsplit : ((Λ * (sV * sO)) * (U + g - u) ^ 2) ^ (-(1 / 2 : ℝ))
        = (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) * (U + g - u)⁻¹ := by
      rw [Real.mul_rpow (mul_nonneg hΛ.le hP.le) (sq_nonneg _)]
      congr 1
      rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq_eq_abs, abs_of_pos hgv]
    rwa [hsplit] at hrp
  -- The comparison function is integrable on the window.
  have hcomp : IntervalIntegrable
      (fun u => (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) * (U + g - u)⁻¹)
      volume (U - Λ / 2) U := by
    have hcont : ContinuousOn
        (fun u => (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) * (U + g - u)⁻¹)
        (Set.uIcc (U - Λ / 2) U) := by
      rw [Set.uIcc_of_le haU]
      exact continuousOn_const.mul
        ((continuousOn_const.sub continuousOn_id).inv₀
          (fun u hu => ne_of_gt (by linarith [hu.2] : (0 : ℝ) < U + g - u)))
    exact hcont.intervalIntegrable
  have hI2 : (∫ u in (U - Λ / 2)..U,
        (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) * (U + g - u)⁻¹)
      ≤ ∫ u in (U - Λ / 2)..U, quadIntegrand b Λ E u :=
    intervalIntegral.integral_mono_on_of_le_Ioo haU hcomp hint2 hpt
  -- The comparison integral, by FTC against `log`.
  have hI2val : (∫ u in (U - Λ / 2)..U,
        (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) * (U + g - u)⁻¹)
      = (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) *
          (Real.log (g + Λ / 2) - Real.log g) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h : (∫ u in (U - Λ / 2)..U, (U + g - u)⁻¹)
        = ∫ t in (U + g) - U..(U + g) - (U - Λ / 2), t⁻¹ :=
      intervalIntegral.integral_comp_sub_left
        (f := fun t : ℝ => t⁻¹) (a := U - Λ / 2) (b := U) (d := U + g)
    rw [show (U + g) - U = g by ring,
      show (U + g) - (U - Λ / 2) = g + Λ / 2 by ring] at h
    rw [h, integral_inv_of_pos hg (by linarith : (0 : ℝ) < g + Λ / 2),
      Real.log_div (by linarith : g + Λ / 2 ≠ 0) hg.ne']
  -- Assemble: split the period integral at the window's left edge.
  have hsum : (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) *
        (Real.log (g + Λ / 2) - Real.log g)
      ≤ (∫ u in (0 : ℝ)..(U - Λ / 2), quadIntegrand b Λ E u) +
          ∫ u in (U - Λ / 2)..U, quadIntegrand b Λ E u := by
    have h2' : (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) *
          (Real.log (g + Λ / 2) - Real.log g)
        ≤ ∫ u in (U - Λ / 2)..U, quadIntegrand b Λ E u := by
      rw [← hI2val]; exact hI2
    linarith
  unfold periodQuad
  rw [hU, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  calc (2 / quadCoeff b) * (Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) *
          (Real.log (g + Λ / 2) - Real.log g)
      = (2 / quadCoeff b) * ((Λ * (sV * sO)) ^ (-(1 / 2 : ℝ)) *
          (Real.log (g + Λ / 2) - Real.log g)) := by ring
    _ ≤ (2 / quadCoeff b) * ((∫ u in (0 : ℝ)..(U - Λ / 2),
            quadIntegrand b Λ E u) +
          ∫ u in (U - Λ / 2)..U, quadIntegrand b Λ E u) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) hc.le)

/-! ## The headline bound, both bands -/

/-- **Divergence bound, top band.** For `E` in the top band with
roots gap `uRoot1 − uRoot3 ≤ Λ/2` (the band near `E_sep`),
`periodQuad b Λ E ≥ divCoeff b Λ · log (1 + topBandB/τ)`,
`τ = E − E_sep > 0`. -/
theorem periodQuad_ge_log_top (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inTopBand b Λ E)
    (hnear : uRoot1 b Λ E - uRoot3 b Λ E ≤ Λ / 2) :
    divCoeff b Λ * Real.log (1 + topBandB b Λ / (E - sepEnergy b Λ))
      ≤ periodQuad b Λ E := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hτ : 0 < E - sepEnergy b Λ := by linarith [hband.1]
  have hK : 0 < b.I1 * b.I2 / (b.I2 - b.I1) :=
    div_pos (mul_pos b.I1_pos b.I2_pos) (sub_pos.mpr h12)
  have hs1 := slope1_pos b h12 h23
  have hid2 : slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E)
      = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * (E - sepEnergy b Λ)) := by
    rw [slope1_mul_root_diff b h12 h23 Λ E]
    congr 1
    rw [← hsep2]; ring
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
    rw [m1SqOfU_eq_slope1_mul b h12 h23, m3SqOfU_eq_slope3_mul b h12 h23]
    ring
  have hint : IntervalIntegrable (quadIntegrand b Λ E) volume 0
      (uRoot3 b Λ E) := by
    have h := periodQuad_intervalIntegrable_top b h12 h23 Λ E hband
    rwa [uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband] at h
  have haux := periodQuad_ge_log_aux b Λ E (uRoot3 b Λ E)
    (uRoot1 b Λ E - uRoot3 b Λ E) (slope3 b) (slope1 b)
    (slope3_pos b h12 h23) hs1 hg hnear hΛ
    (uRoot3_lt_of_topBand b h12 Λ E hband)
    (by linarith [le_uRoot1_of_topBand b h23 Λ E hband])
    (quadCoeff_pos b h12 h23)
    (uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband) hfact hint
  have e1 : Λ * (slope3 b * slope1 b) = Λ * slope1 b * slope3 b := by ring
  have e2 : Real.log (uRoot1 b Λ E - uRoot3 b Λ E + Λ / 2)
        - Real.log (uRoot1 b Λ E - uRoot3 b Λ E)
      = Real.log (1 + topBandB b Λ / (E - sepEnergy b Λ)) := by
    have hlog1 : Real.log (uRoot1 b Λ E - uRoot3 b Λ E + Λ / 2)
          - Real.log (uRoot1 b Λ E - uRoot3 b Λ E)
        = Real.log ((uRoot1 b Λ E - uRoot3 b Λ E + Λ / 2)
            / (uRoot1 b Λ E - uRoot3 b Λ E)) :=
      (Real.log_div (by linarith : uRoot1 b Λ E - uRoot3 b Λ E + Λ / 2 ≠ 0)
        hg.ne').symm
    have hfrac : (uRoot1 b Λ E - uRoot3 b Λ E + Λ / 2)
          / (uRoot1 b Λ E - uRoot3 b Λ E)
        = 1 + topBandB b Λ / (E - sepEnergy b Λ) := by
      have h1 : (uRoot1 b Λ E - uRoot3 b Λ E + Λ / 2)
            / (uRoot1 b Λ E - uRoot3 b Λ E)
          = 1 + (Λ / 2) / (uRoot1 b Λ E - uRoot3 b Λ E) := by
        rw [add_div, div_self hg.ne']
      have h2 : (Λ / 2) / (uRoot1 b Λ E - uRoot3 b Λ E)
          = topBandB b Λ / (E - sepEnergy b Λ) := by
        rw [hgid]
        unfold topBandB
        field_simp [hτ.ne', hK.ne', hs1.ne', (sub_pos.mpr h12).ne']
        ring
      rw [h1, h2]
    rw [hlog1, hfrac]
  rw [e1, e2] at haux
  exact haux

/-- **Divergence bound, bottom band.** For `E` in the bottom band
with roots gap `uRoot3 − uRoot1 ≤ Λ/2`,
`periodQuad b Λ E ≥ divCoeff b Λ · log (1 + botBandB/τ)`,
`τ = E_sep − E > 0`. -/
theorem periodQuad_ge_log_bot (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inBotBand b Λ E)
    (hnear : uRoot3 b Λ E - uRoot1 b Λ E ≤ Λ / 2) :
    divCoeff b Λ * Real.log (1 + botBandB b Λ / (sepEnergy b Λ - E))
      ≤ periodQuad b Λ E := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hτ : 0 < sepEnergy b Λ - E := by linarith [hband.2]
  have hK : 0 < b.I2 * b.I3 / (b.I3 - b.I2) :=
    div_pos (mul_pos b.I2_pos b.I3_pos) (sub_pos.mpr h23)
  have hs3 := slope3_pos b h12 h23
  have hid2 : slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E)
      = (b.I2 * b.I3 / (b.I3 - b.I2)) * (2 * (sepEnergy b Λ - E)) := by
    rw [slope3_mul_root_diff b h12 h23 Λ E]
    congr 1
    rw [← hsep2]; ring
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
    rw [m1SqOfU_eq_slope1_mul b h12 h23, m3SqOfU_eq_slope3_mul b h12 h23]
    ring
  have hint : IntervalIntegrable (quadIntegrand b Λ E) volume 0
      (uRoot1 b Λ E) := by
    have h := periodQuad_intervalIntegrable_bot b h12 h23 Λ E hband
    rwa [uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband] at h
  have haux := periodQuad_ge_log_aux b Λ E (uRoot1 b Λ E)
    (uRoot3 b Λ E - uRoot1 b Λ E) (slope1 b) (slope3 b)
    (slope1_pos b h12 h23) hs3 hg hnear hΛ
    (uRoot1_lt_of_botBand b h23 Λ E hband)
    (by linarith [le_uRoot3_of_botBand b h12 Λ E hband])
    (quadCoeff_pos b h12 h23)
    (uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband) hfact hint
  have e1 : Λ * (slope1 b * slope3 b) = Λ * slope1 b * slope3 b := by ring
  have e2 : Real.log (uRoot3 b Λ E - uRoot1 b Λ E + Λ / 2)
        - Real.log (uRoot3 b Λ E - uRoot1 b Λ E)
      = Real.log (1 + botBandB b Λ / (sepEnergy b Λ - E)) := by
    have hlog1 : Real.log (uRoot3 b Λ E - uRoot1 b Λ E + Λ / 2)
          - Real.log (uRoot3 b Λ E - uRoot1 b Λ E)
        = Real.log ((uRoot3 b Λ E - uRoot1 b Λ E + Λ / 2)
            / (uRoot3 b Λ E - uRoot1 b Λ E)) :=
      (Real.log_div (by linarith : uRoot3 b Λ E - uRoot1 b Λ E + Λ / 2 ≠ 0)
        hg.ne').symm
    have hfrac : (uRoot3 b Λ E - uRoot1 b Λ E + Λ / 2)
          / (uRoot3 b Λ E - uRoot1 b Λ E)
        = 1 + botBandB b Λ / (sepEnergy b Λ - E) := by
      have h1 : (uRoot3 b Λ E - uRoot1 b Λ E + Λ / 2)
            / (uRoot3 b Λ E - uRoot1 b Λ E)
          = 1 + (Λ / 2) / (uRoot3 b Λ E - uRoot1 b Λ E) := by
        rw [add_div, div_self hg.ne']
      have h2 : (Λ / 2) / (uRoot3 b Λ E - uRoot1 b Λ E)
          = botBandB b Λ / (sepEnergy b Λ - E) := by
        rw [hgid]
        unfold botBandB
        field_simp [hτ.ne', hK.ne', hs3.ne', (sub_pos.mpr h23).ne']
        ring
      rw [h1, h2]
    rw [hlog1, hfrac]
  rw [e1, e2] at haux
  exact haux

/-! ## The memo's registered form: `c₁·|log |E − E_sep|| − c₂` -/

/-- **Divergence, memo form, top band.** With `τ = E − E_sep ∈
(0, 1]` and the roots gap `≤ Λ/2`:
`periodQuad b Λ E ≥ divCoeff · |log τ| − divCoeff · |log topBandB|`
— i.e. `P(E) ≥ c₁·|log|E − E_sep|| − c₂` with `c₁ = divCoeff > 0`
and `c₂ = divCoeff · |log topBandB|`, both explicit. -/
theorem periodQuad_ge_abs_log_top (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inTopBand b Λ E)
    (hnear : uRoot1 b Λ E - uRoot3 b Λ E ≤ Λ / 2)
    (hτ1 : E - sepEnergy b Λ ≤ 1) :
    divCoeff b Λ * |Real.log (E - sepEnergy b Λ)|
        - divCoeff b Λ * |Real.log (topBandB b Λ)|
      ≤ periodQuad b Λ E := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hτ : 0 < E - sepEnergy b Λ := by linarith [hband.1]
  have hA := divCoeff_pos b h12 h23 Λ hΛ
  have hB := topBandB_pos b h12 h23 Λ hΛ
  have hge := periodQuad_ge_log_top b h12 h23 Λ hΛ E hband hnear
  have hlogτ : Real.log (E - sepEnergy b Λ) ≤ 0 :=
    Real.log_nonpos hτ.le hτ1
  have hstep : divCoeff b Λ * (Real.log (topBandB b Λ)
        - Real.log (E - sepEnergy b Λ))
      ≤ periodQuad b Λ E := by
    calc divCoeff b Λ * (Real.log (topBandB b Λ)
          - Real.log (E - sepEnergy b Λ))
        = divCoeff b Λ
            * Real.log (topBandB b Λ / (E - sepEnergy b Λ)) := by
          rw [Real.log_div hB.ne' hτ.ne']
      _ ≤ divCoeff b Λ
            * Real.log (1 + topBandB b Λ / (E - sepEnergy b Λ)) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (div_pos hB hτ) (by
              have hpos := div_pos hB hτ; linarith)) hA.le
      _ ≤ periodQuad b Λ E := hge
  calc divCoeff b Λ * |Real.log (E - sepEnergy b Λ)|
        - divCoeff b Λ * |Real.log (topBandB b Λ)|
      = divCoeff b Λ * (|Real.log (E - sepEnergy b Λ)|
          - |Real.log (topBandB b Λ)|) := by ring
    _ ≤ divCoeff b Λ * (Real.log (topBandB b Λ)
          - Real.log (E - sepEnergy b Λ)) := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        rw [abs_of_nonpos hlogτ]
        have h2 : -|Real.log (topBandB b Λ)|
            ≤ Real.log (topBandB b Λ) := neg_abs_le _
        linarith
    _ ≤ periodQuad b Λ E := hstep

/-- **Divergence, memo form, bottom band.** With
`τ = E_sep − E ∈ (0, 1]` and the roots gap `≤ Λ/2`:
`periodQuad b Λ E ≥ divCoeff · |log τ| − divCoeff · |log botBandB|`. -/
theorem periodQuad_ge_abs_log_bot (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) (E : ℝ)
    (hband : inBotBand b Λ E)
    (hnear : uRoot3 b Λ E - uRoot1 b Λ E ≤ Λ / 2)
    (hτ1 : sepEnergy b Λ - E ≤ 1) :
    divCoeff b Λ * |Real.log (sepEnergy b Λ - E)|
        - divCoeff b Λ * |Real.log (botBandB b Λ)|
      ≤ periodQuad b Λ E := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hτ : 0 < sepEnergy b Λ - E := by linarith [hband.2]
  have hA := divCoeff_pos b h12 h23 Λ hΛ
  have hB := botBandB_pos b h12 h23 Λ hΛ
  have hge := periodQuad_ge_log_bot b h12 h23 Λ hΛ E hband hnear
  have hlogτ : Real.log (sepEnergy b Λ - E) ≤ 0 :=
    Real.log_nonpos hτ.le hτ1
  have hstep : divCoeff b Λ * (Real.log (botBandB b Λ)
        - Real.log (sepEnergy b Λ - E))
      ≤ periodQuad b Λ E := by
    calc divCoeff b Λ * (Real.log (botBandB b Λ)
          - Real.log (sepEnergy b Λ - E))
        = divCoeff b Λ
            * Real.log (botBandB b Λ / (sepEnergy b Λ - E)) := by
          rw [Real.log_div hB.ne' hτ.ne']
      _ ≤ divCoeff b Λ
            * Real.log (1 + botBandB b Λ / (sepEnergy b Λ - E)) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (div_pos hB hτ) (by
              have hpos := div_pos hB hτ; linarith)) hA.le
      _ ≤ periodQuad b Λ E := hge
  calc divCoeff b Λ * |Real.log (sepEnergy b Λ - E)|
        - divCoeff b Λ * |Real.log (botBandB b Λ)|
      = divCoeff b Λ * (|Real.log (sepEnergy b Λ - E)|
          - |Real.log (botBandB b Λ)|) := by ring
    _ ≤ divCoeff b Λ * (Real.log (botBandB b Λ)
          - Real.log (sepEnergy b Λ - E)) := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        rw [abs_of_nonpos hlogτ]
        have h2 : -|Real.log (botBandB b Λ)|
            ≤ Real.log (botBandB b Λ) := neg_abs_le _
        linarith
    _ ≤ periodQuad b Λ E := hstep

/-! ## The divergence headline: `Tendsto atTop` from either side -/

/-- **Divergence headline, from above.** As `E → E_sep` within
the right side, the quadrature period tends to `+∞`. The minorant
is `divCoeff · log (topBandB/(E − E_sep))`, eventually below
`periodQuad` by `periodQuad_ge_log_top` (the band and the
nearness hold in a right-neighborhood of `E_sep`). -/
theorem periodQuad_tendsto_atTop_top (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (periodQuad b Λ)
      (𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ)) atTop := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hA := divCoeff_pos b h12 h23 Λ hΛ
  have hB := topBandB_pos b h12 h23 Λ hΛ
  have hK : 0 < b.I1 * b.I2 / (b.I2 - b.I1) :=
    div_pos (mul_pos b.I1_pos b.I2_pos) (sub_pos.mpr h12)
  have hs1 := slope1_pos b h12 h23
  have hφ : Tendsto (fun E => divCoeff b Λ *
        Real.log (topBandB b Λ / (E - sepEnergy b Λ)))
      (𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ)) atTop := by
    have hsub : Tendsto (fun E => E - sepEnergy b Λ)
        (𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Continuous (fun E : ℝ => E - sepEnergy b Λ) :=
          continuous_id.sub continuous_const
        have h := hc.tendsto (sepEnergy b Λ)
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with E hE
        exact Set.mem_Ioi.mpr (sub_pos.mpr hE)
    have hinv : Tendsto (fun E => (E - sepEnergy b Λ)⁻¹)
        (𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsub
    have hdiv : Tendsto (fun E => topBandB b Λ / (E - sepEnergy b Λ))
        (𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ)) atTop := by
      simpa only [div_eq_mul_inv] using
        Tendsto.const_mul_atTop hB hinv
    have hlog := Real.tendsto_log_atTop.comp hdiv
    exact Tendsto.const_mul_atTop hA hlog
  have hmono : (fun E => divCoeff b Λ *
        Real.log (topBandB b Λ / (E - sepEnergy b Λ)))
      ≤ᶠ[𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ)] periodQuad b Λ := by
    have hε : 0 < Λ * slope1 b / (4 * (b.I1 * b.I2 / (b.I2 - b.I1))) :=
      div_pos (mul_pos hΛ hs1) (mul_pos (by norm_num) hK)
    have hlev : sepEnergy b Λ < levelEnergy b Λ 0 := by
      rw [sepEnergy_eq_levelEnergy_one]
      exact (levelEnergy_order b h12 h23 Λ hΛ).2
    have hEv2 : ∀ᶠ E in 𝓝[Set.Ioi (sepEnergy b Λ)] (sepEnergy b Λ),
        E < levelEnergy b Λ 0 :=
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hlev)
    filter_upwards [Ioc_mem_nhdsGT (show sepEnergy b Λ
        < sepEnergy b Λ
          + Λ * slope1 b / (4 * (b.I1 * b.I2 / (b.I2 - b.I1)))
        by linarith),
      hEv2] with E hE1 hE2
    have hband : inTopBand b Λ E := by
      constructor
      · rw [← hsep2]; linarith [hE1.1]
      · have h2 := two_mul_levelEnergy b Λ 0
          (by simp only [momInertia_zero]; exact b.I1_pos.ne')
        simp only [momInertia_zero] at h2
        linarith [hE2]
    have hid2 : slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E)
        = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * (E - sepEnergy b Λ)) := by
      rw [slope1_mul_root_diff b h12 h23 Λ E]
      congr 1
      rw [← hsep2]; ring
    have hgid : uRoot1 b Λ E - uRoot3 b Λ E
        = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * (E - sepEnergy b Λ))
          / slope1 b := by
      rw [eq_div_iff hs1.ne', mul_comm]; exact hid2
    have hnear : uRoot1 b Λ E - uRoot3 b Λ E ≤ Λ / 2 := by
      rw [hgid, div_le_iff₀ hs1]
      have hτle : E - sepEnergy b Λ
          ≤ Λ * slope1 b / (4 * (b.I1 * b.I2 / (b.I2 - b.I1))) := by
        linarith [hE1.2]
      have hstep : (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * (E - sepEnergy b Λ))
          ≤ (b.I1 * b.I2 / (b.I2 - b.I1))
            * (2 * (Λ * slope1 b
              / (4 * (b.I1 * b.I2 / (b.I2 - b.I1))))) :=
        mul_le_mul_of_nonneg_left (by linarith) hK.le
      have heq : (b.I1 * b.I2 / (b.I2 - b.I1))
            * (2 * (Λ * slope1 b
              / (4 * (b.I1 * b.I2 / (b.I2 - b.I1)))))
          = Λ / 2 * slope1 b :=
        aux_mul_two_div Λ (slope1 b) _ hK.ne'
      linarith [hstep, heq]
    have hge := periodQuad_ge_log_top b h12 h23 Λ hΛ E hband hnear
    have hτ : 0 < E - sepEnergy b Λ := sub_pos.mpr hE1.1
    calc divCoeff b Λ * Real.log (topBandB b Λ / (E - sepEnergy b Λ))
        ≤ divCoeff b Λ
            * Real.log (1 + topBandB b Λ / (E - sepEnergy b Λ)) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (div_pos hB hτ) (by
              have hpos := div_pos hB hτ; linarith)) hA.le
      _ ≤ periodQuad b Λ E := hge
  exact tendsto_atTop_mono' _ hmono hφ

/-- **Divergence headline, from below.** As `E → E_sep` within
the left side, the quadrature period tends to `+∞`. -/
theorem periodQuad_tendsto_atTop_bot (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (periodQuad b Λ)
      (𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ)) atTop := by
  have hsep2 := two_mul_sepEnergy b Λ
  have hA := divCoeff_pos b h12 h23 Λ hΛ
  have hB := botBandB_pos b h12 h23 Λ hΛ
  have hK : 0 < b.I2 * b.I3 / (b.I3 - b.I2) :=
    div_pos (mul_pos b.I2_pos b.I3_pos) (sub_pos.mpr h23)
  have hs3 := slope3_pos b h12 h23
  have hφ : Tendsto (fun E => divCoeff b Λ *
        Real.log (botBandB b Λ / (sepEnergy b Λ - E)))
      (𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ)) atTop := by
    have hsub : Tendsto (fun E => sepEnergy b Λ - E)
        (𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Continuous (fun E : ℝ => sepEnergy b Λ - E) :=
          continuous_const.sub continuous_id
        have h := hc.tendsto (sepEnergy b Λ)
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with E hE
        exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Iio.mp hE))
    have hinv : Tendsto (fun E => (sepEnergy b Λ - E)⁻¹)
        (𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsub
    have hdiv : Tendsto (fun E => botBandB b Λ / (sepEnergy b Λ - E))
        (𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ)) atTop := by
      simpa only [div_eq_mul_inv] using
        Tendsto.const_mul_atTop hB hinv
    have hlog := Real.tendsto_log_atTop.comp hdiv
    exact Tendsto.const_mul_atTop hA hlog
  have hmono : (fun E => divCoeff b Λ *
        Real.log (botBandB b Λ / (sepEnergy b Λ - E)))
      ≤ᶠ[𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ)] periodQuad b Λ := by
    have hε : 0 < Λ * slope3 b / (4 * (b.I2 * b.I3 / (b.I3 - b.I2))) :=
      div_pos (mul_pos hΛ hs3) (mul_pos (by norm_num) hK)
    have hlev : levelEnergy b Λ 2 < sepEnergy b Λ := by
      rw [sepEnergy_eq_levelEnergy_one]
      exact (levelEnergy_order b h12 h23 Λ hΛ).1
    have hEv2 : ∀ᶠ E in 𝓝[Set.Iio (sepEnergy b Λ)] (sepEnergy b Λ),
        levelEnergy b Λ 2 < E :=
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hlev)
    filter_upwards [Ioc_mem_nhdsLT (show sepEnergy b Λ
          - Λ * slope3 b / (4 * (b.I2 * b.I3 / (b.I3 - b.I2)))
        < sepEnergy b Λ by linarith),
      hEv2, self_mem_nhdsWithin]
      with E hE1 hE2 hE3
    have hband : inBotBand b Λ E := by
      constructor
      · have h2 := two_mul_levelEnergy b Λ 2
          (by simp only [momInertia_two]; exact b.I3_pos.ne')
        simp only [momInertia_two] at h2
        linarith [hE2]
      · rw [← hsep2]
        have hlt : E < sepEnergy b Λ := hE3
        linarith
    have hid2 : slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E)
        = (b.I2 * b.I3 / (b.I3 - b.I2)) * (2 * (sepEnergy b Λ - E)) := by
      rw [slope3_mul_root_diff b h12 h23 Λ E]
      congr 1
      rw [← hsep2]; ring
    have hgid : uRoot3 b Λ E - uRoot1 b Λ E
        = (b.I2 * b.I3 / (b.I3 - b.I2)) * (2 * (sepEnergy b Λ - E))
          / slope3 b := by
      rw [eq_div_iff hs3.ne', mul_comm]; exact hid2
    have hnear : uRoot3 b Λ E - uRoot1 b Λ E ≤ Λ / 2 := by
      rw [hgid, div_le_iff₀ hs3]
      have hτle : sepEnergy b Λ - E
          ≤ Λ * slope3 b / (4 * (b.I2 * b.I3 / (b.I3 - b.I2))) := by
        linarith [hE1.1]
      have hstep : (b.I2 * b.I3 / (b.I3 - b.I2))
            * (2 * (sepEnergy b Λ - E))
          ≤ (b.I2 * b.I3 / (b.I3 - b.I2))
            * (2 * (Λ * slope3 b
              / (4 * (b.I2 * b.I3 / (b.I3 - b.I2))))) :=
        mul_le_mul_of_nonneg_left (by linarith) hK.le
      have heq : (b.I2 * b.I3 / (b.I3 - b.I2))
            * (2 * (Λ * slope3 b
              / (4 * (b.I2 * b.I3 / (b.I3 - b.I2)))))
          = Λ / 2 * slope3 b :=
        aux_mul_two_div Λ (slope3 b) _ hK.ne'
      linarith [hstep, heq]
    have hge := periodQuad_ge_log_bot b h12 h23 Λ hΛ E hband hnear
    have hτ : 0 < sepEnergy b Λ - E := sub_pos.mpr hE3
    calc divCoeff b Λ * Real.log (botBandB b Λ / (sepEnergy b Λ - E))
        ≤ divCoeff b Λ
            * Real.log (1 + botBandB b Λ / (sepEnergy b Λ - E)) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (div_pos hB hτ) (by
              have hpos := div_pos hB hτ; linarith)) hA.le
      _ ≤ periodQuad b Λ E := hge
  exact tendsto_atTop_mono' _ hmono hφ

end ThetLogos
