import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

namespace ThetLogos

open MeasureTheory
open scoped ENNReal

/-!
# ThetLogos.BSDPeriod — the real period `Ω` of `E2`, as an exact in-tree real

Source: the BSD rung-2 scoping memo §2, brick **B2-3**
(`scoping-bsd-rung-2-2026-10-29.md`). Design authority: rung 1
(`ThetLogos.BSDRankPin`) and the refined pin (`ThetLogos.BSDRefinedPin`),
whose `BSDRefinedE2` is parameterized over the real this module supplies.

**What this file IS.** The real period of `E2 : y² = x³ − 2`. Since
`Δ(E2) = −1728 < 0`, the real locus has one component, and (both branches
of `|dx / 2y|` summed, per the 2026-10-27 study) the period is the
improper integral

  `Ω = ∫_{2^{1/3}}^∞ dx / √(x³ − 2)`,

formalized here as `periodE2`, the Bochner integral of
`(x³ − 2)^(−1/2)` over `Set.Ioi (2^{1/3})` against volume. This module
proves the integral is a well-defined **strictly positive** real:

- integrability at the left endpoint, where the integrand blows up like
  `(x − 2^{1/3})^{−1/2}` (comparison against the shifted power, via
  `x³ − 2 = (x − 2^{1/3}) · (x² + 2^{1/3} x + 2^{2/3}) ≥ 3·2^{2/3}·(x − 2^{1/3})`);
- integrability at `∞`, where the integrand is `O(x^{−3/2})`
  (comparison against `x^{−3/2}` once `x³ − 2 ≥ (3/4) x³`);
- strict positivity, from the integrand being positive on the whole
  domain (`setIntegral_pos_iff_support_of_nonneg_ae`).

The Ω **object** therefore lands in class **(a)** of the memo's
ingredient ledger: an exact in-tree real, defined by its integral, with
integrability and positivity proved — the memo's PARTIAL fallback
(a (c)-only parameter) does **not** fire.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the rank
  equality (rung 1's `BSDRankEquality`). The refined formula this brick
  serves is Wiles's Remark 1. Parts of the official BSD statement
  closed by this module: **0**. NO CLAIM.
- **Not the period's value.** No numeric value of `periodE2` is stated
  or proved here. Its value `Ω ≈ 2.163682` is a class-(c) numeric
  hypothesis owned by brick B2-5 (`E2PeriodValue` in
  `ThetLogos.BSDRefinedPin`, the interval `[2.1636817, 2.1636818]`),
  sourced to the 2026-10-27 study's quadrature / Beta-closed-form
  agreement. Nothing in this file quotes it.

Honesty tiers in this file:
- **T1 (proved):** everything below — the definition, integrability at
  both ends, and strict positivity, all with proof terms.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The endpoint `2^{1/3}` -/

/-- The real cube root of `2`, `2^{1/3}`: the unique real root of
`x³ = 2`, hence the left endpoint of the period integral (the real locus
of `E2` is `x ≥ 2^{1/3}`). -/
noncomputable def cubeRootTwo : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

theorem cubeRootTwo_pos : 0 < cubeRootTwo :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem cubeRootTwo_pow_three : cubeRootTwo ^ 3 = 2 := by
  have h : cubeRootTwo ^ (3 : ℝ) = 2 := by
    show ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = 2
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (1 : ℝ) / 3 * 3 = 1 by norm_num, Real.rpow_one]
  rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h

theorem cubeRootTwo_gt_one : 1 < cubeRootTwo := by
  by_contra hlt
  have h : cubeRootTwo ≤ 1 := le_of_not_gt hlt
  have h3 : cubeRootTwo ^ 3 ≤ (1 : ℝ) ^ 3 :=
    pow_le_pow_left₀ cubeRootTwo_pos.le h 3
  rw [cubeRootTwo_pow_three] at h3
  norm_num at h3

/-- The factorization behind both the positivity and the endpoint
comparison: `x³ − 2 = (x − 2^{1/3}) · (x² + 2^{1/3} x + 2^{2/3})`. -/
theorem cube_sub_two_factor (x : ℝ) :
    x ^ 3 - 2 = (x - cubeRootTwo) * (x ^ 2 + cubeRootTwo * x + cubeRootTwo ^ 2) := by
  rw [← cubeRootTwo_pow_three]; ring

theorem cube_sub_two_pos {x : ℝ} (hx : cubeRootTwo < x) : 0 < x ^ 3 - 2 := by
  have hfac : (0 : ℝ) < x ^ 2 + cubeRootTwo * x + cubeRootTwo ^ 2 :=
    add_pos (add_pos (pow_pos (cubeRootTwo_pos.trans hx) 2)
      (mul_pos cubeRootTwo_pos (cubeRootTwo_pos.trans hx)))
      (pow_pos cubeRootTwo_pos 2)
  rw [cube_sub_two_factor]
  exact mul_pos (sub_pos.mpr hx) hfac

/-! ## The integrand and the period -/

/-- The period integrand `x ↦ (x³ − 2)^{−1/2} = 1 / √(x³ − 2)`, as a real
function via `Real.rpow`. On `x > 2^{1/3}` the base is positive, so this
is the genuine reciprocal square root there. -/
noncomputable def periodIntegrand (x : ℝ) : ℝ := (x ^ 3 - 2) ^ (-1 / 2 : ℝ)

/-- **The real period of `E2`** (brick B2-3): the improper integral
`Ω = ∫_{2^{1/3}}^∞ dx / √(x³ − 2)`, as a Bochner integral over
`Set.Ioi (2^{1/3})` against volume. An exact in-tree real — class (a)
as an object; its *value* is class (c) and is stated nowhere here
(it is B2-5's `E2PeriodValue`). -/
noncomputable def periodE2 : ℝ :=
  ∫ x in Set.Ioi cubeRootTwo, periodIntegrand x

theorem periodIntegrand_pos {x : ℝ} (hx : cubeRootTwo < x) :
    0 < periodIntegrand x :=
  Real.rpow_pos_of_pos (cube_sub_two_pos hx) _

theorem periodIntegrand_continuousOn_Ioi :
    ContinuousOn periodIntegrand (Set.Ioi cubeRootTwo) := by
  show ContinuousOn (fun x => (x ^ 3 - 2) ^ (-1 / 2 : ℝ)) (Set.Ioi cubeRootTwo)
  apply ContinuousOn.rpow_const
  · exact (continuousOn_id.pow 3).sub continuousOn_const
  · intro x hx
    exact Or.inl (ne_of_gt (cube_sub_two_pos hx))

/-! ## Integrability at the left endpoint

On `Ioo (2^{1/3}) (2^{1/3} + 1)` the factorization gives
`x³ − 2 ≥ (x − 2^{1/3}) · 3·2^{2/3}`, so the integrand is dominated by
`(3·2^{2/3})^{−1/2} · (x − 2^{1/3})^{−1/2}`, the shifted `−1/2` power,
which is integrable at the endpoint (`intervalIntegrable_rpow'`
transported by `IntervalIntegrable.comp_sub_right`). -/

theorem periodIntegrand_integrableOn_endpoint :
    IntegrableOn periodIntegrand (Set.Ioo cubeRootTwo (cubeRootTwo + 1)) volume := by
  have hbound : IntegrableOn (fun x => (x - cubeRootTwo) ^ (-1 / 2 : ℝ))
      (Set.Ioo cubeRootTwo (cubeRootTwo + 1)) volume := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (show (-1 : ℝ) < -1 / 2 by norm_num)).comp_sub_right cubeRootTwo
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
      (show (0 : ℝ) + cubeRootTwo ≤ 1 + cubeRootTwo by linarith)] at h
    simpa only [zero_add, add_comm (1 : ℝ) cubeRootTwo] using h
  refine Integrable.mono' (hbound.const_mul ((3 * cubeRootTwo ^ 2) ^ (-1 / 2 : ℝ)))
    ((periodIntegrand_continuousOn_Ioi.mono Set.Ioo_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  obtain ⟨hx1, -⟩ := hx
  have hpos : 0 < x ^ 3 - 2 := cube_sub_two_pos hx1
  have ha2 : (0 : ℝ) < cubeRootTwo ^ 2 := pow_pos cubeRootTwo_pos 2
  have hfac : 3 * cubeRootTwo ^ 2 ≤ x ^ 2 + cubeRootTwo * x + cubeRootTwo ^ 2 := by
    have e1 : cubeRootTwo ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ cubeRootTwo_pos.le hx1.le 2
    have e2 : cubeRootTwo * cubeRootTwo ≤ cubeRootTwo * x :=
      mul_le_mul_of_nonneg_left hx1.le cubeRootTwo_pos.le
    have e3 : cubeRootTwo * cubeRootTwo = cubeRootTwo ^ 2 := (pow_two cubeRootTwo).symm
    linarith
  have hprod : (x - cubeRootTwo) * (3 * cubeRootTwo ^ 2) ≤ x ^ 3 - 2 := by
    rw [cube_sub_two_factor]
    exact mul_le_mul_of_nonneg_left hfac (sub_nonneg.mpr hx1.le)
  have hanti : (x ^ 3 - 2) ^ (-1 / 2 : ℝ)
      ≤ ((x - cubeRootTwo) * (3 * cubeRootTwo ^ 2)) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos
      (mul_pos (sub_pos.mpr hx1) (by linarith)) hprod (by norm_num)
  rw [Real.mul_rpow (sub_nonneg.mpr hx1.le) (by linarith)] at hanti
  calc ‖periodIntegrand x‖ = (x ^ 3 - 2) ^ (-1 / 2 : ℝ) := by
        show ‖(x ^ 3 - 2) ^ (-1 / 2 : ℝ)‖ = (x ^ 3 - 2) ^ (-1 / 2 : ℝ)
        rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    _ ≤ (3 * cubeRootTwo ^ 2) ^ (-1 / 2 : ℝ) * (x - cubeRootTwo) ^ (-1 / 2 : ℝ) := by
        rw [mul_comm]; exact hanti

/-! ## Integrability at `∞`

On `Ici (2^{1/3} + 1)` we have `x ≥ 2`, hence `x³ − 2 ≥ (3/4) x³`, so the
integrand is dominated by `(3/4)^{−1/2} · x^{−3/2}`, integrable at `∞`
by `integrableOn_Ioi_rpow_of_lt`. -/

theorem periodIntegrand_integrableOn_tail :
    IntegrableOn periodIntegrand (Set.Ici (cubeRootTwo + 1)) volume := by
  have hbound : IntegrableOn (fun x => x ^ (-3 / 2 : ℝ))
      (Set.Ici (cubeRootTwo + 1)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (show (-3 / 2 : ℝ) < -1 by norm_num)
        (show (0 : ℝ) < cubeRootTwo + 1 by linarith [cubeRootTwo_pos]))
  refine Integrable.mono' (hbound.const_mul ((3 / 4 : ℝ) ^ (-1 / 2 : ℝ)))
    ((periodIntegrand_continuousOn_Ioi.mono
      (fun x hx => show cubeRootTwo < x from
        lt_of_lt_of_le (by linarith : cubeRootTwo < cubeRootTwo + 1) hx)).aestronglyMeasurable
      measurableSet_Ici) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have h1 : cubeRootTwo + 1 ≤ x := hx
  have hax : cubeRootTwo < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith [cubeRootTwo_gt_one]
  have hx3 : (8 : ℝ) ≤ x ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx2 3
    norm_num at this ⊢; linarith
  have hpos : 0 < x ^ 3 - 2 := cube_sub_two_pos hax
  have hprod : (3 / 4 : ℝ) * x ^ 3 ≤ x ^ 3 - 2 := by linarith
  have hanti : (x ^ 3 - 2) ^ (-1 / 2 : ℝ) ≤ ((3 / 4 : ℝ) * x ^ 3) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hprod (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hanti
  have hpow : (x ^ 3) ^ (-1 / 2 : ℝ) = x ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast x 3, ← Real.rpow_mul (by linarith)]
    congr 1
    norm_num
  rw [hpow] at hanti
  calc ‖periodIntegrand x‖ = (x ^ 3 - 2) ^ (-1 / 2 : ℝ) := by
        show ‖(x ^ 3 - 2) ^ (-1 / 2 : ℝ)‖ = (x ^ 3 - 2) ^ (-1 / 2 : ℝ)
        rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    _ ≤ (3 / 4 : ℝ) ^ (-1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ) := hanti

/-! ## The period is a well-defined positive real -/

/-- The period integrand is integrable on the whole domain
`Ioi (2^{1/3})`: the endpoint piece and the tail piece glued along
`Ioo (2^{1/3}) (2^{1/3} + 1) ∪ Ici (2^{1/3} + 1) = Ioi (2^{1/3})`. -/
theorem periodIntegrand_integrableOn :
    IntegrableOn periodIntegrand (Set.Ioi cubeRootTwo) volume := by
  have h := periodIntegrand_integrableOn_endpoint.union periodIntegrand_integrableOn_tail
  rwa [Set.Ioo_union_Ici_eq_Ioi (show cubeRootTwo < cubeRootTwo + 1 by linarith)] at h

/-- **Strict positivity of the period.** The integrand is positive at
every point of the domain, so its support meets `Ioi (2^{1/3})` in a set
of infinite (hence positive) volume, and the integral is strictly
positive. Together with `periodIntegrand_integrableOn`, this says
`periodE2` is a well-defined positive real — the Ω object lands in
class (a). No numeric value is stated. -/
theorem periodE2_pos : 0 < periodE2 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi cubeRootTwo)] periodIntegrand := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (periodIntegrand_pos hx).le
  show 0 < ∫ x in Set.Ioi cubeRootTwo, periodIntegrand x
  refine (setIntegral_pos_iff_support_of_nonneg_ae hnonneg
    periodIntegrand_integrableOn).mpr ?_
  have hsupp : Set.Ioi cubeRootTwo
      ⊆ Function.support periodIntegrand ∩ Set.Ioi cubeRootTwo := by
    intro x hx
    exact ⟨Function.mem_support.mpr (ne_of_gt (periodIntegrand_pos hx)), hx⟩
  calc (0 : ℝ≥0∞) < volume (Set.Ioi cubeRootTwo) := by simp [Real.volume_Ioi]
    _ ≤ volume (Function.support periodIntegrand ∩ Set.Ioi cubeRootTwo) :=
        measure_mono hsupp

end ThetLogos
