import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import ThetLogos.SolidBody
import ThetLogos.SolidBodyPeriod

/-!
# ThetLogos.SolidBodyMinAxis — the minimum-axis mirror seat and its divergence

Brick 4 of the variable-intermediate-axis program (scoping memo
`varaxis-scoping-2026-10-26.md` §A1, which names this brick: "A
min-axis analogue would diverge as `I₂ ↓ I₁`, but the foundation
has not yet built that linearization"), built on the `SolidBody`
foundation and mirroring Brick 1 (`SolidBodyPeriod`, the maximum
axis). Abstract body only.

## ⚠ Formula correction, registered on the face

The brick brief proposed the rate
`Ω·√(((I₂−I₁)(I₃−I₁))/(I₁·I₃))` — denominator `I₁·I₃`. **That
formula is wrong.** Deriving from the foundation's `eulerRHS`
(cyclic convention), linearized about `ω = (Ω, 0, 0)` — spin about
axis 0, the minimum axis — with `x = δω₁`, `y = δω₂`:

  `x' = a·y`, `a = ((I₃−I₁)/I₂)·Ω > 0`,
  `y' = b·x`, `b = ((I₁−I₂)/I₃)·Ω < 0`,

so `a·b < 0` (the min seat is oscillatory, as classical theory
says) and the true rate is

  `ν_min = Ω·√(((I₂−I₁)(I₃−I₁))/(I₂·I₃))`,

denominator `I₂·I₃` — the product of the two NON-spin moments,
matching both landed seats (max seat: spin `I₃`, `stableRate`
denominator `I₁·I₂`; intermediate seat: spin `I₂`, `growthRate`
denominator `I₁·I₃`). The brief's `I₁·I₃` is the intermediate
seat's denominator carried over by mistake. Numeric check at
`(I₁,I₂,I₃,Ω) = (1,2,3,1)`: `a = 1`, `b = −1/3`, so `ν = √(1/3)`;
the corrected formula gives `√((1·2)/(2·3)) = √(1/3)` ✓, the
brief's gives `√(2/3)` ✗. This module registers the corrected rate.

## What is proved (T1, from the foundation's definitions)

Fix a body with `I₁ < I₂ < I₃` and spin `Ω > 0` about the minimum
axis (axis 0, moment `I₁`).

1. The exhibited transverse modes `x(t) = sin (ν_min t)`,
   `y(t) = (ν_min/a)·cos (ν_min t)` solve the linearized system
   `x' = a·y`, `y' = b·x`, are bounded, and are both periodic
   with the linearized period `P_min = 2π / ν_min`.
2. Fixing `I₁, I₃, Ω` and letting the middle moment descend to
   the minimum moment (`s ↓ I₁`, bodies `(I₁, s, I₃)`),
   `P_min(s) → ∞` along `𝓝[>] I₁`, at the inverse-square-root
   rate in the closing gap `s − I₁`:
   `P_min(s) · √(s − I₁)` tends to the named constant
   `2π / (Ω · √((I₃ − I₁)/(I₁·I₃)))`.

## Fences, on its face

* Linearized level only; nothing about the full nonlinear period.
* This is the mirror of Brick 1: divergence as the **middle moment
  approaches the minimum moment**, for spin linearized about the
  minimum axis. Together Bricks 1 and 4 cover both neighbors.
* Minimality of the period `P_min` is not asserted (not registered
  in the scoping memo).
* **NO CLAIM.** Classical mechanics (T4 core) at T1 formalization.
  Parts of the Clay Yang–Mills statement closed by this module: 0.
-/

namespace ThetLogos

open Filter Topology
open scoped Real

/-! ## The minimum-axis seat, fixed body -/

/-- Linearized coefficient `x' = minCoeffA · y` for a spin about
the minimum axis: `a = ((I₃−I₁)/I₂)·Ω`. -/
noncomputable def minCoeffA (b : SolidBody) (Ω : ℝ) : ℝ := ((b.I3 - b.I1) / b.I2) * Ω

/-- Linearized coefficient `y' = minCoeffB · x` for a spin about
the minimum axis: `b = ((I₁−I₂)/I₃)·Ω`. -/
noncomputable def minCoeffB (b : SolidBody) (Ω : ℝ) : ℝ := ((b.I1 - b.I2) / b.I3) * Ω

/-- The oscillation frequency of the minimum-axis seat,
`ν_min = Ω·√(((I₂−I₁)(I₃−I₁))/(I₂·I₃))` — the CORRECTED formula
(see the module header): the denominator is the product of the
two non-spin moments, `I₂·I₃`. -/
noncomputable def minRate (b : SolidBody) (Ω : ℝ) : ℝ :=
  Ω * Real.sqrt (((b.I2 - b.I1) * (b.I3 - b.I1)) / (b.I2 * b.I3))

/-- Amplitude coefficient of the min-axis mode's `y` component. -/
noncomputable def minCoeff (b : SolidBody) (Ω : ℝ) : ℝ :=
  minRate b Ω / minCoeffA b Ω

/-- Min-axis mode, `x` component (`δω₁`): `x(t) = sin (ν_min t)`. -/
noncomputable def modeXm (b : SolidBody) (Ω : ℝ) (t : ℝ) : ℝ :=
  Real.sin (minRate b Ω * t)

/-- Min-axis mode, `y` component (`δω₂`):
`y(t) = minCoeff · cos (ν_min t)`. -/
noncomputable def modeYm (b : SolidBody) (Ω : ℝ) (t : ℝ) : ℝ :=
  minCoeff b Ω * Real.cos (minRate b Ω * t)

theorem minCoeffA_ne_zero (b : SolidBody) (Ω : ℝ) (h13 : b.I1 < b.I3)
    (hΩ : 0 < Ω) : minCoeffA b Ω ≠ 0 := by
  unfold minCoeffA
  apply mul_ne_zero _ hΩ.ne'
  apply div_ne_zero _ b.I2_pos.ne'
  exact sub_ne_zero.mpr h13.ne'

theorem minRate_pos (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) : 0 < minRate b Ω := by
  unfold minRate
  exact mul_pos hΩ (Real.sqrt_pos.mpr
    (div_pos (mul_pos (sub_pos.mpr h12) (sub_pos.mpr (lt_trans h12 h23)))
      (mul_pos b.I2_pos b.I3_pos)))

/-- The defining identity of the min-axis frequency:
`ν_min² = −(a·b)` — the product `a·b` is negative (oscillatory),
the mirror of `stableRate_sq` at the maximum axis. -/
theorem minRate_sq (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) :
    minRate b Ω ^ 2 = -(minCoeffA b Ω * minCoeffB b Ω) := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have hfrac : (0 : ℝ) ≤ ((b.I2 - b.I1) * (b.I3 - b.I1)) / (b.I2 * b.I3) :=
    le_of_lt (div_pos (mul_pos (sub_pos.mpr h12) (sub_pos.mpr (lt_trans h12 h23)))
      (mul_pos b.I2_pos b.I3_pos))
  unfold minRate minCoeffA minCoeffB
  rw [mul_pow, Real.sq_sqrt hfrac]
  field_simp
  ring

/-- The min-axis mode satisfies `x'(t) = a · y(t)`. -/
theorem modeXm_deriv (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) (t : ℝ) :
    deriv (modeXm b Ω) t = minCoeffA b Ω * modeYm b Ω t := by
  have hA : minCoeffA b Ω ≠ 0 := minCoeffA_ne_zero b Ω (lt_trans h12 h23) hΩ
  have hderiv : HasDerivAt (modeXm b Ω)
      (Real.cos (minRate b Ω * t) * minRate b Ω) t := by
    have h1 : HasDerivAt (fun s => minRate b Ω * s) (minRate b Ω) t := by
      simpa using (hasDerivAt_id' t).const_mul (minRate b Ω)
    have h2 := (Real.hasDerivAt_sin (minRate b Ω * t)).comp t h1
    have hfun : modeXm b Ω = (fun s => Real.sin (minRate b Ω * s)) := by
      funext s
      rfl
    rw [hfun]
    exact h2
  rw [hderiv.deriv]
  have hfunY : modeYm b Ω t
      = (minRate b Ω / minCoeffA b Ω) * Real.cos (minRate b Ω * t) := rfl
  rw [hfunY]
  field_simp

/-- The min-axis mode satisfies `y'(t) = b · x(t)`. The coefficient
works because `minCoeff · ν_min = ν_min²/a = −b`, using
`ν_min² = −a·b`. -/
theorem modeYm_deriv (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) (t : ℝ) :
    deriv (modeYm b Ω) t = minCoeffB b Ω * modeXm b Ω t := by
  have hA : minCoeffA b Ω ≠ 0 := minCoeffA_ne_zero b Ω (lt_trans h12 h23) hΩ
  have hcoeff : minCoeff b Ω * minRate b Ω = -(minCoeffB b Ω) := by
    have hsq := minRate_sq b Ω h12 h23
    have hfrac : minCoeff b Ω * minRate b Ω
        = (minRate b Ω ^ 2) / minCoeffA b Ω := by
      unfold minCoeff
      field_simp
    rw [hfrac, hsq, neg_div, mul_div_cancel_left₀ _ hA]
  have hderiv : HasDerivAt (modeYm b Ω)
      (minCoeff b Ω * (-Real.sin (minRate b Ω * t) * minRate b Ω)) t := by
    have h1 : HasDerivAt (fun s => minRate b Ω * s) (minRate b Ω) t := by
      simpa using (hasDerivAt_id' t).const_mul (minRate b Ω)
    have h2 := (Real.hasDerivAt_cos (minRate b Ω * t)).comp t h1
    have h3 := h2.const_mul (minCoeff b Ω)
    have hfun : modeYm b Ω
        = (fun s => minCoeff b Ω * Real.cos (minRate b Ω * s)) := by
      funext s
      rfl
    rw [hfun]
    exact h3
  rw [hderiv.deriv]
  have hfunX : modeXm b Ω t = Real.sin (minRate b Ω * t) := rfl
  rw [hfunX]
  calc minCoeff b Ω * (-Real.sin (minRate b Ω * t) * minRate b Ω)
      = -(minCoeff b Ω * minRate b Ω) * Real.sin (minRate b Ω * t) := by
        ring
    _ = minCoeffB b Ω * Real.sin (minRate b Ω * t) := by rw [hcoeff]; ring

/-- The min-axis mode is a bounded oscillation: `|x(t)| ≤ 1` for
all `t` — the minimum-axis seat does not run away. -/
theorem modeXm_bounded (b : SolidBody) (Ω : ℝ) (t : ℝ) :
    |modeXm b Ω t| ≤ 1 := by
  have hfun : modeXm b Ω t = Real.sin (minRate b Ω * t) := rfl
  rw [hfun]
  exact Real.abs_sin_le_one _

/-- The `y` component is bounded by its amplitude:
`|y(t)| ≤ |minCoeff|`. -/
theorem modeYm_bounded (b : SolidBody) (Ω : ℝ) (t : ℝ) :
    |modeYm b Ω t| ≤ |minCoeff b Ω| := by
  have hfun : modeYm b Ω t = minCoeff b Ω * Real.cos (minRate b Ω * t) := rfl
  rw [hfun, abs_mul]
  have h := Real.abs_cos_le_one (minRate b Ω * t)
  calc |minCoeff b Ω| * |Real.cos (minRate b Ω * t)|
      ≤ |minCoeff b Ω| * 1 :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |minCoeff b Ω| := mul_one _

/-! ## Periodicity of the exhibited min-axis modes -/

/-- The min-axis mode `x(t) = sin (ν_min t)` is periodic with
period `2π/ν_min`. -/
theorem modeXm_periodic (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) :
    Function.Periodic (modeXm b Ω) (2 * π / minRate b Ω) := by
  have hν : (0 : ℝ) < minRate b Ω := minRate_pos b Ω h12 h23 hΩ
  intro t
  have hstep : minRate b Ω * (t + 2 * π / minRate b Ω)
      = minRate b Ω * t + 2 * π := by
    field_simp
  show Real.sin (minRate b Ω * (t + 2 * π / minRate b Ω))
    = Real.sin (minRate b Ω * t)
  rw [hstep, Real.sin_add_two_pi]

/-- The min-axis mode `y(t) = (ν_min/a)·cos (ν_min t)` is periodic
with period `2π/ν_min` — the same period as the `x` mode. -/
theorem modeYm_periodic (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) :
    Function.Periodic (modeYm b Ω) (2 * π / minRate b Ω) := by
  have hν : (0 : ℝ) < minRate b Ω := minRate_pos b Ω h12 h23 hΩ
  intro t
  have hstep : minRate b Ω * (t + 2 * π / minRate b Ω)
      = minRate b Ω * t + 2 * π := by
    field_simp
  show minCoeff b Ω * Real.cos (minRate b Ω * (t + 2 * π / minRate b Ω))
    = minCoeff b Ω * Real.cos (minRate b Ω * t)
  rw [hstep, Real.cos_add_two_pi]

/-! ## The variable body: the period diverges as `s ↓ I₁` -/

/-- The min-axis rate of the variable body `(I₁, s, I₃)`, as a
bare formula in `s`:
`ν_min(s) = Ω·√(((s − I₁)·(I₃ − I₁))/(s·I₃))`. -/
noncomputable def minRateVar (I1 I3 Ω s : ℝ) : ℝ :=
  Ω * Real.sqrt (((s - I1) * (I3 - I1)) / (s * I3))

/-- The formula above is `minRate` of `varBody`. -/
theorem minRate_varBody (I1 s I3 Ω : ℝ) (hI1 : 0 < I1) (hs : 0 < s)
    (hI3 : 0 < I3) :
    minRate (varBody I1 s I3 hI1 hs hI3) Ω = minRateVar I1 I3 Ω s :=
  rfl

/-- The linearized period about the minimum axis for the variable
body: `Pmin(s) = 2π / ν_min(s)`. -/
noncomputable def Pmin (I1 I3 Ω s : ℝ) : ℝ :=
  2 * π / minRateVar I1 I3 Ω s

/-- `Pmin` is `2π / minRate b_s Ω` in the registered form. -/
theorem Pmin_eq (I1 s I3 Ω : ℝ) (hI1 : 0 < I1) (hs : 0 < s) (hI3 : 0 < I3) :
    Pmin I1 I3 Ω s
      = 2 * π / minRate (varBody I1 s I3 hI1 hs hI3) Ω := rfl

/-- For every `s ∈ (I₁, I₃)`, the exhibited min-axis `x` mode of
`b_s` is `Pmin`-periodic. -/
theorem modeXm_periodic_varBody (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) {s : ℝ} (hs1 : I1 < s) (hs3 : s < I3) :
    Function.Periodic
      (modeXm (varBody I1 s I3 hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)) Ω)
      (Pmin I1 I3 Ω s) := by
  rw [Pmin_eq I1 s I3 Ω hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)]
  exact modeXm_periodic _ Ω hs1 hs3 hΩ

/-- For every `s ∈ (I₁, I₃)`, the exhibited min-axis `y` mode of
`b_s` is `Pmin`-periodic. -/
theorem modeYm_periodic_varBody (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) {s : ℝ} (hs1 : I1 < s) (hs3 : s < I3) :
    Function.Periodic
      (modeYm (varBody I1 s I3 hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)) Ω)
      (Pmin I1 I3 Ω s) := by
  rw [Pmin_eq I1 s I3 Ω hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)]
  exact modeYm_periodic _ Ω hs1 hs3 hΩ

/-! ## The frequency tends to zero, from above -/

/-- The variable min-axis rate, as a function of `s`, is
continuous at the closing endpoint `s = I₁`. -/
theorem minRateVar_continuousAt (I1 I3 Ω : ℝ) (hI1 : 0 < I1)
    (h13 : I1 < I3) :
    ContinuousAt (minRateVar I1 I3 Ω) I1 := by
  have hI3 : (0 : ℝ) < I3 := lt_trans hI1 h13
  have hrad : ContinuousAt
      (fun s => ((s - I1) * (I3 - I1)) / (s * I3)) I1 := by
    refine ContinuousAt.div ?_ ?_ (mul_ne_zero hI1.ne' hI3.ne')
    · fun_prop
    · fun_prop
  have hsqrt : ContinuousAt
      (fun s => Real.sqrt (((s - I1) * (I3 - I1)) / (s * I3))) I1 :=
    Real.continuous_sqrt.continuousAt.comp hrad
  exact hsqrt.const_mul Ω

/-- Along `s ↓ I₁`, the variable min-axis rate tends to `0`
through positive values: `Tendsto ν_min (𝓝[>] I₁) (𝓝[>] 0)`. -/
theorem minRateVar_tendsto_nhdsGT (I1 I3 Ω : ℝ) (hI1 : 0 < I1)
    (h13 : I1 < I3) (hΩ : 0 < Ω) :
    Tendsto (minRateVar I1 I3 Ω) (𝓝[>] I1) (𝓝[>] 0) := by
  have hval : minRateVar I1 I3 Ω I1 = 0 := by
    unfold minRateVar
    simp
  have h𝓝 : Tendsto (minRateVar I1 I3 Ω) (𝓝[>] I1) (𝓝 0) := by
    have h := (minRateVar_continuousAt I1 I3 Ω hI1 h13).tendsto
    rw [hval] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ s in 𝓝[>] I1,
      minRateVar I1 I3 Ω s ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT h13] with s hs
    rw [Set.mem_Ioi]
    unfold minRateVar
    refine mul_pos hΩ (Real.sqrt_pos.mpr (div_pos ?_ ?_))
    · exact mul_pos (sub_pos.mpr hs.1) (sub_pos.mpr h13)
    · exact mul_pos (lt_trans hI1 hs.1) (lt_trans hI1 h13)
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h𝓝, hpos⟩

/-! ## Divergence of the linearized period -/

/-- **The linearized min-axis period diverges.** As the middle
moment closes down to the minimum moment, `Pmin(s) → ∞`. -/
theorem Pmin_tendsto_atTop (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) :
    Tendsto (Pmin I1 I3 Ω) (𝓝[>] I1) atTop := by
  have hinv := (minRateVar_tendsto_nhdsGT I1 I3 Ω hI1 h13 hΩ).inv_tendsto_nhdsGT_zero
  have hmul := hinv.const_mul_atTop (show (0 : ℝ) < 2 * π by positivity)
  refine hmul.congr (fun s => ?_)
  show 2 * π * (minRateVar I1 I3 Ω s)⁻¹ = Pmin I1 I3 Ω s
  unfold Pmin
  rw [div_eq_mul_inv]

/-- **The inverse-square-root rate, with its named constant:**
`Pmin(s) · √(s − I₁) → 2π / (Ω·√((I₃ − I₁)/(I₁·I₃)))` as
`s ↓ I₁`. Equivalently `Pmin(s) ~ C / √(s − I₁)` with `C` that
constant — the period blows up exactly like one over the square
root of the closing gap, mirroring Brick 1's rate at the other
neighbor. -/
theorem Pmin_mul_sqrt_tendsto (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) :
    Tendsto (fun s => Pmin I1 I3 Ω s * Real.sqrt (s - I1)) (𝓝[>] I1)
      (𝓝 (2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * I3))))) := by
  have hI3 : (0 : ℝ) < I3 := lt_trans hI1 h13
  -- The comparison function `g`, continuous at `I₁`.
  have hinner : ContinuousAt (fun s => (I3 - I1) / (s * I3)) I1 := by
    refine ContinuousAt.div continuousAt_const ?_ (mul_ne_zero hI1.ne' hI3.ne')
    · fun_prop
  have hsqrt : ContinuousAt (fun s => Real.sqrt ((I3 - I1) / (s * I3))) I1 :=
    Real.continuous_sqrt.continuousAt.comp hinner
  have hne : Ω * Real.sqrt ((I3 - I1) / (I1 * I3)) ≠ 0 :=
    mul_ne_zero hΩ.ne'
      (Real.sqrt_pos.mpr (div_pos (sub_pos.mpr h13) (mul_pos hI1 hI3))).ne'
  have hg : ContinuousAt
      (fun s => 2 * π / (Ω * Real.sqrt ((I3 - I1) / (s * I3)))) I1 :=
    ContinuousAt.div continuousAt_const (hsqrt.const_mul Ω) hne
  have hgT : Tendsto (fun s => 2 * π / (Ω * Real.sqrt ((I3 - I1) / (s * I3))))
      (𝓝[>] I1)
      (𝓝 (2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * I3))))) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  -- `Pmin s · √(s − I₁)` agrees with `g` on `Ioo I1 I3`.
  have heq : (fun s => 2 * π / (Ω * Real.sqrt ((I3 - I1) / (s * I3))))
      =ᶠ[𝓝[>] I1] (fun s => Pmin I1 I3 Ω s * Real.sqrt (s - I1)) := by
    filter_upwards [Ioo_mem_nhdsGT h13] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hI1 hs.1
    have hI3pos : (0 : ℝ) < I3 := hI3
    have hsI1 : (0 : ℝ) < s - I1 := sub_pos.mpr hs.1
    have hsq1 : (0 : ℝ) < Real.sqrt (s - I1) := Real.sqrt_pos.mpr hsI1
    have hrest : (0 : ℝ) < Real.sqrt ((I3 - I1) / (s * I3)) :=
      Real.sqrt_pos.mpr (div_pos (sub_pos.mpr h13) (mul_pos hs0 hI3pos))
    have hsplit : Real.sqrt (((s - I1) * (I3 - I1)) / (s * I3))
        = Real.sqrt (s - I1) * Real.sqrt ((I3 - I1) / (s * I3)) := by
      have h1 : ((s - I1) * (I3 - I1)) / (s * I3)
          = (s - I1) * ((I3 - I1) / (s * I3)) := by
        rw [mul_div_assoc]
      rw [h1, Real.sqrt_mul hsI1.le]
    show 2 * π / (Ω * Real.sqrt ((I3 - I1) / (s * I3)))
      = Pmin I1 I3 Ω s * Real.sqrt (s - I1)
    unfold Pmin minRateVar
    rw [hsplit]
    field_simp [hΩ.ne', hsq1.ne', hrest.ne']
  exact hgT.congr' heq

end ThetLogos
