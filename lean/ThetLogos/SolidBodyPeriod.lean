import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import ThetLogos.SolidBody

/-!
# ThetLogos.SolidBodyPeriod — the linearized stable period and its divergence

Brick 1 of the variable-intermediate-axis program (scoping memo
`varaxis-scoping-2026-10-26.md` §3; ledger item 9), built directly on
the `SolidBody` foundation. Abstract body only.

## What is proved (T1, from the foundation's definitions)

Fix `0 < I₁ < I₃` and `Ω > 0`. For `s ∈ (I₁, I₃)`, let `b_s` be the
solid body with principal moments `(I₁, s, I₃)` — spin `Ω` is then
about the maximum axis (moment `I₃`), the stable seat of the
foundation, with oscillation frequency `stableRate b_s Ω`. Define
the **linearized period**

  `Pmax(s) = 2π / stableRate b_s Ω`.

1. Both exhibited stable modes are periodic with this period:
   `Function.Periodic (modeXs b_s Ω) (Pmax s)` and
   `Function.Periodic (modeYs b_s Ω) (Pmax s)`.
2. As the middle moment closes up to the maximum moment,
   `Pmax(s) → ∞` along `s ↑ I₃`
   (`Filter.Tendsto (Pmax I₁ I₃ Ω) (𝓝[<] I₃) Filter.atTop`),
   at the inverse-square-root rate in the closing gap `I₃ − s`:
   `Pmax(s) · √(I₃ − s)` tends to the named constant
   `2π / (Ω · √((I₃ − I₁)/(I₁·I₃)))`.

## Fences, on its face

* This is divergence as the **middle moment approaches the maximum
  moment**, for spin linearized about the maximum axis. It is not an
  "approach either neighbor" statement, and it asserts nothing about
  the full nonlinear period.
* About the intermediate axis the foundation gives a growth rate
  `γ`, hence an e-folding **timescale** `1/γ`. A timescale is not a
  period, and nothing here calls it one.
* Minimality of the period `Pmax` is not asserted in this brick
  (it was not registered in the scoping memo).
* **NO CLAIM.** This is classical mechanics (T4 core) at T1
  formalization. Parts of the Clay Yang–Mills statement closed by
  this module: 0.
-/

namespace ThetLogos

open Filter Topology
open scoped Real

/-- The variable body: principal moments `(I₁, s, I₃)`. -/
def varBody (I1 s I3 : ℝ) (hI1 : 0 < I1) (hs : 0 < s) (hI3 : 0 < I3) :
    SolidBody where
  I1 := I1
  I2 := s
  I3 := I3
  I1_pos := hI1
  I2_pos := hs
  I3_pos := hI3

@[simp] lemma varBody_I1 (I1 s I3 : ℝ) (hI1 : 0 < I1) (hs : 0 < s)
    (hI3 : 0 < I3) : (varBody I1 s I3 hI1 hs hI3).I1 = I1 := rfl

@[simp] lemma varBody_I2 (I1 s I3 : ℝ) (hI1 : 0 < I1) (hs : 0 < s)
    (hI3 : 0 < I3) : (varBody I1 s I3 hI1 hs hI3).I2 = s := rfl

@[simp] lemma varBody_I3 (I1 s I3 : ℝ) (hI1 : 0 < I1) (hs : 0 < s)
    (hI3 : 0 < I3) : (varBody I1 s I3 hI1 hs hI3).I3 = I3 := rfl

/-- The stable rate of the variable body, as a bare formula in `s`:
`ν(s) = Ω·√(((I₃ − s)·(I₃ − I₁))/(I₁·s))`. -/
noncomputable def stableRateVar (I1 I3 Ω s : ℝ) : ℝ :=
  Ω * Real.sqrt (((I3 - s) * (I3 - I1)) / (I1 * s))

/-- The formula above is the foundation's `stableRate` of `varBody`. -/
theorem stableRate_varBody (I1 s I3 Ω : ℝ) (hI1 : 0 < I1) (hs : 0 < s)
    (hI3 : 0 < I3) :
    stableRate (varBody I1 s I3 hI1 hs hI3) Ω = stableRateVar I1 I3 Ω s :=
  rfl

/-- The linearized period about the maximum axis for the variable
body: `Pmax(s) = 2π / ν(s)`. -/
noncomputable def Pmax (I1 I3 Ω s : ℝ) : ℝ :=
  2 * π / stableRateVar I1 I3 Ω s

/-- `Pmax` is `2π / stableRate b_s Ω` in the memo's own form. -/
theorem Pmax_eq (I1 s I3 Ω : ℝ) (hI1 : 0 < I1) (hs : 0 < s) (hI3 : 0 < I3) :
    Pmax I1 I3 Ω s
      = 2 * π / stableRate (varBody I1 s I3 hI1 hs hI3) Ω := rfl

/-! ## Periodicity of the exhibited stable modes -/

/-- The stable mode `x(t) = sin (νt)` is periodic with period
`2π/ν`. -/
theorem modeXs_periodic (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) :
    Function.Periodic (modeXs b Ω) (2 * π / stableRate b Ω) := by
  have hν : (0 : ℝ) < stableRate b Ω := stableRate_pos b Ω h12 h23 hΩ
  intro t
  have hstep : stableRate b Ω * (t + 2 * π / stableRate b Ω)
      = stableRate b Ω * t + 2 * π := by
    field_simp
  show Real.sin (stableRate b Ω * (t + 2 * π / stableRate b Ω))
    = Real.sin (stableRate b Ω * t)
  rw [hstep, Real.sin_add_two_pi]

/-- The stable mode `y(t) = (ν/a)·cos (νt)` is periodic with period
`2π/ν` — the same period as the `x` mode: `stableRate` is their
common angular frequency. -/
theorem modeYs_periodic (b : SolidBody) (Ω : ℝ) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (hΩ : 0 < Ω) :
    Function.Periodic (modeYs b Ω) (2 * π / stableRate b Ω) := by
  have hν : (0 : ℝ) < stableRate b Ω := stableRate_pos b Ω h12 h23 hΩ
  intro t
  have hstep : stableRate b Ω * (t + 2 * π / stableRate b Ω)
      = stableRate b Ω * t + 2 * π := by
    field_simp
  show stabCoeff b Ω * Real.cos (stableRate b Ω * (t + 2 * π / stableRate b Ω))
    = stabCoeff b Ω * Real.cos (stableRate b Ω * t)
  rw [hstep, Real.cos_add_two_pi]

/-- Memo statement 1, `x` mode: for every `s ∈ (I₁, I₃)`, the
exhibited stable `x` mode of `b_s` is `Pmax`-periodic. -/
theorem modeXs_periodic_varBody (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) {s : ℝ} (hs1 : I1 < s) (hs3 : s < I3) :
    Function.Periodic
      (modeXs (varBody I1 s I3 hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)) Ω)
      (Pmax I1 I3 Ω s) := by
  rw [Pmax_eq I1 s I3 Ω hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)]
  exact modeXs_periodic _ Ω hs1 hs3 hΩ

/-- Memo statement 1, `y` mode: for every `s ∈ (I₁, I₃)`, the
exhibited stable `y` mode of `b_s` is `Pmax`-periodic. -/
theorem modeYs_periodic_varBody (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) {s : ℝ} (hs1 : I1 < s) (hs3 : s < I3) :
    Function.Periodic
      (modeYs (varBody I1 s I3 hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)) Ω)
      (Pmax I1 I3 Ω s) := by
  rw [Pmax_eq I1 s I3 Ω hI1 (lt_trans hI1 hs1) (lt_trans hI1 h13)]
  exact modeYs_periodic _ Ω hs1 hs3 hΩ

/-! ## The frequency tends to zero, from above -/

/-- The variable stable rate, as a function of `s`, is continuous
at the closing endpoint `s = I₃`. -/
theorem stableRateVar_continuousAt (I1 I3 Ω : ℝ) (hI1 : 0 < I1)
    (h13 : I1 < I3) :
    ContinuousAt (stableRateVar I1 I3 Ω) I3 := by
  have hI3 : (0 : ℝ) < I3 := lt_trans hI1 h13
  have hrad : ContinuousAt
      (fun s => ((I3 - s) * (I3 - I1)) / (I1 * s)) I3 := by
    refine ContinuousAt.div ?_ ?_ (mul_ne_zero hI1.ne' hI3.ne')
    · fun_prop
    · fun_prop
  have hsqrt : ContinuousAt
      (fun s => Real.sqrt (((I3 - s) * (I3 - I1)) / (I1 * s))) I3 :=
    Real.continuous_sqrt.continuousAt.comp hrad
  exact hsqrt.const_mul Ω

/-- Along `s ↑ I₃`, the variable stable rate tends to `0` through
positive values: `Tendsto ν (𝓝[<] I₃) (𝓝[>] 0)`. -/
theorem stableRateVar_tendsto_nhdsGT (I1 I3 Ω : ℝ) (hI1 : 0 < I1)
    (h13 : I1 < I3) (hΩ : 0 < Ω) :
    Tendsto (stableRateVar I1 I3 Ω) (𝓝[<] I3) (𝓝[>] 0) := by
  have hval : stableRateVar I1 I3 Ω I3 = 0 := by
    unfold stableRateVar
    simp
  have h𝓝 : Tendsto (stableRateVar I1 I3 Ω) (𝓝[<] I3) (𝓝 0) := by
    have h := (stableRateVar_continuousAt I1 I3 Ω hI1 h13).tendsto
    rw [hval] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ s in 𝓝[<] I3,
      stableRateVar I1 I3 Ω s ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsLT h13] with s hs
    rw [Set.mem_Ioi]
    unfold stableRateVar
    refine mul_pos hΩ (Real.sqrt_pos.mpr (div_pos ?_ ?_))
    · exact mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr h13)
    · exact mul_pos hI1 (lt_trans hI1 hs.1)
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h𝓝, hpos⟩

/-! ## Divergence of the linearized period -/

/-- **Memo statement 2: the linearized period diverges.** As the
middle moment closes up to the maximum moment, `Pmax(s) → ∞`. -/
theorem Pmax_tendsto_atTop (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) :
    Tendsto (Pmax I1 I3 Ω) (𝓝[<] I3) atTop := by
  have hinv := (stableRateVar_tendsto_nhdsGT I1 I3 Ω hI1 h13 hΩ).inv_tendsto_nhdsGT_zero
  have hmul := hinv.const_mul_atTop (show (0 : ℝ) < 2 * π by positivity)
  refine hmul.congr (fun s => ?_)
  show 2 * π * (stableRateVar I1 I3 Ω s)⁻¹ = Pmax I1 I3 Ω s
  unfold Pmax
  rw [div_eq_mul_inv]

/-- **The inverse-square-root rate, with its named constant:**
`Pmax(s) · √(I₃ − s) → 2π / (Ω·√((I₃ − I₁)/(I₁·I₃)))` as `s ↑ I₃`.
Equivalently `Pmax(s) ~ C / √(I₃ − s)` with `C` that constant — the
period blows up exactly like one over the square root of the
closing gap. -/
theorem Pmax_mul_sqrt_tendsto (I1 I3 Ω : ℝ) (hI1 : 0 < I1) (h13 : I1 < I3)
    (hΩ : 0 < Ω) :
    Tendsto (fun s => Pmax I1 I3 Ω s * Real.sqrt (I3 - s)) (𝓝[<] I3)
      (𝓝 (2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * I3))))) := by
  have hI3 : (0 : ℝ) < I3 := lt_trans hI1 h13
  -- The comparison function `g`, continuous at `I₃`.
  have hinner : ContinuousAt (fun s => (I3 - I1) / (I1 * s)) I3 := by
    refine ContinuousAt.div continuousAt_const ?_ (mul_ne_zero hI1.ne' hI3.ne')
    · fun_prop
  have hsqrt : ContinuousAt (fun s => Real.sqrt ((I3 - I1) / (I1 * s))) I3 :=
    Real.continuous_sqrt.continuousAt.comp hinner
  have hne : Ω * Real.sqrt ((I3 - I1) / (I1 * I3)) ≠ 0 :=
    mul_ne_zero hΩ.ne'
      (Real.sqrt_pos.mpr (div_pos (sub_pos.mpr h13) (mul_pos hI1 hI3))).ne'
  have hg : ContinuousAt
      (fun s => 2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * s)))) I3 :=
    ContinuousAt.div continuousAt_const (hsqrt.const_mul Ω) hne
  have hgT : Tendsto (fun s => 2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * s))))
      (𝓝[<] I3)
      (𝓝 (2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * I3))))) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  -- `Pmax s · √(I₃ − s)` agrees with `g` on `Ioo I1 I3`.
  have heq : (fun s => 2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * s))))
      =ᶠ[𝓝[<] I3] (fun s => Pmax I1 I3 Ω s * Real.sqrt (I3 - s)) := by
    filter_upwards [Ioo_mem_nhdsLT h13] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hI1 hs.1
    have hI3s : (0 : ℝ) < I3 - s := sub_pos.mpr hs.2
    have hsq3 : (0 : ℝ) < Real.sqrt (I3 - s) := Real.sqrt_pos.mpr hI3s
    have hrest : (0 : ℝ) < Real.sqrt ((I3 - I1) / (I1 * s)) :=
      Real.sqrt_pos.mpr (div_pos (sub_pos.mpr h13) (mul_pos hI1 hs0))
    have hsplit : Real.sqrt (((I3 - s) * (I3 - I1)) / (I1 * s))
        = Real.sqrt (I3 - s) * Real.sqrt ((I3 - I1) / (I1 * s)) := by
      have h1 : ((I3 - s) * (I3 - I1)) / (I1 * s)
          = (I3 - s) * ((I3 - I1) / (I1 * s)) := by
        rw [mul_div_assoc]
      rw [h1, Real.sqrt_mul hI3s.le]
    show 2 * π / (Ω * Real.sqrt ((I3 - I1) / (I1 * s)))
      = Pmax I1 I3 Ω s * Real.sqrt (I3 - s)
    unfold Pmax stableRateVar
    rw [hsplit]
    field_simp [hΩ.ne', hsq3.ne', hrest.ne']
  exact hgT.congr' heq

end ThetLogos
