import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import ThetLogos.MassShellMeasure

namespace ThetLogos

open MeasureTheory Filter
open scoped ENNReal

/-!
# ThetLogos.TranslationContinuity — strong continuity of translations

Discharges the *translation half* of the exact price quoted in
`MassShellMeasure.lean` for `StrongContinuity_window`: for `ψ ∈ L²` of the
mass shell, `a ↦ U₁(a, 1)ψ` is continuous at `a = 0` in `eLpNorm`, where
`U₁(a, 1)ψ = e^{ia·p}ψ` (the shell action of `(a, 1)` is trivial).

**What IS proved here (T1, zero sorrys):**
- `translation_diff` — pointwise, the translation difference is
  `(phase a p - 1) * ψ p`;
- `strongContinuity_window_proved` — `StrongContinuity_window` itself, by
  one application of dominated convergence
  (`tendsto_lintegral_filter_of_dominated_convergence'`) to
  `F a p = ‖(phase a p - 1) * ψ p‖ₑ ^ 2`, dominated by the `L¹` function
  `4‖ψ‖ₑ²`, with pointwise convergence from `Complex.continuous_exp`;
  the final `eLpNorm` is the square root of that integral.

**Fences.** Translations ONLY: strong continuity of the Lorentz/rotation
part of the one-particle representation is a separate, later line item
and is not attempted here. No Fock-space packaging (`Γ(U₁)`) is attempted.
No interacting or continuum statement is made or implied.
-/

/-- Pointwise, the translation difference is a phase factor times `ψ`:
    for the group element `⟨a, 1⟩` the shell action is the identity
    (`shellActR_one`), so `U₁(a,1)ψ(p) - ψ(p) = (e^{ia·p} - 1) ψ(p)`. -/
theorem translation_diff (m : ℝ) (hm : 0 < m) (a : Minkowski)
    (ψ : massShell m → ℂ) (p : massShell m) :
    oneParticleFun ⟨a, 1⟩ m hm ψ p - ψ p = (phase a p - 1) * ψ p := by
  have hinv : (⟨a, 1⟩ : RPoincare).lor⁻¹ = 1 := inv_one
  have h1 : shellActR (⟨a, 1⟩ : RPoincare).lor⁻¹ m hm p = p := by
    rw [hinv]
    exact congrFun (shellActR_one m hm) p
  have htrans : (⟨a, 1⟩ : RPoincare).trans = a := rfl
  unfold oneParticleFun
  rw [htrans, h1]
  ring

/-- The translation difference function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_translation_diff (m : ℝ) (hm : 0 < m)
    (a : Minkowski) (ψ : massShell m → ℂ)
    (hψ : MemLp ψ 2 (massShellMeasure m hm)) :
    AEStronglyMeasurable (fun p => (phase a p - 1) * ψ p)
      (massShellMeasure m hm) := by
  have hphase : AEStronglyMeasurable (fun p => phase a p) (massShellMeasure m hm) :=
    (measurable_phase a m).aestronglyMeasurable
  have hsub : AEStronglyMeasurable (fun p => phase a p - 1) (massShellMeasure m hm) := by
    have hconst : AEStronglyMeasurable (fun _ : massShell m => (1 : ℂ))
        (massShellMeasure m hm) := aestronglyMeasurable_const
    have h := hphase.sub hconst
    simpa only [Pi.sub_def] using h
  have h := hsub.mul hψ.aestronglyMeasurable
  simpa only [Pi.mul_def] using h

/-- A complex number of norm `1` has enorm `1`. -/
theorem enorm_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ‖z‖ₑ = 1 := by
  have hz' : ‖z‖₊ = 1 :=
    NNReal.coe_inj.mp (by rw [coe_nnnorm, hz, NNReal.coe_one])
  rw [enorm_eq_nnnorm, hz', ENNReal.coe_one]

/-- The phase factor moves by at most `2` in enorm: `‖e^{ia·p} - 1‖ₑ ≤ 2`,
    from `‖e^{ia·p}‖ = 1` and the triangle inequality. -/
theorem enorm_phase_sub_one_le (m : ℝ) (a : Minkowski) (p : massShell m) :
    ‖phase a p - 1‖ₑ ≤ 2 := by
  have e1 : ‖phase a p‖ₑ = 1 := enorm_eq_one_of_norm_eq_one (phase_norm a p)
  have e2 : ‖(1 : ℂ)‖ₑ = 1 := enorm_eq_one_of_norm_eq_one norm_one
  calc ‖phase a p - 1‖ₑ = ‖phase a p + (-1)‖ₑ := by rw [sub_eq_add_neg]
    _ ≤ ‖phase a p‖ₑ + ‖(-1 : ℂ)‖ₑ := enorm_add_le _ _
    _ = 2 := by rw [enorm_neg, e1, e2]; norm_num

/-- The DCT integrand is dominated by `4‖ψ‖ₑ²`, for every `a` and `p`. -/
theorem translation_integrand_le (m : ℝ) (a : Minkowski)
    (ψ : massShell m → ℂ) (p : massShell m) :
    ‖(phase a p - 1) * ψ p‖ₑ ^ (2 : ℝ) ≤ 4 * ‖ψ p‖ₑ ^ (2 : ℝ) := by
  have hle : ‖(phase a p - 1) * ψ p‖ₑ ≤ 2 * ‖ψ p‖ₑ := by
    rw [enorm_mul]
    exact mul_le_mul_of_nonneg_right (enorm_phase_sub_one_le m a p) zero_le
  calc ‖(phase a p - 1) * ψ p‖ₑ ^ (2 : ℝ)
      ≤ (2 * ‖ψ p‖ₑ) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = 4 * ‖ψ p‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
        norm_num

/-- For an a.e. strongly measurable `f`, the DCT integrand `‖f‖ₑ²` is
    a.e. measurable. -/
theorem aemeasurable_enorm_rpow (m : ℝ) (hm : 0 < m) (f : massShell m → ℂ)
    (hf : AEStronglyMeasurable f (massShellMeasure m hm)) :
    AEMeasurable (fun p => ‖f p‖ₑ ^ (2 : ℝ)) (massShellMeasure m hm) := by
  have h1 : AEMeasurable (fun p => ‖f p‖ₑ) (massShellMeasure m hm) :=
    hf.aemeasurable.enorm
  have h2 : Measurable (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable
  have h := h2.comp_aemeasurable h1
  simpa only [Function.comp_def] using h

/-- The dominator `4‖ψ‖ₑ²` has finite integral: its integral is `4` times
    `∫⁻ ‖ψ‖ₑ²`, and the latter is finite since `eLpNorm ψ 2 μ < ∞` —
    the `eLpNorm` is the square root of that integral. -/
theorem lintegral_translation_bound_ne_top (m : ℝ) (hm : 0 < m)
    (ψ : massShell m → ℂ) (hψ : MemLp ψ 2 (massShellMeasure m hm)) :
    ∫⁻ p, (4 * ‖ψ p‖ₑ ^ (2 : ℝ)) ∂(massShellMeasure m hm) ≠ ⊤ := by
  have hJ : ∫⁻ p, ‖ψ p‖ₑ ^ (2 : ℝ) ∂(massShellMeasure m hm) ≠ ⊤ := by
    by_contra hJ
    have hfin : eLpNorm ψ 2 (massShellMeasure m hm) < ⊤ := hψ
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hψ.aestronglyMeasurable
    rw [ENNReal.toReal_ofNat, hJ,
      ENNReal.top_rpow_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)] at heq
    exact hfin.ne heq
  rw [lintegral_const_mul'' _
    (aemeasurable_enorm_rpow m hm ψ hψ.aestronglyMeasurable)]
  exact ENNReal.mul_ne_top (by norm_num) hJ

/-- Pointwise convergence of the DCT integrand: for fixed `p`,
    `‖(e^{ia·p} - 1)ψ(p)‖ₑ² → 0` as `a → 0`, from continuity of the
    Minkowski form in `a` and of `Complex.exp`. -/
theorem tendsto_translation_integrand (m : ℝ) (ψ : massShell m → ℂ)
    (p : massShell m) :
    Tendsto (fun a : Minkowski => ‖(phase a p - 1) * ψ p‖ₑ ^ (2 : ℝ))
      (nhds 0) (nhds 0) := by
  have hinner : Tendsto (fun a : Minkowski => minkowskiInner a p.val)
      (nhds 0) (nhds 0) := by
    have hcont : Continuous fun a : Minkowski => minkowskiInner a p.val := by
      unfold minkowskiInner
      fun_prop
    have h0 : minkowskiInner (0 : Minkowski) p.val = 0 := by
      simp [minkowskiInner]
    have h := hcont.tendsto (0 : Minkowski)
    rwa [h0] at h
  have hphase : Tendsto (fun a : Minkowski => phase a p) (nhds 0) (nhds 1) := by
    have hof : Tendsto (fun a : Minkowski => (minkowskiInner a p.val : ℂ))
        (nhds 0) (nhds 0) := by
      have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hinner
      simpa [Function.comp_def] using h
    have h2 : Tendsto
        (fun a : Minkowski => Complex.I * (minkowskiInner a p.val : ℂ))
        (nhds 0) (nhds 0) := by
      have h : Tendsto
          (fun a : Minkowski => Complex.I * (minkowskiInner a p.val : ℂ))
          (nhds 0) (nhds (Complex.I * 0)) := tendsto_const_nhds.mul hof
      simpa using h
    have h3 := (Complex.continuous_exp.tendsto (0 : ℂ)).comp h2
    unfold phase
    simpa [Function.comp_def] using h3
  have hdiff : Tendsto (fun a : Minkowski => (phase a p - 1) * ψ p)
      (nhds 0) (nhds 0) := by
    have h := (hphase.sub_const (1 : ℂ)).mul_const (ψ p)
    simpa using h
  have henorm : Tendsto (fun a : Minkowski => ‖(phase a p - 1) * ψ p‖ₑ)
      (nhds 0) (nhds 0) := by
    have h := (continuous_enorm.tendsto (0 : ℂ)).comp hdiff
    simpa [Function.comp_def] using h
  have h := henorm.ennrpow_const (2 : ℝ)
  rwa [ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 2 by norm_num)] at h

/-- The dominated convergence step: the integral of the squared
    translation difference tends to `0` as `a → 0`. -/
theorem lintegral_translation_tendsto_zero (m : ℝ) (hm : 0 < m)
    (ψ : massShell m → ℂ) (hψ : MemLp ψ 2 (massShellMeasure m hm)) :
    Tendsto (fun a : Minkowski =>
      ∫⁻ p, ‖(phase a p - 1) * ψ p‖ₑ ^ (2 : ℝ) ∂(massShellMeasure m hm))
      (nhds 0) (nhds 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := massShellMeasure m hm) (l := nhds (0 : Minkowski))
    (F := fun a p => ‖(phase a p - 1) * ψ p‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
    (bound := fun p => 4 * ‖ψ p‖ₑ ^ (2 : ℝ))
    (Filter.Eventually.of_forall fun a =>
      aemeasurable_enorm_rpow m hm _
        (aestronglyMeasurable_translation_diff m hm a ψ hψ))
    (Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun p =>
      translation_integrand_le m a ψ p)
    (lintegral_translation_bound_ne_top m hm ψ hψ)
    (Filter.Eventually.of_forall fun p => tendsto_translation_integrand m ψ p)
  simpa using h

/-- **T1:** `StrongContinuity_window`, translation half discharged.
    For every `ψ ∈ L²` of the mass shell, `a ↦ ‖U₁(a, 1)ψ - ψ‖₂ → 0` as
    `a → 0`: the `eLpNorm` is the square root of the dominated integral
    of `lintegral_translation_tendsto_zero`. -/
theorem strongContinuity_window_proved (m : ℝ) (hm : 0 < m) :
    StrongContinuity_window m hm := by
  intro ψ hψ
  have hfun : (fun a : Minkowski =>
        eLpNorm (fun p => oneParticleFun ⟨a, 1⟩ m hm ψ p - ψ p) 2
          (massShellMeasure m hm))
      = (fun a : Minkowski =>
          (∫⁻ p, ‖(phase a p - 1) * ψ p‖ₑ ^ (2 : ℝ)
            ∂(massShellMeasure m hm)) ^ (1 / 2 : ℝ)) := by
    funext a
    have hpt : (fun p => oneParticleFun ⟨a, 1⟩ m hm ψ p - ψ p)
        = (fun p => (phase a p - 1) * ψ p) := by
      funext p
      exact translation_diff m hm a ψ p
    rw [hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      (aestronglyMeasurable_translation_diff m hm a ψ hψ),
      ENNReal.toReal_ofNat]
  rw [hfun]
  have h := (lintegral_translation_tendsto_zero m hm ψ hψ).ennrpow_const
    (1 / 2 : ℝ)
  rwa [ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)] at h

end ThetLogos
