import ThetLogos.IntegralKernelHS
import Mathlib.Tactic

open Filter Topology ComplexInnerProductSpace MeasureTheory
open scoped ENNReal NNReal

namespace ThetLogos

/-!
# Integral-kernel Schur / product theorems - SHELF-3b

General-API stock, built under the SHELF fill commission
(pack: `routeb-general-scratch/pack-shelf-3b.md`, brick
SHELF-3b; consumes the landed SHELF-3a-ii module
`IntegralKernelHS.lean`: `integralKernelOp`,
`integralKernelOp_inner`,
`integralKernelOp_inner_iterated`).

## The fence this brick addresses

`Span3FactLayerKernelPos.lean`'s header records: "the Schur
product step exists in the corpus only as the finite-matrix
`Matrix.PosSemidef.hadamard` (`PlaquetteFactorPD`,
`ThermalPreCompensation`). There is **no landed
integral-kernel Schur/product theorem** composing the two
`A`-pairings into positivity of the `K`-bar pairing, and no
landed statement of that composition." The shelf map's note
binds: filling SHELF-3b retires the fence, not the weld -
the weld brick itself additionally needs the
`reflSite_eq_torusShift_zero` duplicate resolved upstream
and is separately priced when queued. This module does NOT
attempt the weld, does NOT touch the duplicate, and edits
no landed file. OUTCOME OF THIS BRICK: the fence retires
only in part - items (1), (2), (4) below are landed, and
item (3), the Schur product step itself, is named OPEN at
the pack's pre-named seam (see item (3)); the fence's Schur
clause therefore stands.

## Contents (pack SHELF-3b items (1)-(4))

1. `PosKernel` (registration, stated here on the face):
   positivity is registered at the OPERATOR level, in the
   shape the weld consumes - a kernel `K : α × α → ℂ` with
   `hK : MemLp K 2 (μ.prod μ)` is positive iff its induced
   operator pairing is nonnegative:
   `∀ f : Lp ℂ 2 μ, 0 ≤ (inner ℂ f (integralKernelOp hK f)).re`.
   This operator-level meaning is the registered one; no
   finite-sample definition is registered.
2. Gram / factorization positivity: a kernel admitting a
   factorization `K x y = ∫ t, F x t * conj (F y t)` against
   a third measure space is a `PosKernel` - its quadratic
   form is the integral of a squared norm.
3. Schur product (integral Hadamard): the pointwise product
   of two positive integral kernels is positive. - NOT
   LANDED, named OPEN at the pack's pre-named seam: the
   statement does not typecheck at this generality, because
   the pointwise product of two `L2` kernels need not be
   `L2` (counterexample shape: `K (x, y) = g x * g y` with
   `g` in `L2` but not in `L4` is a positive `L2` kernel
   whose pointwise square is not `MemLp 2`), and a general
   `PosKernel` admits no Gram factorization (the square
   root of a positive Hilbert-Schmidt operator need not be
   Hilbert-Schmidt), so the item-(2) route cannot close it
   either. No finite-dimensional or seat-shaped version is
   landed under this headline.
4. Composition form: the composed operator of two kernel
   operators is induced by the composed kernel
   `(x, z) ↦ ∫ y, K₁ (x, y) * K₂ (y, z)`, with the
   adjoint-composition positivity corollary.

## Fences

General measure spaces / L2 throughout (as in SHELF-3a-ii);
no specialization to the `A`-pairing / `osSpace` seat is
made or wanted (the weld is a different brick). NO CLAIM;
dials 0/4; nothing here touches `LayerKernelPos`, clause
(a), or the `A ⪰ 0` core.
-/

section PosKernelDef

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- **Item (1) - `PosKernel`, the registered definition.**
A kernel `K : α × α → ℂ` (with its L2 hypothesis `hK`) is
positive iff the pairing induced by its integral-kernel
operator `integralKernelOp hK` (SHELF-3a-ii) is nonnegative
on every `f : Lp ℂ 2 μ`:
`0 ≤ (inner ℂ f (integralKernelOp hK f)).re`.
This operator-level form is the registered meaning of
kernel positivity in this module. -/
def PosKernel (K : α × α → ℂ) (hK : MemLp K 2 (μ.prod μ)) : Prop :=
  ∀ f : Lp ℂ 2 μ, 0 ≤ (inner ℂ f (integralKernelOp hK f)).re

/-- The zero kernel is positive: its operator is zero, by
the form identity of SHELF-3a-ii applied against an
arbitrary test vector. -/
theorem posKernel_zero :
    PosKernel (0 : α × α → ℂ)
      (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ)) := by
  intro f
  have hT : integralKernelOp
      (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ)) f = 0 := by
    have h := integralKernelOp_inner
      (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ))
      (integralKernelOp
        (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ)) f) f
    simp only [Pi.zero_apply, zero_mul, mul_zero, integral_zero] at h
    have hnorm : ‖integralKernelOp
        (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ)) f‖ = 0 := by
      have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (integralKernelOp
        (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ)) f)
      rw [h] at h2
      have h3 : (‖integralKernelOp
          (MemLp.zero : MemLp (0 : α × α → ℂ) 2 (μ.prod μ)) f‖ : ℂ) = 0 :=
        sq_eq_zero_iff.mp h2.symm
      exact_mod_cast h3
    exact norm_eq_zero.mp hnorm
  rw [hT]
  simp

end PosKernelDef

section QuasiMeasurePreservingExtractions

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] {μα : Measure α} {μβ : Measure β} {μγ : Measure γ}
  [SFinite μα] [SFinite μβ] [SFinite μγ]

/-- The extraction `(p, t) ↦ (p.1, t)` is quasi-measure-preserving
from `(μα.prod μβ).prod μγ` to `μα.prod μγ`: its pushforward is
the scalar multiple `μβ univ • (μα.prod μγ)`-shaped measure,
which has the same null sets. This is the measurability input
for triple-space integrands coupling the first and third
variables. -/
theorem quasiMeasurePreserving_fst_snd :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun q : (α × β) × γ => (q.1.1, q.2))
      ((μα.prod μβ).prod μγ) (μα.prod μγ) := by
  refine ⟨measurable_fst.fst.prodMk measurable_snd,
    MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  have hmeas : Measurable (fun q : (α × β) × γ => (q.1.1, q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hpre : MeasurableSet
      ((fun q : (α × β) × γ => (q.1.1, q.2)) ⁻¹' s) := hmeas hs
  have hsec : ∀ x : α, ∀ y : β, Prod.mk (x, y) ⁻¹'
        ((fun q : (α × β) × γ => (q.1.1, q.2)) ⁻¹' s)
      = Prod.mk x ⁻¹' s := fun x y => rfl
  have hlint : ∫⁻ x, μγ (Prod.mk x ⁻¹' s) ∂μα = 0 := by
    rw [← Measure.prod_apply hs]
    exact h2s
  have hgz : (fun x => μγ (Prod.mk x ⁻¹' s)) =ᵐ[μα] 0 :=
    (lintegral_eq_zero_iff'
      (measurable_measure_prodMk_left hs).aemeasurable).mp hlint
  rw [Measure.map_apply hmeas hs, Measure.prod_apply hpre,
    MeasureTheory.lintegral_prod _
      (measurable_measure_prodMk_left hpre).aemeasurable]
  have hinner : ∀ x : α, (∫⁻ y, μγ (Prod.mk (x, y) ⁻¹'
        ((fun q : (α × β) × γ => (q.1.1, q.2)) ⁻¹' s)) ∂μβ)
      = μγ (Prod.mk x ⁻¹' s) * μβ Set.univ := by
    intro x
    rw [lintegral_congr_ae (ae_of_all _ fun y => by rw [hsec x y])]
    exact MeasureTheory.lintegral_const _
  rw [lintegral_congr_ae (ae_of_all _ hinner)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hgz] with x hx
  rw [hx, Pi.zero_apply, zero_mul]

/-- The extraction `(p, t) ↦ (p.2, t)` is quasi-measure-preserving
from `(μα.prod μβ).prod μγ` to `μβ.prod μγ`. -/
theorem quasiMeasurePreserving_snd_snd :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun q : (α × β) × γ => (q.1.2, q.2))
      ((μα.prod μβ).prod μγ) (μβ.prod μγ) := by
  refine ⟨measurable_fst.snd.prodMk measurable_snd,
    MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  have hmeas : Measurable (fun q : (α × β) × γ => (q.1.2, q.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hpre : MeasurableSet
      ((fun q : (α × β) × γ => (q.1.2, q.2)) ⁻¹' s) := hmeas hs
  have hsec : ∀ x : α, ∀ y : β, Prod.mk (x, y) ⁻¹'
        ((fun q : (α × β) × γ => (q.1.2, q.2)) ⁻¹' s)
      = Prod.mk y ⁻¹' s := fun x y => rfl
  have hlint : ∫⁻ y, μγ (Prod.mk y ⁻¹' s) ∂μβ = 0 := by
    rw [← Measure.prod_apply hs]
    exact h2s
  have hgz : (fun y => μγ (Prod.mk y ⁻¹' s)) =ᵐ[μβ] 0 :=
    (lintegral_eq_zero_iff'
      (measurable_measure_prodMk_left hs).aemeasurable).mp hlint
  rw [Measure.map_apply hmeas hs, Measure.prod_apply hpre,
    MeasureTheory.lintegral_prod_symm _
      (measurable_measure_prodMk_left hpre).aemeasurable]
  have hinner : ∀ y : β, (∫⁻ x, μγ (Prod.mk (x, y) ⁻¹'
        ((fun q : (α × β) × γ => (q.1.2, q.2)) ⁻¹' s)) ∂μα)
      = μγ (Prod.mk y ⁻¹' s) * μα Set.univ := by
    intro y
    rw [lintegral_congr_ae (ae_of_all _ fun x => by rw [hsec x y])]
    exact MeasureTheory.lintegral_const _
  rw [lintegral_congr_ae (ae_of_all _ hinner)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hgz] with y hy
  rw [hy, Pi.zero_apply, zero_mul]

/-- The extraction `(p, t) ↦ (t, p.2)` is quasi-measure-preserving
from `(μα.prod μβ).prod μγ` to `μγ.prod μβ`. -/
theorem quasiMeasurePreserving_snd_fst :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun q : (α × β) × γ => (q.2, q.1.2))
      ((μα.prod μβ).prod μγ) (μγ.prod μβ) := by
  refine ⟨measurable_snd.prodMk measurable_fst.snd,
    MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  have hmeas : Measurable (fun q : (α × β) × γ => (q.2, q.1.2)) :=
    measurable_snd.prodMk measurable_fst.snd
  have hpre : MeasurableSet
      ((fun q : (α × β) × γ => (q.2, q.1.2)) ⁻¹' s) := hmeas hs
  have hsec : ∀ x : α, ∀ z : β, Prod.mk (x, z) ⁻¹'
        ((fun q : (α × β) × γ => (q.2, q.1.2)) ⁻¹' s)
      = (fun t => (t, z)) ⁻¹' s := fun x z => rfl
  have hlint : ∫⁻ z, μγ ((fun t => (t, z)) ⁻¹' s) ∂μβ = 0 := by
    rw [← Measure.prod_apply_symm hs]
    exact h2s
  have hgz : (fun z => μγ ((fun t => (t, z)) ⁻¹' s)) =ᵐ[μβ] 0 :=
    (lintegral_eq_zero_iff'
      (measurable_measure_prodMk_right hs).aemeasurable).mp hlint
  rw [Measure.map_apply hmeas hs, Measure.prod_apply hpre,
    MeasureTheory.lintegral_prod_symm _
      (measurable_measure_prodMk_left hpre).aemeasurable]
  have hinner : ∀ z : β, (∫⁻ x, μγ (Prod.mk (x, z) ⁻¹'
        ((fun q : (α × β) × γ => (q.2, q.1.2)) ⁻¹' s)) ∂μα)
      = μγ ((fun t => (t, z)) ⁻¹' s) * μα Set.univ := by
    intro z
    rw [lintegral_congr_ae (ae_of_all _ fun x => by rw [hsec x z])]
    exact MeasureTheory.lintegral_const _
  rw [lintegral_congr_ae (ae_of_all _ hinner)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hgz] with z hz
  rw [hz, Pi.zero_apply, zero_mul]

/-- Half-power squared, in `ℝ≥0∞`: `(r ^ (1/2 : ℝ)) ^ (2 : ℝ) = r`
for every `r` (no side conditions: `ENNReal.rpow_inv_natCast_pow`
covers `0` and `∞`). -/
theorem rpow_half_sq (r : ℝ≥0∞) : (r ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = r := by
  have h1 : (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ := by norm_num
  have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h1, h2, ENNReal.rpow_natCast]
  exact ENNReal.rpow_inv_natCast_pow (by norm_num) r

end QuasiMeasurePreservingExtractions

section ChainBound

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
  [SFinite μ] [SFinite ν] [SFinite ρ]

/-- Cauchy-Schwarz in `ℝ≥0∞` form, with squared (`ℕ`-power)
integrals on the right: for `ℝ≥0∞`-valued a.e.-measurable
`u, v` on any measure space,
`∫⁻ u * v ≤ (∫⁻ u^2)^{1/2} * (∫⁻ v^2)^{1/2}`. -/
theorem lintegral_mul_le_sqrt_mul_sqrt {δ : Type*} [MeasurableSpace δ]
    {m : Measure δ} (u v : δ → ℝ≥0∞) (hu : AEMeasurable u m)
    (hv : AEMeasurable v m) :
    (∫⁻ a, u a * v a ∂m)
      ≤ (∫⁻ a, u a ^ 2 ∂m) ^ (1 / 2 : ℝ)
        * (∫⁻ a, v a ^ 2 ∂m) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m (p := 2) (q := 2)
    ⟨by norm_num, by norm_num, by norm_num⟩ hu hv
  simpa only [Pi.mul_apply, ENNReal.rpow_two, one_div] using h

/-- **The chain bound.** For `ℝ≥0∞`-valued a.e.-measurable
`a` on `(α, μ)`, `u` on `(α × β, μ.prod ν)`, `v` on
`(β × γ, ν.prod ρ)` and `b` on `(γ, ρ)`, the `ℝ≥0∞` integral
of the chained product `a x * u (x, y) * v (y, z) * b z` over
the triple space `((α × γ) × β, (μ.prod ρ).prod ν)` is at
most the product of the four square roots of the squared
integrals. (Tonelli, then Cauchy-Schwarz in `x`, in `z`,
and in the coupling variable `y`; the finiteness hypotheses
on `u` and `v` are what the applications have.) -/
theorem lintegral_chain_le (a : α → ℝ≥0∞) (u : α × β → ℝ≥0∞)
    (v : β × γ → ℝ≥0∞) (b : γ → ℝ≥0∞)
    (ha : AEMeasurable a μ) (hu : AEMeasurable u (μ.prod ν))
    (hv : AEMeasurable v (ν.prod ρ)) (hb : AEMeasurable b ρ)
    (hu2 : ∫⁻ p, u p ^ 2 ∂(μ.prod ν) < ∞)
    (hv2 : ∫⁻ p, v p ^ 2 ∂(ν.prod ρ) < ∞) :
    (∫⁻ q : (α × γ) × β, a q.1.1 * u (q.1.1, q.2) * v (q.2, q.1.2)
        * b q.1.2 ∂((μ.prod ρ).prod ν))
      ≤ (∫⁻ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ p, u p ^ 2 ∂(μ.prod ν)) ^ (1 / 2 : ℝ)
        * (∫⁻ p, v p ^ 2 ∂(ν.prod ρ)) ^ (1 / 2 : ℝ)
        * (∫⁻ z, b z ^ 2 ∂ρ) ^ (1 / 2 : ℝ) := by
  have hInt : AEMeasurable (fun q : (α × γ) × β =>
      a q.1.1 * u (q.1.1, q.2) * v (q.2, q.1.2) * b q.1.2)
      ((μ.prod ρ).prod ν) :=
    (((ha.comp_fst.comp_fst).mul
      (hu.comp_quasiMeasurePreserving
        quasiMeasurePreserving_fst_snd)).mul
      (hv.comp_quasiMeasurePreserving
        quasiMeasurePreserving_snd_fst)).mul
        hb.comp_snd.comp_fst
  -- Middle energies, as functions of the coupling variable.
  set U : β → ℝ≥0∞ := fun y => ∫⁻ x, u (x, y) ^ 2 ∂μ with hUdef
  set V : β → ℝ≥0∞ := fun y => ∫⁻ z, v (y, z) ^ 2 ∂ρ with hVdef
  have hUae : AEMeasurable U ν :=
    (hu.pow_const 2).lintegral_prod_left'
  have hVae : AEMeasurable V ν :=
    (hv.pow_const 2).lintegral_prod_right'
  have hUint : ∫⁻ y, U y ∂ν = ∫⁻ p, u p ^ 2 ∂(μ.prod ν) :=
    (MeasureTheory.lintegral_prod_symm _ (hu.pow_const 2)).symm
  have hVint : ∫⁻ y, V y ∂ν = ∫⁻ p, v p ^ 2 ∂(ν.prod ρ) :=
    (MeasureTheory.lintegral_prod _ (hv.pow_const 2)).symm
  have hUsec : ∀ᵐ y ∂ν, AEMeasurable (fun x => u (x, y)) μ :=
    hu.aestronglyMeasurable.prodMk_right.mono
      fun y hy => hy.aemeasurable
  have hVsec : ∀ᵐ y ∂ν, AEMeasurable (fun z => v (y, z)) ρ :=
    hv.aestronglyMeasurable.prodMk_left.mono
      fun y hy => hy.aemeasurable
  -- The inner integral bound, for a.e. coupling value `y`.
  have hbound : (fun y => ∫⁻ p : α × γ, a p.1 * u (p.1, y)
        * v (y, p.2) * b p.2 ∂(μ.prod ρ))
      ≤ᵐ[ν] (fun y => (∫⁻ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ z, b z ^ 2 ∂ρ) ^ (1 / 2 : ℝ)
        * (U y ^ (1 / 2 : ℝ) * V y ^ (1 / 2 : ℝ))) := by
    filter_upwards [hUsec, hVsec] with y hyU hyV
    have hsplit : (∫⁻ p : α × γ, a p.1 * u (p.1, y)
          * v (y, p.2) * b p.2 ∂(μ.prod ρ))
        = (∫⁻ x, a x * u (x, y) ∂μ)
          * (∫⁻ z, v (y, z) * b z ∂ρ) := by
      have hpm : (∫⁻ p : α × γ, (a p.1 * u (p.1, y))
            * (v (y, p.2) * b p.2) ∂(μ.prod ρ))
          = (∫⁻ x, a x * u (x, y) ∂μ)
            * (∫⁻ z, v (y, z) * b z ∂ρ) :=
        MeasureTheory.lintegral_prod_mul (ha.mul hyU) (hyV.mul hb)
      rw [← hpm]
      refine lintegral_congr_ae (ae_of_all _ fun p => ?_)
      show a p.1 * u (p.1, y) * v (y, p.2) * b p.2
        = (a p.1 * u (p.1, y)) * (v (y, p.2) * b p.2)
      ring
    rw [hsplit]
    refine le_trans (mul_le_mul'
      (lintegral_mul_le_sqrt_mul_sqrt a (fun x => u (x, y)) ha hyU)
      (lintegral_mul_le_sqrt_mul_sqrt (fun z => v (y, z)) b hyV hb))
      (le_of_eq (by ring))
  -- Integrate the bound over the coupling variable.
  rw [MeasureTheory.lintegral_prod_symm _ hInt]
  refine le_trans (lintegral_mono_ae hbound) ?_
  have hmul : (∫⁻ y, ((∫⁻ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ z, b z ^ 2 ∂ρ) ^ (1 / 2 : ℝ))
        * (U y ^ (1 / 2 : ℝ) * V y ^ (1 / 2 : ℝ)) ∂ν)
      = ((∫⁻ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ z, b z ^ 2 ∂ρ) ^ (1 / 2 : ℝ))
        * ∫⁻ y, U y ^ (1 / 2 : ℝ) * V y ^ (1 / 2 : ℝ) ∂ν :=
    MeasureTheory.lintegral_const_mul'' _
      ((ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        hUae).mul
        (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          hVae))
  rw [hmul]
  have hY : (∫⁻ y, U y ^ (1 / 2 : ℝ) * V y ^ (1 / 2 : ℝ) ∂ν)
      ≤ (∫⁻ p, u p ^ 2 ∂(μ.prod ν)) ^ (1 / 2 : ℝ)
        * (∫⁻ p, v p ^ 2 ∂(ν.prod ρ)) ^ (1 / 2 : ℝ) := by
    have h := lintegral_mul_le_sqrt_mul_sqrt
      (fun y => U y ^ (1 / 2 : ℝ)) (fun y => V y ^ (1 / 2 : ℝ))
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hUae)
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hVae)
    have hU2 : (∫⁻ y, (U y ^ (1 / 2 : ℝ)) ^ 2 ∂ν)
        = ∫⁻ p, u p ^ 2 ∂(μ.prod ν) := by
      rw [← hUint]
      refine lintegral_congr_ae (ae_of_all _ fun y => ?_)
      show (U y ^ (1 / 2 : ℝ)) ^ 2 = U y
      rw [← ENNReal.rpow_two]
      exact rpow_half_sq (U y)
    have hV2 : (∫⁻ y, (V y ^ (1 / 2 : ℝ)) ^ 2 ∂ν)
        = ∫⁻ p, v p ^ 2 ∂(ν.prod ρ) := by
      rw [← hVint]
      refine lintegral_congr_ae (ae_of_all _ fun y => ?_)
      show (V y ^ (1 / 2 : ℝ)) ^ 2 = V y
      rw [← ENNReal.rpow_two]
      exact rpow_half_sq (V y)
    rwa [hU2, hV2] at h
  refine le_trans (mul_le_mul le_rfl hY zero_le zero_le)
    (le_of_eq (by ring))

end ChainBound

section Gram

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
  {μ : Measure α} {κ : Measure γ} [SFinite μ] [SFinite κ]
  {F : α × γ → ℂ}

/-- **The Gram kernel** of an `L2` family `F : α × γ → ℂ`:
`K (x, y) = ∫ t, F (x, t) * conj (F (y, t))`, the kernel
obtained by composing two evaluations - one at `x`, one
(conjugated) at `y` - against a third measure space
`(γ, κ)`. -/
noncomputable def gramKernel (κ : Measure γ) (F : α × γ → ℂ) :
    α × α → ℂ :=
  fun p => ∫ t, F (p.1, t) * star (F (p.2, t)) ∂κ

/-- The Gram kernel of an `L2` family is an `L2` kernel:
a.e.-strong measurability by the product-integral
measurability of SHELF-3a-ii's stock (via the extraction
lemmas above), and the squared-norm bound
`‖K (x, y)‖^2 ≤ (∫ ‖F (x, ·)‖^2) * (∫ ‖F (y, ·)‖^2)`
by Cauchy-Schwarz in the third variable. -/
theorem gramKernel_memLp (hF : MemLp F 2 (μ.prod κ)) :
    MemLp (gramKernel κ F) 2 (μ.prod μ) := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hH : AEStronglyMeasurable (fun q : (α × α) × γ =>
      F (q.1.1, q.2) * star (F (q.1.2, q.2))) ((μ.prod μ).prod κ) :=
    (hF.aestronglyMeasurable.comp_quasiMeasurePreserving
      quasiMeasurePreserving_fst_snd).mul
      (continuous_star.comp_aestronglyMeasurable
        (hF.aestronglyMeasurable.comp_quasiMeasurePreserving
          quasiMeasurePreserving_snd_snd))
  have hAESM : AEStronglyMeasurable (gramKernel κ F) (μ.prod μ) :=
    hH.integral_prod_right'
  have heF : AEMeasurable (fun x => ∫⁻ t, ‖F (x, t)‖ₑ ^ 2 ∂κ) μ :=
    (hF.aestronglyMeasurable.enorm.pow_const 2)
      |>.lintegral_prod_right'
  have hFint : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ) < ∞ := by
    rw [← eLpNorm_two_sq (μ.prod κ) hF.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hF.eLpNorm_lt_top
  have heFint : ∫⁻ x, (∫⁻ t, ‖F (x, t)‖ₑ ^ 2 ∂κ) ∂μ
      = ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ) :=
    (MeasureTheory.lintegral_prod _
      (hF.aestronglyMeasurable.enorm.pow_const 2)).symm
  have hsec : ∀ᵐ x ∂μ, MemLp (fun t => F (x, t)) 2 κ :=
    memLp_section_ae_gen hF
  have hbound : ∀ᵐ p ∂(μ.prod μ), ‖gramKernel κ F p‖ₑ ^ 2
      ≤ (∫⁻ t, ‖F (p.1, t)‖ₑ ^ 2 ∂κ)
        * (∫⁻ t, ‖F (p.2, t)‖ₑ ^ 2 ∂κ) := by
    filter_upwards [MeasureTheory.Measure.quasiMeasurePreserving_fst.ae
        hsec,
      MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hsec]
      with p hp1 hp2
    have hφ : Integrable (fun t => F (p.1, t) * star (F (p.2, t))) κ :=
      memLp_one_iff_integrable.mp (hp1.mul hp2.star)
    have hnorm : ‖gramKernel κ F p‖
        ≤ ∫ t, ‖F (p.1, t) * star (F (p.2, t))‖ ∂κ :=
      norm_integral_le_integral_norm _
    have h1 : ‖gramKernel κ F p‖ₑ ^ 2
        = ENNReal.ofReal (‖gramKernel κ F p‖ ^ 2) := by
      simp [enorm, ENNReal.ofReal_pow]
    have h2 : ENNReal.ofReal (‖gramKernel κ F p‖ ^ 2)
        ≤ ENNReal.ofReal
          ((∫ t, ‖F (p.1, t) * star (F (p.2, t))‖ ∂κ) ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    have h3 : ENNReal.ofReal
          ((∫ t, ‖F (p.1, t) * star (F (p.2, t))‖ ∂κ) ^ 2)
        = (∫⁻ t, ‖F (p.1, t)‖ₑ * ‖F (p.2, t)‖ₑ ∂κ) ^ 2 := by
      calc ENNReal.ofReal
            ((∫ t, ‖F (p.1, t) * star (F (p.2, t))‖ ∂κ) ^ 2)
          = (∫⁻ t, ‖F (p.1, t) * star (F (p.2, t))‖ₑ ∂κ) ^ 2 := by
            rw [ENNReal.ofReal_pow
              (integral_nonneg (fun t => norm_nonneg _)) 2]
            congr 1
            exact ofReal_integral_norm_eq_lintegral_enorm hφ
        _ = (∫⁻ t, ‖F (p.1, t)‖ₑ * ‖F (p.2, t)‖ₑ ∂κ) ^ 2 := by
            congr 1
            refine lintegral_congr_ae (ae_of_all _ fun t => ?_)
            simp [enorm_mul]
    have h4 : (∫⁻ t, ‖F (p.1, t)‖ₑ * ‖F (p.2, t)‖ₑ ∂κ) ^ 2
        ≤ (∫⁻ t, ‖F (p.1, t)‖ₑ ^ 2 ∂κ)
          * (∫⁻ t, ‖F (p.2, t)‖ₑ ^ 2 ∂κ) := by
      have hcs := lintegral_mul_le_sqrt_mul_sqrt
        (fun t => ‖F (p.1, t)‖ₑ) (fun t => ‖F (p.2, t)‖ₑ)
        hp1.aestronglyMeasurable.enorm
        hp2.aestronglyMeasurable.enorm
      have hsq : ((∫⁻ t, ‖F (p.1, t)‖ₑ ^ 2 ∂κ) ^ (1 / 2 : ℝ)
            * (∫⁻ t, ‖F (p.2, t)‖ₑ ^ 2 ∂κ) ^ (1 / 2 : ℝ)) ^ 2
          = (∫⁻ t, ‖F (p.1, t)‖ₑ ^ 2 ∂κ)
            * (∫⁻ t, ‖F (p.2, t)‖ₑ ^ 2 ∂κ) := by
        rw [mul_pow]
        simp only [← ENNReal.rpow_two, rpow_half_sq]
      exact le_trans (pow_le_pow_left₀ zero_le hcs 2) (le_of_eq hsq)
    rw [h1]
    exact le_trans h2 (le_trans (le_of_eq h3) h4)
  have hle : (eLpNorm (gramKernel κ F) 2 (μ.prod μ)) ^ 2
      ≤ (∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ))
        * (∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ)) := by
    rw [eLpNorm_two_sq (μ.prod μ) hAESM, ← heFint]
    refine le_trans (lintegral_mono_ae hbound) ?_
    rw [MeasureTheory.lintegral_prod_mul heF heF]
  have hfin2 : (eLpNorm (gramKernel κ F) 2 (μ.prod μ)) ^ 2 < ∞ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top hFint hFint)
  have heLp : eLpNorm (gramKernel κ F) 2 (μ.prod μ) < ∞ := by
    by_contra htop
    have hEq : eLpNorm (gramKernel κ F) 2 (μ.prod μ) = ∞ :=
      le_antisymm le_top (not_lt.mp htop)
    rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hfin2
    exact (lt_irrefl _) hfin2
  exact heLp

/-- **Item (2) - Gram / factorization positivity.** A kernel
admitting a factorization
`K (x, y) = ∫ t, F (x, t) * conj (F (y, t))` against a third
measure space `(γ, κ)`, with `F` an `L2` family on the
product `(μ.prod κ)`, is a `PosKernel`: its quadratic form
is the integral of a squared norm,
`⟪f, T_K f⟫ = ∫ t, ‖∫ x, conj (f x) * F (x, t)‖^2`,
by Fubini (the triple integrand is integrable by the chain
bound) and separation of the product integral. -/
theorem posKernel_gram (hF : MemLp F 2 (μ.prod κ)) :
    PosKernel (gramKernel κ F) (gramKernel_memLp hF) := by
  intro f
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  -- The triple integrand and its integrability.
  have hHae : AEStronglyMeasurable (fun q : (α × α) × γ =>
      star (⇑f q.1.1) * (F (q.1.1, q.2) * star (F (q.1.2, q.2)))
        * ⇑f q.1.2) ((μ.prod μ).prod κ) :=
    (((continuous_star.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable f).comp_fst.comp_fst)).mul
      ((hF.aestronglyMeasurable.comp_quasiMeasurePreserving
        quasiMeasurePreserving_fst_snd).mul
        (continuous_star.comp_aestronglyMeasurable
          (hF.aestronglyMeasurable.comp_quasiMeasurePreserving
            quasiMeasurePreserving_snd_snd))))).mul
      ((Lp.aestronglyMeasurable f).comp_snd.comp_fst)
  have hfint : ∫⁻ x, ‖⇑f x‖ₑ ^ 2 ∂μ < ∞ := by
    rw [← eLpNorm_two_sq μ (Lp.aestronglyMeasurable f)]
    exact ENNReal.pow_lt_top (Lp.memLp f).eLpNorm_lt_top
  have hFint : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ) < ∞ := by
    rw [← eLpNorm_two_sq (μ.prod κ) hF.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hF.eLpNorm_lt_top
  have hv2 : ∫⁻ p : γ × α, ‖F p.swap‖ₑ ^ 2 ∂(κ.prod μ) < ∞ := by
    rw [MeasureTheory.lintegral_prod_swap (fun p => ‖F p‖ₑ ^ 2)]
    exact hFint
  have hroot : ∀ X : ℝ≥0∞, X < ∞ → X ^ (1 / 2 : ℝ) < ∞ :=
    fun X hX => ENNReal.rpow_lt_top_of_nonneg (by norm_num) hX.ne
  have hnormq : ∀ q : (α × α) × γ,
      ‖star (⇑f q.1.1) * (F (q.1.1, q.2) * star (F (q.1.2, q.2)))
        * ⇑f q.1.2‖ₑ
      = ‖⇑f q.1.1‖ₑ * (‖F (q.1.1, q.2)‖ₑ * ‖F (q.1.2, q.2)‖ₑ)
        * ‖⇑f q.1.2‖ₑ := by
    intro q
    simp [enorm_mul]
  have hHfin : HasFiniteIntegral (fun q : (α × α) × γ =>
      star (⇑f q.1.1) * (F (q.1.1, q.2) * star (F (q.1.2, q.2)))
        * ⇑f q.1.2) ((μ.prod μ).prod κ) := by
    rw [hasFiniteIntegral_iff_enorm]
    have hnorm : (∫⁻ q, ‖star (⇑f q.1.1)
          * (F (q.1.1, q.2) * star (F (q.1.2, q.2)))
          * ⇑f q.1.2‖ₑ ∂((μ.prod μ).prod κ))
        = ∫⁻ q, ‖⇑f q.1.1‖ₑ * ‖F (q.1.1, q.2)‖ₑ
            * ‖F (q.1.2, q.2)‖ₑ * ‖⇑f q.1.2‖ₑ
            ∂((μ.prod μ).prod κ) := by
      refine lintegral_congr_ae (ae_of_all _ fun q => ?_)
      show ‖star (⇑f q.1.1) * (F (q.1.1, q.2) * star (F (q.1.2, q.2)))
          * ⇑f q.1.2‖ₑ
        = ‖⇑f q.1.1‖ₑ * ‖F (q.1.1, q.2)‖ₑ * ‖F (q.1.2, q.2)‖ₑ
          * ‖⇑f q.1.2‖ₑ
      rw [hnormq q]
      ring
    rw [hnorm]
    refine lt_of_le_of_lt (lintegral_chain_le (fun x => ‖⇑f x‖ₑ)
      (fun p => ‖F p‖ₑ) (fun p => ‖F p.swap‖ₑ) (fun y => ‖⇑f y‖ₑ)
      (Lp.aestronglyMeasurable f).enorm
      hF.aestronglyMeasurable.enorm
      (hF.aestronglyMeasurable.enorm.prod_swap)
      (Lp.aestronglyMeasurable f).enorm
      hFint hv2) ?_
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (hroot _ hfint)
        (hroot _ hFint)) (hroot _ hv2)) (hroot _ hfint)
  have hHint : Integrable (fun q : (α × α) × γ =>
      star (⇑f q.1.1) * (F (q.1.1, q.2) * star (F (q.1.2, q.2)))
        * ⇑f q.1.2) ((μ.prod μ).prod κ) := ⟨hHae, hHfin⟩
  -- The inner product separates, pointwise in `t`.
  have h3 : ∀ t, (∫ p, star (⇑f p.1)
        * (F (p.1, t) * star (F (p.2, t))) * ⇑f p.2 ∂(μ.prod μ))
      = (∫ x, star (⇑f x) * F (x, t) ∂μ)
        * star (∫ x, star (⇑f x) * F (x, t) ∂μ) := by
    intro t
    have hsplit : (∫ p, star (⇑f p.1)
          * (F (p.1, t) * star (F (p.2, t))) * ⇑f p.2 ∂(μ.prod μ))
        = (∫ x, star (⇑f x) * F (x, t) ∂μ)
          * (∫ y, star (F (y, t)) * ⇑f y ∂μ) := by
      rw [← integral_prod_mul (fun x => star (⇑f x) * F (x, t))
        (fun y => star (F (y, t)) * ⇑f y)]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      show star (⇑f p.1) * (F (p.1, t) * star (F (p.2, t))) * ⇑f p.2
        = star (⇑f p.1) * F (p.1, t) * (star (F (p.2, t)) * ⇑f p.2)
      ring
    have hstarconv : ∀ w : ℂ, star w = (starRingEnd ℂ) w :=
      fun w => by rw [starRingEnd_apply]
    have hstar : star (∫ x, star (⇑f x) * F (x, t) ∂μ)
        = ∫ y, star (F (y, t)) * ⇑f y ∂μ := by
      rw [hstarconv (∫ x, star (⇑f x) * F (x, t) ∂μ),
        ← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (starRingEnd ℂ) (star (⇑f x) * F (x, t))
        = star (F (x, t)) * ⇑f x
      rw [starRingEnd_apply, star_mul, star_star]
    rw [hsplit, ← hstar]
  -- Assemble: Fubini, then swap, then separate.
  have h2 : (∫ p, star (⇑f p.1) * (gramKernel κ F p * ⇑f p.2)
        ∂(μ.prod μ))
      = ∫ p, ∫ t, star (⇑f p.1) * (F (p.1, t) * star (F (p.2, t)))
          * ⇑f p.2 ∂κ ∂(μ.prod μ) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show star (⇑f p.1) * ((∫ t, F (p.1, t) * star (F (p.2, t)) ∂κ)
        * ⇑f p.2)
      = ∫ t, star (⇑f p.1) * (F (p.1, t) * star (F (p.2, t)))
          * ⇑f p.2 ∂κ
    rw [← mul_assoc, ← integral_const_mul, ← integral_mul_const]
  have h1 : inner ℂ f (integralKernelOp (gramKernel_memLp hF) f)
      = ∫ t, (∫ x, star (⇑f x) * F (x, t) ∂μ)
          * star (∫ x, star (⇑f x) * F (x, t) ∂μ) ∂κ := by
    rw [integralKernelOp_inner (gramKernel_memLp hF) f f, h2,
      integral_integral_swap hHint]
    exact integral_congr_ae (ae_of_all _ h3)
  have hcast : ∀ z : ℂ, z * star z
      = RCLike.ofReal (‖z‖ ^ 2) := by
    intro z
    have hconv : star z = (starRingEnd ℂ) z := by
      rw [starRingEnd_apply]
    rw [hconv, RCLike.mul_conj, ← RCLike.ofReal_pow]
  have hInt2 : (∫ t, (∫ x, star (⇑f x) * F (x, t) ∂μ)
        * star (∫ x, star (⇑f x) * F (x, t) ∂μ) ∂κ)
      = RCLike.ofReal
          (∫ t, ‖∫ x, star (⇑f x) * F (x, t) ∂μ‖ ^ 2 ∂κ) := by
    rw [← integral_ofReal]
    exact integral_congr_ae (ae_of_all _ fun t => hcast _)
  rw [h1, hInt2, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg (fun t => pow_nonneg (norm_nonneg _) 2)

end Gram

section Composition

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
  [SFinite μ] [SFinite ν] [SFinite ρ]
  {K₁ : α × β → ℂ} {K₂ : β × γ → ℂ}

/-- The **composition kernel**: `p = (x, z) ↦ ∫ y, K₁ (x, y) *
K₂ (y, z)`, the kernel of the operator composition
`T_{K₁} ∘ T_{K₂}` (item (4)). -/
noncomputable def compKernel (ν : Measure β) (K₁ : α × β → ℂ)
    (K₂ : β × γ → ℂ) : α × γ → ℂ :=
  fun p => ∫ y, K₁ (p.1, y) * K₂ (y, p.2) ∂ν

/-- The **adjoint kernel**: `p = (y, x) ↦ conj (K (x, y))`, the
kernel of the adjoint operator `T_K^*` (item (4)). -/
noncomputable def adjKernel (K : α × β → ℂ) : β × α → ℂ :=
  fun p => star (K (p.2, p.1))

/-- The adjoint kernel of an `L2` kernel is `L2`: swapping the
variables is measure-preserving and `star` preserves `MemLp`. -/
theorem adjKernel_memLp {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν)) :
    MemLp (adjKernel K) 2 (ν.prod μ) := by
  have hswap : MemLp (fun p : β × α => K p.swap) 2 (ν.prod μ) :=
    hK.comp_measurePreserving
      MeasureTheory.Measure.measurePreserving_swap
  exact hswap.star

/-- The composition kernel of two `L2` kernels is `L2`: its
sections are products of `L2` sections (integrable by the
Holder triple `2, 2, 1`), Cauchy-Schwarz in the coupling
variable bounds the section energies, and Tonelli separates
the total energy into the product of the two kernel energies.
This is the composition half of item (4). -/
theorem compKernel_memLp (hK₁ : MemLp K₁ 2 (μ.prod ν))
    (hK₂ : MemLp K₂ 2 (ν.prod ρ)) :
    MemLp (compKernel ν K₁ K₂) 2 (μ.prod ρ) := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hW : AEStronglyMeasurable
      (fun q : (α × γ) × β => K₁ (q.1.1, q.2) * K₂ (q.2, q.1.2))
      ((μ.prod ρ).prod ν) :=
    (hK₁.aestronglyMeasurable.comp_quasiMeasurePreserving
      quasiMeasurePreserving_fst_snd).mul
      (hK₂.aestronglyMeasurable.comp_quasiMeasurePreserving
        quasiMeasurePreserving_snd_fst)
  have hAESM : AEStronglyMeasurable (compKernel ν K₁ K₂) (μ.prod ρ) :=
    hW.integral_prod_right'
  have hK₁int : ∫⁻ p, ‖K₁ p‖ₑ ^ 2 ∂(μ.prod ν) < ∞ := by
    rw [← eLpNorm_two_sq (μ.prod ν) hK₁.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hK₁.eLpNorm_lt_top
  have hK₂int : ∫⁻ p, ‖K₂ p‖ₑ ^ 2 ∂(ν.prod ρ) < ∞ := by
    rw [← eLpNorm_two_sq (ν.prod ρ) hK₂.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hK₂.eLpNorm_lt_top
  have hK₂s : MemLp (fun p : γ × β => K₂ p.swap) 2 (ρ.prod ν) :=
    hK₂.comp_measurePreserving
      MeasureTheory.Measure.measurePreserving_swap
  have hA : AEMeasurable (fun x => ∫⁻ y, ‖K₁ (x, y)‖ₑ ^ 2 ∂ν) μ :=
    (hK₁.aestronglyMeasurable.enorm.pow_const 2).lintegral_prod_right'
  have hB : AEMeasurable (fun z => ∫⁻ y, ‖K₂ (y, z)‖ₑ ^ 2 ∂ν) ρ :=
    (hK₂s.aestronglyMeasurable.enorm.pow_const 2).lintegral_prod_right'
  have hT1 : ∫⁻ x, (∫⁻ y, ‖K₁ (x, y)‖ₑ ^ 2 ∂ν) ∂μ
      = ∫⁻ p, ‖K₁ p‖ₑ ^ 2 ∂(μ.prod ν) :=
    (MeasureTheory.lintegral_prod _
      (hK₁.aestronglyMeasurable.enorm.pow_const 2)).symm
  have hT2 : ∫⁻ z, (∫⁻ y, ‖K₂ (y, z)‖ₑ ^ 2 ∂ν) ∂ρ
      = ∫⁻ p, ‖K₂ p‖ₑ ^ 2 ∂(ν.prod ρ) := by
    have hswap2 : ∫⁻ p, ‖K₂ p‖ₑ ^ 2 ∂(ν.prod ρ)
        = ∫⁻ p : γ × β, ‖K₂ p.swap‖ₑ ^ 2 ∂(ρ.prod ν) :=
      (MeasureTheory.lintegral_prod_swap (fun p => ‖K₂ p‖ₑ ^ 2)).symm
    rw [hswap2]
    exact (MeasureTheory.lintegral_prod _
      (hK₂s.aestronglyMeasurable.enorm.pow_const 2)).symm
  have hsec1 : ∀ᵐ x ∂μ, MemLp (fun y => K₁ (x, y)) 2 ν :=
    memLp_section_ae_gen hK₁
  have hsec2 : ∀ᵐ z ∂ρ, MemLp (fun y => K₂ (y, z)) 2 ν :=
    memLp_section_ae_gen hK₂s
  have hbound : ∀ᵐ p ∂(μ.prod ρ), ‖compKernel ν K₁ K₂ p‖ₑ ^ 2
      ≤ (∫⁻ y, ‖K₁ (p.1, y)‖ₑ ^ 2 ∂ν)
        * (∫⁻ y, ‖K₂ (y, p.2)‖ₑ ^ 2 ∂ν) := by
    filter_upwards [MeasureTheory.Measure.quasiMeasurePreserving_fst.ae
        hsec1,
      MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hsec2]
      with p hp1 hp2
    have hφ : Integrable (fun y => K₁ (p.1, y) * K₂ (y, p.2)) ν :=
      memLp_one_iff_integrable.mp (hp1.mul hp2)
    have hnorm : ‖compKernel ν K₁ K₂ p‖
        ≤ ∫ y, ‖K₁ (p.1, y) * K₂ (y, p.2)‖ ∂ν :=
      norm_integral_le_integral_norm _
    have h1 : ‖compKernel ν K₁ K₂ p‖ₑ ^ 2
        = ENNReal.ofReal (‖compKernel ν K₁ K₂ p‖ ^ 2) := by
      simp [enorm, ENNReal.ofReal_pow]
    have h2 : ENNReal.ofReal (‖compKernel ν K₁ K₂ p‖ ^ 2)
        ≤ ENNReal.ofReal
          ((∫ y, ‖K₁ (p.1, y) * K₂ (y, p.2)‖ ∂ν) ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    have h3 : ENNReal.ofReal
          ((∫ y, ‖K₁ (p.1, y) * K₂ (y, p.2)‖ ∂ν) ^ 2)
        = (∫⁻ y, ‖K₁ (p.1, y)‖ₑ * ‖K₂ (y, p.2)‖ₑ ∂ν) ^ 2 := by
      calc ENNReal.ofReal
            ((∫ y, ‖K₁ (p.1, y) * K₂ (y, p.2)‖ ∂ν) ^ 2)
          = (∫⁻ y, ‖K₁ (p.1, y) * K₂ (y, p.2)‖ₑ ∂ν) ^ 2 := by
            rw [ENNReal.ofReal_pow
              (integral_nonneg (fun y => norm_nonneg _)) 2]
            congr 1
            exact ofReal_integral_norm_eq_lintegral_enorm hφ
        _ = (∫⁻ y, ‖K₁ (p.1, y)‖ₑ * ‖K₂ (y, p.2)‖ₑ ∂ν) ^ 2 := by
            congr 1
            refine lintegral_congr_ae (ae_of_all _ fun y => ?_)
            simp [enorm_mul]
    have h4 : (∫⁻ y, ‖K₁ (p.1, y)‖ₑ * ‖K₂ (y, p.2)‖ₑ ∂ν) ^ 2
        ≤ (∫⁻ y, ‖K₁ (p.1, y)‖ₑ ^ 2 ∂ν)
          * (∫⁻ y, ‖K₂ (y, p.2)‖ₑ ^ 2 ∂ν) := by
      have hcs := lintegral_mul_le_sqrt_mul_sqrt
        (fun y => ‖K₁ (p.1, y)‖ₑ) (fun y => ‖K₂ (y, p.2)‖ₑ)
        hp1.aestronglyMeasurable.enorm
        hp2.aestronglyMeasurable.enorm
      have hsq : ((∫⁻ y, ‖K₁ (p.1, y)‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ)
            * (∫⁻ y, ‖K₂ (y, p.2)‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2
          = (∫⁻ y, ‖K₁ (p.1, y)‖ₑ ^ 2 ∂ν)
            * (∫⁻ y, ‖K₂ (y, p.2)‖ₑ ^ 2 ∂ν) := by
        rw [mul_pow]
        simp only [← ENNReal.rpow_two, rpow_half_sq]
      exact le_trans (pow_le_pow_left₀ zero_le hcs 2) (le_of_eq hsq)
    rw [h1]
    exact le_trans h2 (le_trans (le_of_eq h3) h4)
  have hle : (eLpNorm (compKernel ν K₁ K₂) 2 (μ.prod ρ)) ^ 2
      ≤ (∫⁻ p, ‖K₁ p‖ₑ ^ 2 ∂(μ.prod ν))
        * (∫⁻ p, ‖K₂ p‖ₑ ^ 2 ∂(ν.prod ρ)) := by
    rw [eLpNorm_two_sq (μ.prod ρ) hAESM, ← hT1, ← hT2]
    refine le_trans (lintegral_mono_ae hbound) ?_
    rw [MeasureTheory.lintegral_prod_mul hA hB]
  have hfin2 : (eLpNorm (compKernel ν K₁ K₂) 2 (μ.prod ρ)) ^ 2 < ∞ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top hK₁int hK₂int)
  have heLp : eLpNorm (compKernel ν K₁ K₂) 2 (μ.prod ρ) < ∞ := by
    by_contra htop
    have hEq : eLpNorm (compKernel ν K₁ K₂) 2 (μ.prod ρ) = ∞ :=
      le_antisymm le_top (not_lt.mp htop)
    rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hfin2
    exact (lt_irrefl _) hfin2
  exact heLp

/-- The middle-swap measurable equivalence
`((x, y), z) ↦ ((x, z), y)`, built from the associator, a
product congruence with the commutator, and the associator
back. -/
noncomputable def shuffleEquiv : ((α × β) × γ) ≃ᵐ ((α × γ) × β) :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl α).prodCongr
      (MeasurableEquiv.prodComm (α := β) (β := γ)))).trans
    MeasurableEquiv.prodAssoc.symm

/-- The middle swap is measure-preserving between the two
triple product measures. -/
theorem measurePreserving_shuffle :
    MeasureTheory.MeasurePreserving
      (shuffleEquiv (α := α) (β := β) (γ := γ))
      ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  have hA1 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := α) (β := β) (γ := γ))
      ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) :=
    MeasureTheory.measurePreserving_prodAssoc μ ν ρ
  have hA2 : MeasureTheory.MeasurePreserving
      ((MeasurableEquiv.refl α).prodCongr
        (MeasurableEquiv.prodComm (α := β) (β := γ)))
      (μ.prod (ν.prod ρ)) (μ.prod (ρ.prod ν)) :=
    MeasureTheory.MeasurePreserving.prod
      (MeasureTheory.MeasurePreserving.id μ)
      MeasureTheory.Measure.measurePreserving_swap
  have hA3 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)).symm
      (μ.prod (ρ.prod ν)) ((μ.prod ρ).prod ν) :=
    MeasureTheory.MeasurePreserving.symm _
      (MeasureTheory.measurePreserving_prodAssoc μ ρ ν)
  exact hA3.comp (hA2.comp hA1)

/-- The triple integrand of the composition identity, in the
`((α × γ) × β)` association, is integrable: its absolute
integral is the chain bound of the `ChainBound` section. -/
theorem integrable_triple_left (hK₁ : MemLp K₁ 2 (μ.prod ν))
    (hK₂ : MemLp K₂ 2 (ν.prod ρ)) (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ρ) :
    Integrable (fun q : (α × γ) × β => star (⇑g q.1.1)
      * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2)))
      ((μ.prod ρ).prod ν) := by
  have hK₁int : ∫⁻ p, ‖K₁ p‖ₑ ^ 2 ∂(μ.prod ν) < ∞ := by
    rw [← eLpNorm_two_sq (μ.prod ν) hK₁.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hK₁.eLpNorm_lt_top
  have hK₂int : ∫⁻ p, ‖K₂ p‖ₑ ^ 2 ∂(ν.prod ρ) < ∞ := by
    rw [← eLpNorm_two_sq (ν.prod ρ) hK₂.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hK₂.eLpNorm_lt_top
  have hgint : ∫⁻ x, ‖⇑g x‖ₑ ^ 2 ∂μ < ∞ := by
    rw [← eLpNorm_two_sq μ (Lp.aestronglyMeasurable g)]
    exact ENNReal.pow_lt_top (MeasureTheory.Lp.memLp g).eLpNorm_lt_top
  have hfint : ∫⁻ z, ‖⇑f z‖ₑ ^ 2 ∂ρ < ∞ := by
    rw [← eLpNorm_two_sq ρ (Lp.aestronglyMeasurable f)]
    exact ENNReal.pow_lt_top (MeasureTheory.Lp.memLp f).eLpNorm_lt_top
  have hroot : ∀ X : ℝ≥0∞, X < ∞ → X ^ (1 / 2 : ℝ) < ∞ :=
    fun X hX => ENNReal.rpow_lt_top_of_nonneg (by norm_num) hX.ne
  refine ⟨?_, ?_⟩
  · exact (continuous_star.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
          ((MeasureTheory.Measure.quasiMeasurePreserving_fst
            (μ := μ) (ν := ρ)).comp
            (MeasureTheory.Measure.quasiMeasurePreserving_fst
              (μ := μ.prod ρ) (ν := ν))))).mul
      ((hK₁.aestronglyMeasurable.comp_quasiMeasurePreserving
          quasiMeasurePreserving_fst_snd).mul
        ((hK₂.aestronglyMeasurable.comp_quasiMeasurePreserving
            quasiMeasurePreserving_snd_fst).mul
          ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
            ((MeasureTheory.Measure.quasiMeasurePreserving_snd
              (μ := μ) (ν := ρ)).comp
              (MeasureTheory.Measure.quasiMeasurePreserving_fst
                (μ := μ.prod ρ) (ν := ν))))))
  · have hle := lintegral_chain_le (fun x => ‖⇑g x‖ₑ)
      (fun p => ‖K₁ p‖ₑ) (fun p => ‖K₂ p‖ₑ) (fun z => ‖⇑f z‖ₑ)
      (Lp.aestronglyMeasurable g).enorm
      hK₁.aestronglyMeasurable.enorm
      hK₂.aestronglyMeasurable.enorm
      (Lp.aestronglyMeasurable f).enorm hK₁int hK₂int
    have hfin : (∫⁻ x, ‖⇑g x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ p, ‖K₁ p‖ₑ ^ 2 ∂(μ.prod ν)) ^ (1 / 2 : ℝ)
        * (∫⁻ p, ‖K₂ p‖ₑ ^ 2 ∂(ν.prod ρ)) ^ (1 / 2 : ℝ)
        * (∫⁻ z, ‖⇑f z‖ₑ ^ 2 ∂ρ) ^ (1 / 2 : ℝ) < ∞ :=
      ENNReal.mul_lt_top
        (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (hroot _ hgint) (hroot _ hK₁int))
          (hroot _ hK₂int)) (hroot _ hfint)
    have hEq : ∫⁻ q, ‖star (⇑g q.1.1)
          * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))‖ₑ
          ∂((μ.prod ρ).prod ν)
        = ∫⁻ q : (α × γ) × β, ‖⇑g q.1.1‖ₑ * ‖K₁ (q.1.1, q.2)‖ₑ
            * ‖K₂ (q.2, q.1.2)‖ₑ * ‖⇑f q.1.2‖ₑ
            ∂((μ.prod ρ).prod ν) := by
      refine lintegral_congr_ae (ae_of_all _ fun q => ?_)
      have hstar : ‖star (⇑g q.1.1)‖ₑ = ‖⇑g q.1.1‖ₑ := by
        simp [enorm]
      show ‖star (⇑g q.1.1)
          * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))‖ₑ
        = ‖⇑g q.1.1‖ₑ * ‖K₁ (q.1.1, q.2)‖ₑ * ‖K₂ (q.2, q.1.2)‖ₑ
          * ‖⇑f q.1.2‖ₑ
      rw [enorm_mul, enorm_mul, enorm_mul, hstar]
      ring
    show ∫⁻ q, ‖star (⇑g q.1.1)
        * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))‖ₑ
        ∂((μ.prod ρ).prod ν) < ∞
    rw [hEq]
    exact lt_of_le_of_lt hle hfin

/-- The triple integrand of the composition identity, in the
`((α × β) × γ)` association, is integrable: absolute
integrability transfers from the other association along the
measure-preserving middle swap. -/
theorem integrable_triple_right (hK₁ : MemLp K₁ 2 (μ.prod ν))
    (hK₂ : MemLp K₂ 2 (ν.prod ρ)) (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ρ) :
    Integrable (fun q : (α × β) × γ => star (⇑g q.1.1)
      * (K₁ q.1 * (K₂ (q.1.2, q.2) * ⇑f q.2)))
      ((μ.prod ν).prod ρ) := by
  refine ⟨?_, ?_⟩
  · exact (continuous_star.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
          ((MeasureTheory.Measure.quasiMeasurePreserving_fst
            (μ := μ) (ν := ν)).comp
            (MeasureTheory.Measure.quasiMeasurePreserving_fst
              (μ := μ.prod ν) (ν := ρ))))).mul
      ((hK₁.aestronglyMeasurable.comp_quasiMeasurePreserving
          (MeasureTheory.Measure.quasiMeasurePreserving_fst
            (μ := μ.prod ν) (ν := ρ))).mul
        ((hK₂.aestronglyMeasurable.comp_quasiMeasurePreserving
            quasiMeasurePreserving_snd_snd).mul
          ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd
              (μ := μ.prod ν) (ν := ρ)))))
  · have hΦ := (integrable_triple_left hK₁ hK₂ g f).hasFiniteIntegral
    have htrans : ∫⁻ q, ‖star (⇑g q.1.1)
          * (K₁ q.1 * (K₂ (q.1.2, q.2) * ⇑f q.2))‖ₑ
          ∂((μ.prod ν).prod ρ)
        = ∫⁻ q, ‖star (⇑g q.1.1)
            * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))‖ₑ
            ∂((μ.prod ρ).prod ν) := by
      have h := (measurePreserving_shuffle (μ := μ) (ν := ν) (ρ := ρ)).lintegral_comp_emb
        (shuffleEquiv (α := α) (β := β) (γ := γ)).measurableEmbedding
        (fun q : (α × γ) × β => ‖star (⇑g q.1.1)
          * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))‖ₑ)
      refine (lintegral_congr_ae (ae_of_all _ fun q => ?_)).trans h
      rfl
    show ∫⁻ q, ‖star (⇑g q.1.1)
        * (K₁ q.1 * (K₂ (q.1.2, q.2) * ⇑f q.2))‖ₑ
        ∂((μ.prod ν).prod ρ) < ∞
    rw [htrans]
    exact hΦ

/-- **Composition kernel formula** (item (4)): the operator of
the composition kernel is the composition of the operators,
`T_{K₁∘K₂} = T_{K₁} ∘ T_{K₂}`. Both quadratic forms unfold to
the same triple integral: Fubini for the integrable triple
integrand, the composition side separating through the
measure-preserving middle swap, the operator side through the
a.e. pointwise formula for `T_{K₂} f`; equality of operators
follows since the difference has vanishing self-inner
product. -/
theorem integralKernelOp_comp (hK₁ : MemLp K₁ 2 (μ.prod ν))
    (hK₂ : MemLp K₂ 2 (ν.prod ρ)) :
    integralKernelOp (compKernel_memLp hK₁ hK₂)
      = (integralKernelOp hK₁).comp (integralKernelOp hK₂) := by
  apply ContinuousLinearMap.ext fun f => ?_
  have hkey : ∀ g : Lp ℂ 2 μ,
      inner ℂ g (integralKernelOp (compKernel_memLp hK₁ hK₂) f)
        = inner ℂ g ((integralKernelOp hK₁)
            (integralKernelOp hK₂ f)) := by
    intro g
    have hΦint := integrable_triple_left hK₁ hK₂ g f
    have hΨint := integrable_triple_right hK₁ hK₂ g f
    have hbridge : ∫ q : (α × β) × γ, star (⇑g q.1.1)
          * (K₁ q.1 * (K₂ (q.1.2, q.2) * ⇑f q.2))
          ∂((μ.prod ν).prod ρ)
        = ∫ q : (α × γ) × β, star (⇑g q.1.1)
            * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))
            ∂((μ.prod ρ).prod ν) := by
      have h := (measurePreserving_shuffle (μ := μ) (ν := ν)
        (ρ := ρ)).integral_comp' (fun q : (α × γ) × β =>
          star (⇑g q.1.1)
            * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2)))
      refine (integral_congr_ae (ae_of_all _ fun q => ?_)).trans h
      rfl
    calc inner ℂ g (integralKernelOp (compKernel_memLp hK₁ hK₂) f)
        = ∫ q : (α × γ) × β, star (⇑g q.1.1)
            * (K₁ (q.1.1, q.2) * (K₂ (q.2, q.1.2) * ⇑f q.1.2))
            ∂((μ.prod ρ).prod ν) := by
          rw [integralKernelOp_inner (compKernel_memLp hK₁ hK₂) g f,
            integral_prod _ hΦint]
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          show star (⇑g p.1) * (compKernel ν K₁ K₂ p * ⇑f p.2)
            = ∫ y, star (⇑g p.1)
                * (K₁ (p.1, y) * (K₂ (y, p.2) * ⇑f p.2)) ∂ν
          show star (⇑g p.1)
              * ((∫ y, K₁ (p.1, y) * K₂ (y, p.2) ∂ν) * ⇑f p.2)
            = ∫ y, star (⇑g p.1)
                * (K₁ (p.1, y) * (K₂ (y, p.2) * ⇑f p.2)) ∂ν
          rw [← integral_mul_const, ← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          ring
      _ = ∫ q : (α × β) × γ, star (⇑g q.1.1)
            * (K₁ q.1 * (K₂ (q.1.2, q.2) * ⇑f q.2))
            ∂((μ.prod ν).prod ρ) := hbridge.symm
      _ = inner ℂ g ((integralKernelOp hK₁)
            (integralKernelOp hK₂ f)) := by
          rw [integralKernelOp_inner hK₁ g (integralKernelOp hK₂ f),
            integral_prod _ hΨint]
          refine integral_congr_ae ?_
          filter_upwards [MeasureTheory.Measure.quasiMeasurePreserving_snd.ae
              (coeFn_integralKernelOp hK₂ f)] with p hp
          show (∫ z, star (⇑g p.1) * (K₁ p * (K₂ (p.2, z) * ⇑f z))
              ∂ρ)
            = star (⇑g p.1) * (K₁ p * ⇑(integralKernelOp hK₂ f) p.2)
          rw [hp]
          show (∫ z, star (⇑g p.1) * (K₁ p * (K₂ (p.2, z) * ⇑f z))
              ∂ρ)
            = star (⇑g p.1)
              * (K₁ p * (∫ z, K₂ (p.2, z) * ⇑f z ∂ρ))
          rw [← integral_const_mul, ← integral_const_mul]
  have hself : inner ℂ
      (integralKernelOp (compKernel_memLp hK₁ hK₂) f
        - (integralKernelOp hK₁) (integralKernelOp hK₂ f))
      (integralKernelOp (compKernel_memLp hK₁ hK₂) f
        - (integralKernelOp hK₁) (integralKernelOp hK₂ f)) = 0 := by
    rw [inner_sub_right, hkey, sub_self]
  have hnorm : ‖integralKernelOp (compKernel_memLp hK₁ hK₂) f
      - (integralKernelOp hK₁) (integralKernelOp hK₂ f)‖ = 0 := by
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (integralKernelOp (compKernel_memLp hK₁ hK₂) f
        - (integralKernelOp hK₁) (integralKernelOp hK₂ f))
    rw [hself] at h2
    have h3 : (‖integralKernelOp (compKernel_memLp hK₁ hK₂) f
        - (integralKernelOp hK₁) (integralKernelOp hK₂ f)‖ : ℂ)
        = 0 :=
      sq_eq_zero_iff.mp h2.symm
    exact_mod_cast h3
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The adjoint kernel represents the adjoint operator:
`⟪T_K f, g⟫ = ⟪f, T_{K*} g⟫`, by conjugate symmetry, the
conjugation of the integral, and Fubini in the form of the
product swap. -/
theorem integralKernelOp_adj_inner {K : α × β → ℂ}
    (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 ν) (g : Lp ℂ 2 μ) :
    inner ℂ (integralKernelOp hK f) g
      = inner ℂ f (integralKernelOp (adjKernel_memLp hK) g) := by
  have hpt : ∀ p : α × β, (starRingEnd ℂ)
        (star (⇑g p.1) * (K p * ⇑f p.2))
      = ⇑g p.1 * (star (K p) * star (⇑f p.2)) := by
    intro p
    rw [starRingEnd_apply, star_mul, star_mul, star_star]
    ring
  calc inner ℂ (integralKernelOp hK f) g
      = (starRingEnd ℂ) (∫ p, star (⇑g p.1) * (K p * ⇑f p.2)
          ∂(μ.prod ν)) := by
        rw [← integralKernelOp_inner hK g f]
        exact (inner_conj_symm _ _).symm
    _ = ∫ p, ⇑g p.1 * (star (K p) * star (⇑f p.2))
          ∂(μ.prod ν) := by
        rw [← integral_conj]
        exact integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ p : β × α, star (⇑f p.1) * (adjKernel K p * ⇑g p.2)
          ∂(ν.prod μ) := by
        rw [← integral_prod_swap]
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        show ⇑g p.2 * (star (K (p.2, p.1)) * star (⇑f p.1))
          = star (⇑f p.1) * (star (K (p.2, p.1)) * ⇑g p.2)
        ring
    _ = inner ℂ f (integralKernelOp (adjKernel_memLp hK) g) :=
        (integralKernelOp_inner (adjKernel_memLp hK) f g).symm

/-- **Composition positivity corollary** (item (4)): for every
`L2` kernel `K`, the composition of its adjoint kernel with
itself, `(y, z) ↦ ∫ x, conj (K (x, y)) * K (x, z)`, is a
`PosKernel`: the operator is `T_K^* ∘ T_K`, so the quadratic
form is `⟪f, T_K^* (T_K f)⟫ = ⟪T_K f, T_K f⟫ = ‖T_K f‖^2`,
a nonnegative real. -/
theorem posKernel_comp_adj {K : α × β → ℂ}
    (hK : MemLp K 2 (μ.prod ν)) :
    PosKernel (compKernel μ (adjKernel K) K)
      (compKernel_memLp (adjKernel_memLp hK) hK) := by
  intro f
  have h1 : inner ℂ f (integralKernelOp
        (compKernel_memLp (adjKernel_memLp hK) hK) f)
      = inner ℂ (integralKernelOp hK f)
          (integralKernelOp hK f) := by
    rw [integralKernelOp_comp (adjKernel_memLp hK) hK]
    show inner ℂ f ((integralKernelOp (adjKernel_memLp hK))
        (integralKernelOp hK f))
      = inner ℂ (integralKernelOp hK f) (integralKernelOp hK f)
    exact (integralKernelOp_adj_inner hK f
      (integralKernelOp hK f)).symm
  rw [h1]
  have h2 : (inner ℂ (integralKernelOp hK f)
        (integralKernelOp hK f)).re
      = ‖integralKernelOp hK f‖ ^ 2 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (integralKernelOp hK f)
    rw [h, ← RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_re]
  rw [h2]
  exact pow_nonneg (norm_nonneg _) 2

end Composition

end ThetLogos

