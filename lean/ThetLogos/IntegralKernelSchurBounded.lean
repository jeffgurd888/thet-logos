import ThetLogos.IntegralKernelSchur
import Mathlib.Tactic

open Filter Topology ComplexInnerProductSpace MeasureTheory
open scoped ENNReal NNReal

namespace ThetLogos

/-!
# Integral-kernel Schur product, RESTRICTED regime - Q3-3

Working label (naming is Jeff's). Built under the Q3 menu
(scoping: `q3-distance-scoping-2026-11-06.md` §5, item Q3-3),
consuming the landed SHELF-3b module
`IntegralKernelSchur.lean`: `PosKernel` (item (1), the
registered operator-level definition), `gramKernel`,
`gramKernel_memLp` and `posKernel_gram` (item (2),
Gram-factorization positivity). Nothing landed is edited,
re-derived, or re-registered here.

## What is proved

The classical tensor-product proof of the Schur product
theorem, at restricted generality: the pointwise product of
two GRAM kernels is again a Gram kernel - over the product
of the two feature spaces, with the tensor-product feature
`(x, (s, t)) ↦ F (x, s) * G (x, t)` - hence is a `PosKernel`
by the landed item (2). The product identity
(`gramKernel_mul`) holds pointwise everywhere, with no
extra hypothesis. What the restriction buys is the
`MemLp 2` membership of the tensor feature, without which
item (2) cannot be applied to it.

## The exact restricted hypothesis

Both factors are Gram-factorized:
`K₁ = gramKernel κ F`, `K₂ = gramKernel ν G` with
`F : α × γ → ℂ` in `L2 (μ.prod κ)` and `G : α × δ → ℂ` in
`L2 (μ.prod ν)`; AND the second factor carries the bound
the landed counterexample shape names:

* every section `t ↦ G (x, t)` is in `L2 ν`
  (`hGsec : ∀ x, MemLp (fun t => G (x, t)) 2 ν`), and
* its row energy is uniformly bounded: for some finite
  `C : ℝ≥0∞`,
  `hGbound : ∀ x, ∫⁻ t, ‖G (x, t)‖ₑ ^ 2 ∂ν ≤ C`.

Under these, `tensorFeature F G` is `MemLp 2` over
`μ.prod (κ.prod ν)` (`tensorFeature_memLp`: the energy
Tonelli-separates into row energies, the bounded one pulls
out, the other integrates by `F ∈ L2`), the product kernel
is `MemLp 2` (`memLp_gramKernel_mul`), and it is a
`PosKernel` (`posKernel_gram_mul`). The primed pair
(`memLp_gramKernel_mul'`, `posKernel_gram_mul'`) is the
same statement with the bound carried by the FIRST factor
instead (product commutativity transports it).

## What is NOT proved - the residue, named

Item (3) of `IntegralKernelSchur.lean` at full generality
remains OPEN, exactly as on that module's face: the
pointwise product of two general `L2` kernels need not be
`L2` (counterexample shape there: `K (x, y) = g x * g y`
with `g ∈ L2 ∖ L4`), and a general `PosKernel` admits no
Gram factorization, so neither the route nor the statement
here covers arbitrary positive kernels. This brick covers
only the Gram-factorized, one-factor-bounded regime - the
regime the scoping named as the one the A0 weld's seats
consume. No statement about the weld, any seat, or
`LayerKernelPos` is made here; nothing landed is touched.

## Kill status

K-SCHUR-RESTRICT (armed by the Q3 scoping): fires only if
positivity of the product fails even with one bounded
factor at this generality. It did NOT fire - the restricted
statement is proved below. Recorded: **armed, did not
fire**.

## Fences

NO CLAIM; dials 0/4. Zero sorrys. General measure spaces /
`L2` throughout, as in the landed module.
-/

section TensorFeature

variable {α γ δ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
  [MeasurableSpace δ] {μ : Measure α} {κ : Measure γ} {ν : Measure δ}
  [SFinite μ] [SFinite κ] [SFinite ν]
  {F : α × γ → ℂ} {G : α × δ → ℂ}

/-- The **tensor-product feature** of two feature families
`F : α × γ → ℂ` and `G : α × δ → ℂ`:
`(x, (s, t)) ↦ F (x, s) * G (x, t)`, a family on the
product feature space `(γ × δ, κ.prod ν)`. The Gram kernel
of this feature is the pointwise product of the two Gram
kernels (`gramKernel_mul`). -/
def tensorFeature (F : α × γ → ℂ) (G : α × δ → ℂ) :
    α × (γ × δ) → ℂ :=
  fun p => F (p.1, p.2.1) * G (p.1, p.2.2)

/-- The tensor-product feature in the associated
association, `(α × γ) × δ → ℂ`:
`((x, s), t) ↦ F (x, s) * G (x, t)`. This association is
where the landed quasi-measure-preserving extractions of
`IntegralKernelSchur.lean` apply directly. -/
def tensorFeatureAssoc (F : α × γ → ℂ) (G : α × δ → ℂ) :
    (α × γ) × δ → ℂ :=
  fun q => F q.1 * G (q.1.1, q.2)

/-- **The restricted `MemLp` step.** Under the restricted
hypothesis of this module's face - `F`, `G` both `L2`,
every section of `G` in `L2 ν`, and the row energy of `G`
uniformly bounded by a finite `C` - the tensor-product
feature is `MemLp 2` over `μ.prod (κ.prod ν)`.
Proof: pass to the associated feature space
`((α × γ) × δ, (μ.prod κ).prod ν)`, where Tonelli separates
the energy into the product of row energies; the bounded
row energy of `G` pulls out of the integral and the row
energy of `F` integrates to the finite `L2` energy of `F`.
Transport back along the measure-preserving associator. -/
theorem tensorFeature_memLp (hF : MemLp F 2 (μ.prod κ))
    (hG : MemLp G 2 (μ.prod ν))
    (hGsec : ∀ x, MemLp (fun t => G (x, t)) 2 ν)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hGbound : ∀ x, ∫⁻ t, ‖G (x, t)‖ₑ ^ 2 ∂ν ≤ C) :
    MemLp (tensorFeature F G) 2 (μ.prod (κ.prod ν)) := by
  have hHAESM : AEStronglyMeasurable (tensorFeatureAssoc F G)
      ((μ.prod κ).prod ν) :=
    (hF.aestronglyMeasurable.comp_quasiMeasurePreserving
      MeasureTheory.Measure.quasiMeasurePreserving_fst).mul
      (hG.aestronglyMeasurable.comp_quasiMeasurePreserving
        quasiMeasurePreserving_fst_snd)
  have hFint : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ) < ∞ := by
    rw [← eLpNorm_two_sq (μ.prod κ) hF.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hF.eLpNorm_lt_top
  have hHae : AEMeasurable
      (fun q => ‖tensorFeatureAssoc F G q‖ₑ ^ 2)
      ((μ.prod κ).prod ν) :=
    hHAESM.enorm.pow_const 2
  have hHfin2 : ∫⁻ q, ‖tensorFeatureAssoc F G q‖ₑ ^ 2
        ∂((μ.prod κ).prod ν)
      ≤ (∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ)) * C := by
    rw [MeasureTheory.lintegral_prod _ hHae]
    refine le_trans (b := ∫⁻ p, ‖F p‖ₑ ^ 2 * C ∂(μ.prod κ))
      (lintegral_mono fun p => ?_) ?_
    · have h1 : (∫⁻ t, ‖tensorFeatureAssoc F G (p, t)‖ₑ ^ 2 ∂ν)
          = ‖F p‖ₑ ^ 2 * ∫⁻ t, ‖G (p.1, t)‖ₑ ^ 2 ∂ν := by
        rw [← MeasureTheory.lintegral_const_mul'' _
          ((hGsec p.1).aestronglyMeasurable.enorm.pow_const 2)]
        refine lintegral_congr_ae (ae_of_all _ fun t => ?_)
        show ‖F p * G (p.1, t)‖ₑ ^ 2
          = ‖F p‖ₑ ^ 2 * ‖G (p.1, t)‖ₑ ^ 2
        rw [enorm_mul, mul_pow]
      rw [h1]
      gcongr
      exact hGbound p.1
    · have h2 : (∫⁻ p, ‖F p‖ₑ ^ 2 * C ∂(μ.prod κ))
          = C * ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod κ) := by
        rw [← MeasureTheory.lintegral_const_mul'' C
          (hF.aestronglyMeasurable.enorm.pow_const 2)]
        refine lintegral_congr_ae (ae_of_all _ fun p => mul_comm _ _)
      exact le_of_eq (h2.trans (mul_comm _ _))
  have hHMemLp : MemLp (tensorFeatureAssoc F G) 2
      ((μ.prod κ).prod ν) := by
    by_contra htop
    have htop' : ¬ eLpNorm (tensorFeatureAssoc F G) 2
        ((μ.prod κ).prod ν) < ∞ := htop
    have hEq : eLpNorm (tensorFeatureAssoc F G) 2
        ((μ.prod κ).prod ν) = ∞ :=
      le_antisymm le_top (not_lt.mp htop')
    have hfin : (eLpNorm (tensorFeatureAssoc F G) 2
        ((μ.prod κ).prod ν)) ^ 2 < ∞ := by
      rw [eLpNorm_two_sq _ hHAESM]
      exact lt_of_le_of_lt hHfin2 (ENNReal.mul_lt_top hFint hC)
    rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hfin
    exact (lt_irrefl _) hfin
  have hMP : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := δ)).symm
      (μ.prod (κ.prod ν)) ((μ.prod κ).prod ν) :=
    MeasureTheory.MeasurePreserving.symm _
      (MeasureTheory.measurePreserving_prodAssoc μ κ ν)
  have hcomp : tensorFeatureAssoc F G
        ∘ (MeasurableEquiv.prodAssoc
          (α := α) (β := γ) (γ := δ)).symm
      = tensorFeature F G := by
    funext ⟨x, s, t⟩
    rfl
  rw [← hcomp]
  exact hHMemLp.comp_measurePreserving hMP

/-- **The product identity.** The pointwise product of two
Gram kernels is the Gram kernel of the tensor-product
feature over the product feature space. Pointwise
everywhere, no extra hypothesis: the product integral
`integral_prod_mul` separates the double integral, and the
integrands agree by `star_mul` and commutativity. -/
theorem gramKernel_mul (p : α × α) :
    gramKernel κ F p * gramKernel ν G p
      = gramKernel (κ.prod ν) (tensorFeature F G) p := by
  obtain ⟨x, y⟩ := p
  show (∫ s, F (x, s) * star (F (y, s)) ∂κ)
        * (∫ t, G (x, t) * star (G (y, t)) ∂ν)
      = ∫ u, tensorFeature F G (x, u)
          * star (tensorFeature F G (y, u)) ∂(κ.prod ν)
  rw [← integral_prod_mul (fun s => F (x, s) * star (F (y, s)))
    (fun t => G (x, t) * star (G (y, t)))]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show (F (x, u.1) * star (F (y, u.1)))
        * (G (x, u.2) * star (G (y, u.2)))
      = tensorFeature F G (x, u) * star (tensorFeature F G (y, u))
  simp only [tensorFeature, star_mul]
  ring

/-- Transport of `PosKernel` along an equality of kernels:
positivity is a property of the kernel function itself
(the `MemLp` witness is a proof, hence irrelevant). -/
theorem posKernel_congr {K₁ K₂ : α × α → ℂ}
    {h₁ : MemLp K₁ 2 (μ.prod μ)} {h₂ : MemLp K₂ 2 (μ.prod μ)}
    (h : K₁ = K₂) (hP : PosKernel K₁ h₁) : PosKernel K₂ h₂ := by
  subst h
  exact hP

/-- **Restricted Schur product, `MemLp` form.** The
pointwise product of the two Gram kernels is an `L2`
kernel on `(μ.prod μ)`, under the restricted hypothesis. -/
theorem memLp_gramKernel_mul (hF : MemLp F 2 (μ.prod κ))
    (hG : MemLp G 2 (μ.prod ν))
    (hGsec : ∀ x, MemLp (fun t => G (x, t)) 2 ν)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hGbound : ∀ x, ∫⁻ t, ‖G (x, t)‖ₑ ^ 2 ∂ν ≤ C) :
    MemLp (fun p => gramKernel κ F p * gramKernel ν G p) 2
      (μ.prod μ) := by
  have hEq : (fun p => gramKernel κ F p * gramKernel ν G p)
      = gramKernel (κ.prod ν) (tensorFeature F G) :=
    funext fun p => gramKernel_mul p
  rw [hEq]
  exact gramKernel_memLp
    (tensorFeature_memLp hF hG hGsec hC hGbound)

/-- **Restricted Schur product theorem (Q3-3).** The
pointwise product of two Gram kernels, one of them
carrying the bounded-row-energy restriction of this
module's face, is a `PosKernel` in the registered
operator-level sense of `IntegralKernelSchur.lean` item
(1): its integral-kernel operator pairing is nonnegative
on every `f : Lp ℂ 2 μ`. Proof: the product is the Gram
kernel of the tensor-product feature (`gramKernel_mul`),
which is `L2` by the restriction (`tensorFeature_memLp`),
so the landed item (2), `posKernel_gram`, applies. -/
theorem posKernel_gram_mul (hF : MemLp F 2 (μ.prod κ))
    (hG : MemLp G 2 (μ.prod ν))
    (hGsec : ∀ x, MemLp (fun t => G (x, t)) 2 ν)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hGbound : ∀ x, ∫⁻ t, ‖G (x, t)‖ₑ ^ 2 ∂ν ≤ C) :
    PosKernel (fun p => gramKernel κ F p * gramKernel ν G p)
      (memLp_gramKernel_mul hF hG hGsec hC hGbound) :=
  posKernel_congr (funext fun p => (gramKernel_mul p).symm)
    (posKernel_gram (tensorFeature_memLp hF hG hGsec hC hGbound))

/-- The `MemLp` form with the restriction carried by the
FIRST factor instead (sections and row-energy bound on
`F`): product commutativity transports
`memLp_gramKernel_mul`. -/
theorem memLp_gramKernel_mul' (hF : MemLp F 2 (μ.prod κ))
    (hG : MemLp G 2 (μ.prod ν))
    (hFsec : ∀ x, MemLp (fun s => F (x, s)) 2 κ)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hFbound : ∀ x, ∫⁻ s, ‖F (x, s)‖ₑ ^ 2 ∂κ ≤ C) :
    MemLp (fun p => gramKernel κ F p * gramKernel ν G p) 2
      (μ.prod μ) := by
  have h := memLp_gramKernel_mul hG hF hFsec hC hFbound
  have hEq : (fun p => gramKernel ν G p * gramKernel κ F p)
      = (fun p => gramKernel κ F p * gramKernel ν G p) :=
    funext fun _ => mul_comm _ _
  rwa [hEq] at h

/-- **Restricted Schur product theorem, bound on the first
factor.** The symmetric form of `posKernel_gram_mul`. -/
theorem posKernel_gram_mul' (hF : MemLp F 2 (μ.prod κ))
    (hG : MemLp G 2 (μ.prod ν))
    (hFsec : ∀ x, MemLp (fun s => F (x, s)) 2 κ)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hFbound : ∀ x, ∫⁻ s, ‖F (x, s)‖ₑ ^ 2 ∂κ ≤ C) :
    PosKernel (fun p => gramKernel κ F p * gramKernel ν G p)
      (memLp_gramKernel_mul' hF hG hFsec hC hFbound) :=
  posKernel_congr (funext fun _ => mul_comm _ _)
    (posKernel_gram_mul hG hF hFsec hC hFbound)

end TensorFeature

end ThetLogos
