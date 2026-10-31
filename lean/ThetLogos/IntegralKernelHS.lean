import ThetLogos.HilbertSchmidt
import ThetLogos.LatticeTransferCompact
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open Filter Topology ComplexInnerProductSpace MeasureTheory
open scoped ENNReal NNReal

namespace ThetLogos

/-!
# Integral-kernel operators on L2 - SHELF-3a-ii

General-API stock, built under the SHELF fill commission
(pack: `routeb-general-scratch/pack-shelf-3a.md`, brick
3a-ii; imports the landed 3a-i module `HilbertSchmidt.lean`).
The pin re-check at dispatch (2026-10-31) re-grepped the
vendored Mathlib v4.35.0-rc3 tree: no integral-kernel
operator construction on `Lp` exists in the pin (the only
`*_kernel` integral lemmas are for probability kernels, a
different object).

Contents (pack 3a-ii), for arbitrary measure spaces
`(α, μ)`, `(β, ν)` with `SFinite` measures (probability is
NOT assumed) and a kernel `K : α × β → ℂ` with
`MemLp K 2 (μ.prod ν)`:

1. the operator `integralKernelOp hK : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ`,
   `(integralKernelOp hK f) x =ᵐ ∫ y, K (x, y) * f y ∂ν`
   (output variable is the FIRST kernel variable, the
   `μ`-variable; used consistently throughout);
2. the form identity: the inner product against
   `integralKernelOp hK f` is the product-measure integral
   of the kernel pairing (and its iterated form);
3. the Hilbert-Schmidt bound
   `‖integralKernelOp hK‖ ≤ ‖K‖₂`, where
   `‖K‖₂ := (eLpNorm K 2 (μ.prod ν)).toReal`;
4. the HS identity (headline): `integralKernelOp hK` is
   Hilbert-Schmidt in 3a-i's sense and, for every Hilbert
   basis `(b i)` of `Lp ℂ 2 ν`,
   `∑' i, ‖integralKernelOp hK (b i)‖ ^ 2 = ‖K‖₂ ^ 2`
   - HS norm = L2 norm of the kernel, as an equality;
5. compactness of `integralKernelOp hK`, via (4) + 3a-i;
6. the specialization check against Q12's seat operator
   `kernelOp` in `LatticeTransferCompact.lean`: at the seat
   data the two operators are equal (proved, last section).

Named seam (pack 3a-ii item 6, pre-named in the pack):
P-KERNEL-CONVERSE. The converse / kernel extraction -
every Hilbert-Schmidt operator `Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ`
arises as `integralKernelOp hK` for some kernel `K` - is
NOT landed in this module. The correspondence is therefore
NOT a bijection and is nowhere called one: what lands is
the forward construction, its HS isometry identity (4),
and compactness (5).

This module is the first half of the F2 fence's
prerequisite stock: it does NOT retire the F2 fence (that
is SHELF-3b's, gated on this brick plus the upstream
`reflSite` duplicate).

NO CLAIM; dials 0/4. General-API stock only: no statement
below mentions `osSpace`, `sliceMeasure`, `sliceLinks` or
the `(G, ρ, β, N)` package, except the final specialization
section, whose whole point is the comparison at that seat.
-/

/-! ## The section map on finite measure spaces

For the Tonelli step of the HS identity over a general
Hilbert basis, we need the section map
`x ↦ (section of `M` at `x`, as an `Lp` element)` to be
a.e.-strongly measurable, so that its range lies in a
separable subspace. On finite measure spaces this is
proved here by approximation: separated simple tensors
are dense in `L2` of the product (a pi-lambda argument
for indicators plus density of simple functions), and
`L2`-convergence of kernels gives a.e. convergence of
the section maps. -/

section FiniteSectionMap

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Squared seminorm of a tensor factor, finite-measure
version (the same Tonelli separation as in the general
section below). -/
theorem eLpNorm_tensor_sq_fin (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2 (μ.prod ν)) ^ 2
      = ((eLpNorm (⇑g) 2 μ) * (eLpNorm (⇑f) 2 ν)) ^ 2 := by
  have hpt : ∀ y : ℂ, ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
    intro y
    simp [enorm, ENNReal.ofReal_pow]
  have hgA : AEStronglyMeasurable (⇑g) μ :=
    MeasureTheory.Lp.aestronglyMeasurable g
  have hfA : AEStronglyMeasurable (⇑f) ν :=
    MeasureTheory.Lp.aestronglyMeasurable f
  have hV : AEStronglyMeasurable
      (fun p => star (⇑g p.1) * ⇑f p.2) (μ.prod ν) :=
    (continuous_star.comp_aestronglyMeasurable hgA.comp_fst).mul
      hfA.comp_snd
  rw [eLpNorm_two_sq _ hV, mul_pow, eLpNorm_two_sq _ hgA,
    eLpNorm_two_sq _ hfA]
  have hAM : AEMeasurable
      (fun p => ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2) (μ.prod ν) :=
    ((hgA.aemeasurable.comp_fst).enorm.pow_const 2).mul
      ((hfA.aemeasurable.comp_snd).enorm.pow_const 2)
  calc ∫⁻ p, ‖star (⇑g p.1) * ⇑f p.2‖ₑ ^ 2 ∂(μ.prod ν)
      = ∫⁻ p, ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2 ∂(μ.prod ν) :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
          show ‖star (⇑g p.1) * ⇑f p.2‖ₑ ^ 2
            = ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2
          rw [hpt, hpt (⇑g p.1), hpt (⇑f p.2), ← ENNReal.ofReal_mul
            (by positivity)]
          congr 1
          rw [norm_mul, norm_star, mul_pow])
    _ = (∫⁻ x, ‖⇑g x‖ₑ ^ 2 ∂μ) * (∫⁻ y, ‖⇑f y‖ₑ ^ 2 ∂ν) := by
        rw [MeasureTheory.lintegral_prod _ hAM]
        exact MeasureTheory.lintegral_lintegral_mul
          (hgA.aemeasurable.enorm.pow_const 2)
          (hfA.aemeasurable.enorm.pow_const 2)

/-- Tensor factors are `L2` on the product of finite
measure spaces. -/
theorem memLp_tensor_fin (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    MemLp (fun p => star (⇑g p.1) * ⇑f p.2) 2 (μ.prod ν) := by
  have hsq := eLpNorm_tensor_sq_fin g f
  show eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2 (μ.prod ν) < ∞
  by_contra htop
  push Not at htop
  have hEq : eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
      (μ.prod ν) = ∞ := le_antisymm le_top htop
  rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  have hfin : ((eLpNorm (⇑g) 2 μ) * (eLpNorm (⇑f) 2 ν)) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.mul_ne_top
      (MeasureTheory.Lp.memLp g).ne (MeasureTheory.Lp.memLp f).ne)
  exact hfin hsq.symm

/-- The tensor product of two `Lp` elements, as an `Lp`
element of the product space. -/
noncomputable def tensorLp (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    Lp ℂ 2 (μ.prod ν) :=
  (memLp_tensor_fin g f).toLp (fun p => star (⇑g p.1) * ⇑f p.2)

theorem coeFn_tensorLp (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    ⇑(tensorLp g f)
      =ᵐ[μ.prod ν] (fun p => star (⇑g p.1) * ⇑f p.2) :=
  MemLp.coeFn_toLp _

/-- The section map: `sectionLp M x` is the section of
the kernel `M` at `x`, as an `Lp` element (and `0` where
the section is not in `L2`). -/
noncomputable def sectionLp (M : α × β → ℂ) (x : α) : Lp ℂ 2 ν := by
  classical
  exact if h : MemLp (fun y => M (x, y)) 2 ν then h.toLp _ else 0

theorem sectionLp_eq_of_memLp {M : α × β → ℂ} {x : α}
    (h : MemLp (fun y => M (x, y)) 2 ν) :
    sectionLp M x = h.toLp (fun y => M (x, y)) := by
  classical
  exact dif_pos h

/-- Sections of an `L2` kernel on finite measure spaces
are `L2`, a.e. in the first variable. -/
theorem memLp_section_ae_fin {M : α × β → ℂ}
    (hM : MemLp M 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => M (x, y)) 2 ν := by
  have hfin : (∫⁻ p, ‖M p‖ₑ ^ 2 ∂(μ.prod ν)) ≠ ∞ := by
    have h := eLpNorm_two_sq (μ.prod ν) hM.aestronglyMeasurable
    rw [← h]
    exact ENNReal.pow_ne_top (hM.eLpNorm_lt_top).ne
  have hAM : AEMeasurable (fun p => ‖M p‖ₑ ^ 2) (μ.prod ν) := by
    simp only [pow_two]
    exact (hM.aestronglyMeasurable.aemeasurable.enorm).mul
      hM.aestronglyMeasurable.aemeasurable.enorm
  rw [MeasureTheory.lintegral_prod _ hAM] at hfin
  have hae : ∀ᵐ x ∂μ, (∫⁻ y, ‖M (x, y)‖ₑ ^ 2 ∂ν) < ∞ :=
    ae_lt_top' hAM.lintegral_prod_right' hfin
  filter_upwards [hM.aestronglyMeasurable.prodMk_left, hae]
    with x hx hsec
  show eLpNorm (fun y => M (x, y)) 2 ν < ∞
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by simp) hx]
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
  rw [h2]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  exact hsec.ne

/-- The section of a tensor at `x` is the scalar multiple
`star (g x) • f`. -/
theorem sectionLp_tensor (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) (x : α) :
    sectionLp (fun p => star (⇑g p.1) * ⇑f p.2) x
      = star (⇑g x) • f := by
  have hsec : MemLp (fun y => star (⇑g x) * ⇑f y) 2 ν :=
    MemLp.const_mul (MeasureTheory.Lp.memLp f) (star (⇑g x))
  rw [sectionLp_eq_of_memLp hsec]
  apply MeasureTheory.Lp.ext
  calc ⇑(hsec.toLp (fun y => star (⇑g x) * ⇑f y))
      =ᵐ[ν] (fun y => star (⇑g x) * ⇑f y) := MemLp.coeFn_toLp _
    _ =ᵐ[ν] ⇑(star (⇑g x) • f) := by
        filter_upwards [MeasureTheory.Lp.coeFn_smul (star (⇑g x)) f]
          with y hy
        rw [hy]
        rfl

/-- The closure of the span of the separated tensors. -/
noncomputable def tensorSpanClosure : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
  (Submodule.span ℂ (Set.range fun (q : Lp ℂ 2 μ × Lp ℂ 2 ν) =>
    tensorLp q.1 q.2)).topologicalClosure

/-- The indicator of a rectangle is the tensor of the
indicators. -/
theorem indicatorConstLp_prod {A : Set α} {B : Set β}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) (hA.prod hB)
        (measure_ne_top (μ.prod ν) _) (1 : ℂ)
      = tensorLp (MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          hA (measure_ne_top μ _) (1 : ℂ))
        (MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          hB (measure_ne_top ν _) (1 : ℂ)) := by
  apply MeasureTheory.Lp.ext
  have hpt : ∀ p : α × β,
      star ((A.indicator (fun _ => (1 : ℂ))) p.1)
          * (B.indicator (fun _ => (1 : ℂ))) p.2
        = (A ×ˢ B).indicator (fun _ => (1 : ℂ)) p := by
    intro p
    by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2,
        Set.mem_prod]
  have hmeas : MeasurableSet {p : α × β |
      star (⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hA
          (measure_ne_top μ _) (1 : ℂ)) p.1)
        * ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hB
          (measure_ne_top ν _) (1 : ℂ)) p.2
        = (A ×ˢ B).indicator (fun _ => (1 : ℂ)) p} := by
    apply StronglyMeasurable.measurableSet_eq_fun
    · exact (continuous_star.comp_stronglyMeasurable
        ((MeasureTheory.Lp.stronglyMeasurable _).comp_fst)).mul
        ((MeasureTheory.Lp.stronglyMeasurable _).comp_snd)
    · exact (measurable_const.indicator (hA.prod hB)).stronglyMeasurable
  have hae : (fun p =>
        star (⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hA
            (measure_ne_top μ _) (1 : ℂ)) p.1)
          * ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hB
            (measure_ne_top ν _) (1 : ℂ)) p.2)
      =ᵐ[μ.prod ν] (A ×ˢ B).indicator (fun _ => (1 : ℂ)) := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).mpr ?_
    filter_upwards [MeasureTheory.indicatorConstLp_coeFn
      (μ := μ) (p := (2 : ℝ≥0∞)) (s := A) (hs := hA)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ))] with x hx
    filter_upwards [MeasureTheory.indicatorConstLp_coeFn
      (μ := ν) (p := (2 : ℝ≥0∞)) (s := B) (hs := hB)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ))] with y hy
    show star (⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hA
        (measure_ne_top μ _) (1 : ℂ)) x)
      * ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hB
        (measure_ne_top ν _) (1 : ℂ)) y
      = (A ×ˢ B).indicator (fun _ => (1 : ℂ)) (x, y)
    rw [hx, hy]
    exact hpt (x, y)
  calc ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) (hA.prod hB)
          (measure_ne_top (μ.prod ν) _) (1 : ℂ))
      =ᵐ[μ.prod ν] (A ×ˢ B).indicator (fun _ => (1 : ℂ)) :=
        MeasureTheory.indicatorConstLp_coeFn
    _ =ᵐ[μ.prod ν] fun p =>
          star (⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hA
              (measure_ne_top μ _) (1 : ℂ)) p.1)
            * ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hB
              (measure_ne_top ν _) (1 : ℂ)) p.2 :=
        hae.symm
    _ =ᵐ[μ.prod ν] ⇑(tensorLp (MeasureTheory.indicatorConstLp
          (2 : ℝ≥0∞) hA (measure_ne_top μ _) (1 : ℂ))
        (MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hB
          (measure_ne_top ν _) (1 : ℂ))) :=
        (coeFn_tensorLp _ _).symm

/-- The indicator of a complement is the difference of
the indicators of the whole space and of the set. -/
theorem indicatorConstLp_compl {E : Set (α × β)}
    (hE : MeasurableSet E) :
    MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE.compl
        (measure_ne_top (μ.prod ν) _) (1 : ℂ)
      = MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ)
        - MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE
          (measure_ne_top (μ.prod ν) _) (1 : ℂ) := by
  apply MeasureTheory.Lp.ext
  have hpt : (Set.univ.indicator (fun _ => (1 : ℂ))
        - E.indicator (fun _ => (1 : ℂ)))
      = Eᶜ.indicator (fun _ => (1 : ℂ)) := by
    funext p
    by_cases hp : p ∈ E <;>
      simp [Pi.sub_apply, Set.indicator_of_mem, Set.indicator_of_notMem,
        hp, Set.mem_compl_iff]
  calc ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE.compl
          (measure_ne_top (μ.prod ν) _) (1 : ℂ))
      =ᵐ[μ.prod ν] Eᶜ.indicator (fun _ => (1 : ℂ)) :=
        MeasureTheory.indicatorConstLp_coeFn
    _ =ᵐ[μ.prod ν] (Set.univ.indicator (fun _ => (1 : ℂ))
          - E.indicator (fun _ => (1 : ℂ))) :=
        Filter.EventuallyEq.of_eq hpt.symm
    _ =ᵐ[μ.prod ν] ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
            MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ)
          - MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE
            (measure_ne_top (μ.prod ν) _) (1 : ℂ)) := by
        have h1 : ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
              MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ)
            - MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE
              (measure_ne_top (μ.prod ν) _) (1 : ℂ))
            =ᵐ[μ.prod ν] ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ))
              - ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE
                (measure_ne_top (μ.prod ν) _) (1 : ℂ)) :=
          MeasureTheory.Lp.coeFn_sub _ _
        have h2 : ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ))
              - ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE
                (measure_ne_top (μ.prod ν) _) (1 : ℂ))
            =ᵐ[μ.prod ν] (Set.univ.indicator (fun _ => (1 : ℂ))
              - E.indicator (fun _ => (1 : ℂ))) :=
          MeasureTheory.indicatorConstLp_coeFn.sub
            MeasureTheory.indicatorConstLp_coeFn
        exact (h1.trans h2).symm

/-- Every indicator of a measurable set of the product
lies in the closure of the span of the separated
tensors (pi-lambda argument). -/
theorem indicatorConstLp_mem_tensorSpanClosure {E : Set (α × β)}
    (hE : MeasurableSet E) :
    MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hE
        (measure_ne_top (μ.prod ν) _) (1 : ℂ) ∈ tensorSpanClosure := by
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·)
      {s : Set α | MeasurableSet s} {t : Set β | MeasurableSet t}) :=
    isPiSystem_prod
  have key : ∀ t (ht : MeasurableSet t),
      MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) ht
          (measure_ne_top (μ.prod ν) _) (1 : ℂ) ∈ tensorSpanClosure := by
    apply MeasurableSpace.induction_on_inter
      (C := fun (t : Set (α × β)) (ht : MeasurableSet t) =>
        MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) ht
          (measure_ne_top (μ.prod ν) _) (1 : ℂ) ∈ tensorSpanClosure)
      (s := Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s}
        {t : Set β | MeasurableSet t})
      generateFrom_prod.symm hpi
    · show MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          MeasurableSet.empty (measure_ne_top (μ.prod ν) _) (1 : ℂ)
          ∈ tensorSpanClosure
      have hempty : MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          MeasurableSet.empty (measure_ne_top (μ.prod ν) _) (1 : ℂ)
          = (0 : Lp ℂ 2 (μ.prod ν)) :=
        MeasureTheory.indicatorConstLp_empty
      rw [hempty]
      exact zero_mem _
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      show MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) (hA.prod hB)
          (measure_ne_top (μ.prod ν) _) (1 : ℂ) ∈ tensorSpanClosure
      rw [indicatorConstLp_prod hA hB]
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨(MeasureTheory.indicatorConstLp
          (2 : ℝ≥0∞) hA (measure_ne_top μ _) (1 : ℂ),
          MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hB
          (measure_ne_top ν _) (1 : ℂ)), rfl⟩)
    · intro t ht iht
      show MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) ht.compl
          (measure_ne_top (μ.prod ν) _) (1 : ℂ) ∈ tensorSpanClosure
      rw [indicatorConstLp_compl ht]
      apply sub_mem _ iht
      have huniv : (Set.univ : Set (α × β))
          = Set.univ ×ˢ Set.univ := Set.univ_prod_univ.symm
      have hmem : MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          (MeasurableSet.univ.prod MeasurableSet.univ)
            (measure_ne_top (μ.prod ν) _) (1 : ℂ) ∈ tensorSpanClosure := by
        rw [indicatorConstLp_prod MeasurableSet.univ
          MeasurableSet.univ]
        exact Submodule.le_topologicalClosure _
          (Submodule.subset_span ⟨(MeasureTheory.indicatorConstLp
            (2 : ℝ≥0∞) MeasurableSet.univ (measure_ne_top μ _)
              (1 : ℂ), MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
            MeasurableSet.univ (measure_ne_top ν _) (1 : ℂ)), rfl⟩)
      have heq : MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
            MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ)
          = MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
            (MeasurableSet.univ.prod MeasurableSet.univ)
              (measure_ne_top (μ.prod ν) _) (1 : ℂ) := by
        apply MeasureTheory.Lp.ext
        calc ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                MeasurableSet.univ (measure_ne_top (μ.prod ν) _) (1 : ℂ))
            =ᵐ[μ.prod ν] Set.univ.indicator (fun _ => (1 : ℂ)) :=
              MeasureTheory.indicatorConstLp_coeFn
          _ =ᵐ[μ.prod ν] (Set.univ ×ˢ Set.univ).indicator
                (fun _ => (1 : ℂ)) :=
              Filter.EventuallyEq.of_eq (by rw [Set.univ_prod_univ])
          _ =ᵐ[μ.prod ν] ⇑(MeasureTheory.indicatorConstLp
                (2 : ℝ≥0∞) (MeasurableSet.univ.prod
                  MeasurableSet.univ) (measure_ne_top (μ.prod ν) _) (1 : ℂ)) :=
              MeasureTheory.indicatorConstLp_coeFn.symm
      rw [heq]
      exact hmem
    · intro f hdisj hfmeas hfmem
      classical
      set U : ℕ → Set (α × β) := fun N =>
        ⋃ n ∈ Finset.range N, f n with hU
      have hUmeas : ∀ N, MeasurableSet (U N) := fun N =>
        MeasurableSet.biUnion (Finset.range N).countable_toSet
          (fun n _ => hfmeas n)
      have hind : ∀ (s t : Set (α × β)) (hs : MeasurableSet s)
          (ht : MeasurableSet t), s = t →
          MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) hs
              (measure_ne_top (μ.prod ν) _) (1 : ℂ)
            = MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) ht
              (measure_ne_top (μ.prod ν) _) (1 : ℂ) := by
        intro s t hs ht hst
        subst hst
        rfl
      have hUmem : ∀ N, MeasureTheory.indicatorConstLp
          (2 : ℝ≥0∞) (hUmeas N) (measure_ne_top (μ.prod ν) _) (1 : ℂ)
            ∈ tensorSpanClosure := by
        intro N
        induction N with
        | zero =>
          have hU0 : U 0 = ∅ := by
            simp [hU]
          have : MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
              (hUmeas 0) (measure_ne_top (μ.prod ν) _) (1 : ℂ) = 0 := by
            apply MeasureTheory.Lp.ext
            calc ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                    (hUmeas 0) (measure_ne_top (μ.prod ν) _) (1 : ℂ))
                =ᵐ[μ.prod ν] (U 0).indicator (fun _ => (1 : ℂ)) :=
                  MeasureTheory.indicatorConstLp_coeFn
              _ =ᵐ[μ.prod ν] (0 : α × β → ℂ) :=
                  Filter.EventuallyEq.of_eq (by
                    rw [hU0]; simp only [Set.indicator_empty'])
              _ =ᵐ[μ.prod ν] ⇑(0 : Lp ℂ 2 (μ.prod ν)) :=
                  (MeasureTheory.Lp.coeFn_zero ℂ (2 : ℝ≥0∞)
                    (μ.prod ν)).symm
          rw [this]
          exact zero_mem _
        | succ N ih =>
          have hdisjN : Disjoint (U N) (f N) := by
            rw [hU]
            refine Set.disjoint_iUnion_left.mpr fun n =>
              Set.disjoint_iUnion_left.mpr fun hn => ?_
            have hnN : n ≠ N := by
              have h2 : n ∈ Finset.range N := Finset.mem_coe.mp hn
              rw [Finset.mem_range] at h2
              omega
            exact hdisj hnN
          have hUeq : U (N + 1) = U N ∪ f N := by
            ext p
            simp only [hU, Set.mem_iUnion, Set.mem_iUnion₂,
              Finset.mem_coe, Finset.mem_range, exists_prop,
              Set.mem_union]
            constructor
            · rintro ⟨n, hn, hp⟩
              by_cases hlt : n < N
              · exact Or.inl ⟨n, hlt, hp⟩
              · have hnN : n = N := by omega
                exact Or.inr (hnN ▸ hp)
            · rintro (⟨n, hn, hp⟩ | hp)
              · exact ⟨n, by omega, hp⟩
              · exact ⟨N, by omega, hp⟩
          have hsum : MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                (hUmeas (N + 1)) (measure_ne_top (μ.prod ν) _) (1 : ℂ)
              = MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                  (hUmeas N) (measure_ne_top (μ.prod ν) _) (1 : ℂ)
                + MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
                  (hfmeas N) (measure_ne_top (μ.prod ν) _) (1 : ℂ) := by
            rw [hind (U (N + 1)) (U N ∪ f N) (hUmeas (N + 1))
              ((hUmeas N).union (hfmeas N)) hUeq]
            exact MeasureTheory.indicatorConstLp_disjoint_union
              (μ := μ.prod ν) (p := (2 : ℝ≥0∞)) (hs := hUmeas N)
              (ht := hfmeas N) (hμs := measure_ne_top (μ.prod ν) _)
              (hμt := measure_ne_top (μ.prod ν) _) (hst := hdisjN)
              (c := (1 : ℂ))
          rw [hsum]
          exact add_mem ih (hfmem N)
      haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
      have hlim : Filter.Tendsto (fun N =>
            MeasureTheory.indicatorConstLp (2 : ℝ≥0∞) (hUmeas N)
              (measure_ne_top (μ.prod ν) _) (1 : ℂ)) Filter.atTop
          (nhds (MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
            (MeasurableSet.iUnion hfmeas) (measure_ne_top (μ.prod ν) _)
            (1 : ℂ))) := by
        apply MeasureTheory.tendsto_indicatorConstLp_set
          (μ := μ.prod ν) (p := (2 : ℝ≥0∞)) (ht := hUmeas)
          (hμt := fun _ => measure_ne_top (μ.prod ν) _) (by norm_num)
        have hΔ : ∀ N, (μ.prod ν) (symmDiff (U N) (⋃ n, f n))
            = (μ.prod ν) (⋃ n, f (N + n)) := by
          intro N
          congr 1
          ext p
          simp only [hU, Set.mem_symmDiff, Set.mem_iUnion,
            Set.mem_iUnion₂, Finset.mem_coe, Finset.mem_range,
            exists_prop]
          constructor
          · rintro (⟨⟨j, hjN, hj⟩, hnp⟩ | ⟨⟨j, hj⟩, hnp⟩)
            · exact absurd ⟨j, hj⟩ hnp
            · have hjNN : N ≤ j := by
                by_contra hlt
                push Not at hlt
                exact hnp ⟨j, hlt, hj⟩
              refine ⟨j - N, ?_⟩
              rw [Nat.add_sub_cancel' hjNN]
              exact hj
          · rintro ⟨n, hn⟩
            right
            refine ⟨⟨N + n, hn⟩, ?_⟩
            rintro ⟨m, hm, hpm⟩
            have hmN : m ≠ N + n := by omega
            exact (Set.disjoint_left.mp (hdisj hmN)) hpm hn
        have hAnti : Antitone (fun N => ⋃ n, f (N + n)) := by
          intro a b hab
          apply Set.iUnion_subset
          intro n
          have hidx : a + (n + (b - a)) = b + n := by omega
          rw [← hidx]
          exact Set.subset_iUnion (fun m => f (a + m)) (n + (b - a))
        have hInter : ⋂ N, (⋃ n, f (N + n)) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro p hp
          have hsub : ∀ N, (⋂ N, (⋃ n, f (N + n)))
              ⊆ ⋃ n, f (N + n) :=
            fun N => Set.iInter_subset _ N
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hsub 0 hp)
          have hj' : p ∈ f j := Nat.zero_add j ▸ hj
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hsub (j + 1) hp)
          exact (Set.disjoint_left.mp (hdisj (show j ≠ j + 1 + n
            by omega))) hj' hn
        have h := MeasureTheory.tendsto_measure_iInter_atTop
          (μ := μ.prod ν) (s := fun N => ⋃ n, f (N + n))
          (fun N => (MeasurableSet.iUnion fun n =>
            hfmeas (N + n)).nullMeasurableSet) hAnti
          ⟨0, measure_ne_top _ _⟩
        rw [hInter, MeasureTheory.measure_empty] at h
        exact Filter.Tendsto.congr (fun N => (hΔ N).symm) h
      have hgoal : MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
            (MeasurableSet.iUnion hfmeas) (measure_ne_top (μ.prod ν) _)
            (1 : ℂ) ∈ tensorSpanClosure := by
        exact (Submodule.isClosed_topologicalClosure
          (Submodule.span ℂ (Set.range fun
            (q : Lp ℂ 2 μ × Lp ℂ 2 ν) => tensorLp q.1 q.2))).mem_of_tendsto
          hlim (Filter.Eventually.of_forall hUmem)
      exact hgoal
  exact key E hE

/-- A simple function on the product, written as a sum
of fiber indicators. -/
theorem simpleFunc_eq_sum_indicator (s : SimpleFunc (α × β) ℂ) :
    ∀ p : α × β, s p
      = ∑ y ∈ s.range, ((Set.preimage (⇑s) {y}).indicator (fun _ => y)) p := by
  intro p
  rw [Finset.sum_eq_single (s p)]
  · exact (Set.indicator_of_mem (by
      simp [Set.mem_preimage]) (fun _ => s p)).symm
  · intro y _ hne
    apply Set.indicator_of_notMem
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fun h => hne h.symm
  · intro hmem
    exfalso
    exact hmem (SimpleFunc.mem_range.mpr ⟨p, rfl⟩)

/-- Simple functions on the product have `L2` sections
in the closure of the span of the separated tensors. -/
theorem simpleFunc_mem_tensorSpanClosure {v : Lp ℂ 2 (μ.prod ν)}
    (hv : v ∈ MeasureTheory.Lp.simpleFunc ℂ 2 (μ.prod ν)) :
    v ∈ tensorSpanClosure := by
  obtain ⟨s, hs⟩ := hv
  have hsM : MemLp (⇑s) 2 (μ.prod ν) := by
    have hsum : ∀ t : Finset ℂ,
        MemLp (∑ y ∈ t, (Set.preimage (⇑s) {y}).indicator (fun _ => y))
          2 (μ.prod ν) := by
      intro t
      induction t using Finset.induction with
      | empty => simpa using (MeasureTheory.memLp_zero (E := ℂ)
          (p := (2 : ℝ≥0∞)) (μ := μ.prod ν))
      | insert y t hy ih =>
        rw [Finset.sum_insert hy]
        exact (MeasureTheory.memLp_indicator_const (2 : ℝ≥0∞)
          (s.measurableSet_fiber y).nullMeasurableSet y
          (Or.inr (measure_ne_top _ _))).add ih
    have h := hsum s.range
    show eLpNorm (⇑s) 2 (μ.prod ν) < ∞
    rw [eLpNorm_congr_ae (show (⇑s : (α × β) → ℂ)
      =ᵐ[μ.prod ν] (∑ y ∈ s.range,
        (Set.preimage (⇑s) {y}).indicator (fun _ => y)) from
      Filter.EventuallyEq.of_eq (funext fun p => by
        rw [Finset.sum_apply]
        exact simpleFunc_eq_sum_indicator s p))]
    exact h
  have hvv : v = hsM.toLp (⇑s) := by
    apply MeasureTheory.Lp.ext
    calc ⇑v =ᵐ[μ.prod ν] ⇑s := by
          have h1 : ⇑(AEEqFun.mk (⇑s) s.aestronglyMeasurable)
              =ᵐ[μ.prod ν] ⇑s := AEEqFun.coeFn_mk _ _
          rw [hs] at h1
          exact h1
      _ =ᵐ[μ.prod ν] ⇑(hsM.toLp (⇑s)) := (MemLp.coeFn_toLp _).symm
  rw [hvv]
  have hdecomp : hsM.toLp (⇑s)
      = ∑ y ∈ s.range, y • MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
          (s.measurableSet_fiber y) (measure_ne_top _ _) (1 : ℂ) := by
    apply MeasureTheory.Lp.ext
    calc ⇑(hsM.toLp (⇑s)) =ᵐ[μ.prod ν] ⇑s := MemLp.coeFn_toLp _
      _ =ᵐ[μ.prod ν] ∑ y ∈ s.range,
            ((Set.preimage (⇑s) {y}).indicator (fun _ => y)) :=
          Filter.EventuallyEq.of_eq (funext fun p => by
            rw [Finset.sum_apply]
            exact simpleFunc_eq_sum_indicator s p)
      _ =ᵐ[μ.prod ν] ∑ y ∈ s.range,
            y • ⇑(MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
              (s.measurableSet_fiber y) (measure_ne_top _ _)
              (1 : ℂ)) :=
          eventuallyEq_sum fun y _ => by
            have hA : ((Set.preimage (⇑s) {y}).indicator
                  (fun _ => y))
                = y • ((Set.preimage (⇑s) {y}).indicator
                  (fun _ => (1 : ℂ))) := by
              funext p
              by_cases hp : p ∈ Set.preimage (⇑s) {y} <;>
                simp [Set.indicator_of_mem, Set.indicator_of_notMem,
                  hp, Pi.smul_apply, smul_eq_mul]
            have hB : (y • ⇑(MeasureTheory.indicatorConstLp
                  (2 : ℝ≥0∞) (s.measurableSet_fiber y)
                  (measure_ne_top _ _) (1 : ℂ)))
                =ᵐ[μ.prod ν] y • ((Set.preimage (⇑s) {y}).indicator
                  (fun _ => (1 : ℂ))) :=
              Filter.EventuallyEq.smul
                (Filter.EventuallyEq.refl (MeasureTheory.ae (μ.prod ν))
                  (fun _ => y))
                MeasureTheory.indicatorConstLp_coeFn
            exact (Filter.EventuallyEq.of_eq hA).trans hB.symm
      _ =ᵐ[μ.prod ν] ⇑(∑ y ∈ s.range, y •
            MeasureTheory.indicatorConstLp (2 : ℝ≥0∞)
              (s.measurableSet_fiber y) (measure_ne_top _ _)
              (1 : ℂ)) :=
          ((MeasureTheory.Lp.coeFn_finsetSum _ _).trans
            (eventuallyEq_sum fun y _ =>
              MeasureTheory.Lp.coeFn_smul y _)).symm
  rw [hdecomp]
  exact sum_mem (fun y _ => Submodule.smul_mem _ _
    (indicatorConstLp_mem_tensorSpanClosure (s.measurableSet_fiber y)))

/-- Every `L2` kernel's `Lp` class lies in the closure of
the span of the separated tensors: the tensors are dense. -/
theorem memLp_toLp_mem_tensorSpanClosure {M : α × β → ℂ}
    (hM : MemLp M 2 (μ.prod ν)) :
    hM.toLp M ∈ tensorSpanClosure := by
  have hsub : (MeasureTheory.Lp.simpleFunc ℂ 2
        (μ.prod ν)).carrier
      ⊆ ((tensorSpanClosure : Submodule ℂ (Lp ℂ 2 (μ.prod ν)))
        : Set (Lp ℂ 2 (μ.prod ν))) := by
    intro v hv
    exact simpleFunc_mem_tensorSpanClosure hv
  have hclosed : IsClosed
      ((tensorSpanClosure : Submodule ℂ (Lp ℂ 2 (μ.prod ν)))
        : Set (Lp ℂ 2 (μ.prod ν))) :=
    Submodule.isClosed_topologicalClosure _
  have hclosure : closure (MeasureTheory.Lp.simpleFunc ℂ 2
        (μ.prod ν)).carrier
      ⊆ ((tensorSpanClosure : Submodule ℂ (Lp ℂ 2 (μ.prod ν)))
        : Set (Lp ℂ 2 (μ.prod ν))) :=
    closure_minimal hsub hclosed
  have hdense : DenseRange ((↑) : (MeasureTheory.Lp.simpleFunc
      ℂ 2 (μ.prod ν)) → Lp ℂ 2 (μ.prod ν)) :=
    MeasureTheory.Lp.simpleFunc.denseRange (E := ℂ) (p := 2)
      (μ := μ.prod ν) (by norm_num)
  have hmem : hM.toLp M ∈ closure (Set.range ((↑) :
      (MeasureTheory.Lp.simpleFunc ℂ 2 (μ.prod ν))
        → Lp ℂ 2 (μ.prod ν))) := hdense _
  have hrange : Set.range ((↑) : (MeasureTheory.Lp.simpleFunc
        ℂ 2 (μ.prod ν)) → Lp ℂ 2 (μ.prod ν))
      = (MeasureTheory.Lp.simpleFunc ℂ 2 (μ.prod ν)).carrier := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at hmem
  exact SetLike.mem_coe.mp (hclosure hmem)

/-- A sequence of finite tensor combinations converging
to the kernel's `Lp` class at a geometric rate. -/
theorem exists_tensor_approx_seq {M : α × β → ℂ}
    (hM : MemLp M 2 (μ.prod ν)) :
    ∃ v : ℕ → Lp ℂ 2 (μ.prod ν),
      (∀ n, v n ∈ Submodule.span ℂ (Set.range
        fun (q : Lp ℂ 2 μ × Lp ℂ 2 ν) => tensorLp q.1 q.2)) ∧
      (∀ n, dist (hM.toLp M) (v n) < (1 / 2 : ℝ) ^ n) := by
  have hmem : hM.toLp M ∈ tensorSpanClosure :=
    memLp_toLp_mem_tensorSpanClosure hM
  have hmem' : hM.toLp M ∈ closure ↑(Submodule.span ℂ
      (Set.range fun (q : Lp ℂ 2 μ × Lp ℂ 2 ν) =>
        tensorLp q.1 q.2)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  have hchoice : ∀ n : ℕ, ∃ w ∈ Submodule.span ℂ (Set.range
        fun (q : Lp ℂ 2 μ × Lp ℂ 2 ν) => tensorLp q.1 q.2),
      dist (hM.toLp M) w < (1 / 2 : ℝ) ^ n := by
    intro n
    have hε : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    obtain ⟨w, hw, hdist⟩ :=
      Metric.mem_closure_iff.mp hmem' _ hε
    exact ⟨w, hw, hdist⟩
  choose v hv hvdist using hchoice
  exact ⟨v, hv, hvdist⟩

/-- Sections of a tensor-span element are the corresponding finite
tensor sums, for almost every `x`. -/
theorem sectionLp_eq_sum_of_mem_span {v : Lp ℂ 2 (μ.prod ν)}
    (hv : v ∈ Submodule.span ℂ (Set.range
      fun (q : Lp ℂ 2 μ × Lp ℂ 2 ν) => tensorLp q.1 q.2)) :
    ∃ c : (Lp ℂ 2 μ × Lp ℂ 2 ν) →₀ ℂ,
      ∀ᵐ x ∂μ, sectionLp (⇑v) x
        = ∑ q ∈ c.support, c q • (star (⇑q.1 x) • q.2) := by
  obtain ⟨c, hc⟩ :=
    (Finsupp.mem_span_range_iff_exists_finsupp).mp hv
  refine ⟨c, ?_⟩
  have hsum_el : v = ∑ q ∈ c.support, c q • tensorLp q.1 q.2 :=
    hc.symm
  have hcoe : ⇑v =ᵐ[μ.prod ν] fun p => ∑ q ∈ c.support,
      c q • (star (⇑q.1 p.1) * ⇑q.2 p.2) := by
    rw [hsum_el]
    refine (MeasureTheory.Lp.coeFn_finsetSum _ _).trans ?_
    have step2 : (∑ q ∈ c.support, ⇑(c q • tensorLp q.1 q.2))
        =ᵐ[μ.prod ν] ∑ q ∈ c.support,
          (fun p => c q • (star (⇑q.1 p.1) * ⇑q.2 p.2)) := by
      apply eventuallyEq_sum
      intro q _
      refine (MeasureTheory.Lp.coeFn_smul (c q) _).trans ?_
      exact (coeFn_tensorLp q.1 q.2).mono fun p hp => by
        rw [Pi.smul_apply, hp]
    refine step2.trans ?_
    apply Filter.EventuallyEq.of_eq
    funext p
    rw [Finset.sum_apply]
  have hSM : StronglyMeasurable (fun p : α × β =>
      ∑ q ∈ c.support,
        c q • (star (⇑q.1 p.1) * ⇑q.2 p.2)) := by
    have h : StronglyMeasurable (∑ q ∈ c.support, (fun p : α × β =>
        c q • (star (⇑q.1 p.1) * ⇑q.2 p.2))) :=
      Finset.stronglyMeasurable_sum c.support (fun q _ =>
        ((StronglyMeasurable.star _
          ((MeasureTheory.Lp.stronglyMeasurable q.1).comp_fst)).mul
            ((MeasureTheory.Lp.stronglyMeasurable q.2).comp_snd)).const_smul
              (c q))
    have heq : (∑ q ∈ c.support, (fun p : α × β =>
        c q • (star (⇑q.1 p.1) * ⇑q.2 p.2)))
        = (fun p : α × β => ∑ q ∈ c.support,
            c q • (star (⇑q.1 p.1) * ⇑q.2 p.2)) := by
      funext p
      rw [Finset.sum_apply]
    rw [heq] at h
    exact h
  have hmeas : MeasurableSet {p : α × β | ⇑v p
      = ∑ q ∈ c.support,
        c q • (star (⇑q.1 p.1) * ⇑q.2 p.2)} :=
    (MeasureTheory.Lp.stronglyMeasurable v).measurableSet_eq_fun hSM
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ⇑v (x, y)
      = ∑ q ∈ c.support, c q • (star (⇑q.1 x) * ⇑q.2 y) :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).mp hcoe
  filter_upwards [hae, memLp_section_ae_fin
    (MeasureTheory.Lp.memLp v)] with x hx hsecx
  rw [sectionLp_eq_of_memLp hsecx]
  apply MeasureTheory.Lp.ext
  calc ⇑(hsecx.toLp (fun y => ⇑v (x, y)))
        =ᵐ[ν] (fun y => ⇑v (x, y)) := MemLp.coeFn_toLp _
    _ =ᵐ[ν] (fun y => ∑ q ∈ c.support,
          c q • (star (⇑q.1 x) * ⇑q.2 y)) := hx
    _ =ᵐ[ν] ∑ q ∈ c.support, (fun y =>
          c q • (star (⇑q.1 x) * ⇑q.2 y)) := by
        apply Filter.EventuallyEq.of_eq
        funext y
        rw [Finset.sum_apply]
    _ =ᵐ[ν] ∑ q ∈ c.support,
          ⇑(c q • (star (⇑q.1 x) • q.2)) := by
        apply eventuallyEq_sum
        intro q _
        have e1 : ⇑(c q • (star (⇑q.1 x) • q.2))
            =ᵐ[ν] (fun y => c q • (star (⇑q.1 x) * ⇑q.2 y)) := by
          refine (MeasureTheory.Lp.coeFn_smul (c q) _).trans ?_
          refine (MeasureTheory.Lp.coeFn_smul
            (star (⇑q.1 x)) q.2).mono fun y hy => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [hy]
          simp only [Pi.smul_apply, smul_eq_mul]
        exact e1.symm
    _ =ᵐ[ν] ⇑(∑ q ∈ c.support, c q • (star (⇑q.1 x) • q.2)) :=
        (MeasureTheory.Lp.coeFn_finsetSum _ _).symm

/-- Sections of a tensor-span element are a.e. strongly measurable. -/
theorem sectionLp_aestronglyMeasurable_of_mem_span
    {v : Lp ℂ 2 (μ.prod ν)}
    (hv : v ∈ Submodule.span ℂ (Set.range
      fun (q : Lp ℂ 2 μ × Lp ℂ 2 ν) => tensorLp q.1 q.2)) :
    AEStronglyMeasurable (sectionLp (ν := ν) (⇑v)) μ := by
  obtain ⟨c, hc⟩ := sectionLp_eq_sum_of_mem_span hv
  have hSM : StronglyMeasurable (fun x => ∑ q ∈ c.support,
      c q • (star (⇑q.1 x) • q.2)) := by
    have h : StronglyMeasurable (∑ q ∈ c.support, (fun x =>
        c q • (star (⇑q.1 x) • q.2))) :=
      Finset.stronglyMeasurable_sum c.support (fun q _ =>
        ((StronglyMeasurable.star _
          (MeasureTheory.Lp.stronglyMeasurable q.1)).smul_const
            q.2).const_smul (c q))
    have heq : (∑ q ∈ c.support, (fun x =>
        c q • (star (⇑q.1 x) • q.2)))
        = (fun x => ∑ q ∈ c.support,
            c q • (star (⇑q.1 x) • q.2)) := by
      funext x
      rw [Finset.sum_apply]
    rw [heq] at h
    exact h
  refine hSM.aestronglyMeasurable.congr ?_
  filter_upwards [hc] with x hx
  exact hx.symm

/-- The squared section norms of the differences `⇑(v n) - M` are
summable in `n` for almost every `x`, and the sections converge. -/
theorem sectionLp_tendsto_ae {M : α × β → ℂ}
    (hM : MemLp M 2 (μ.prod ν)) (v : ℕ → Lp ℂ 2 (μ.prod ν))
    (hdist : ∀ n, dist (hM.toLp M) (v n) < (1 / 2 : ℝ) ^ n) :
    ∀ᵐ x ∂μ, Tendsto (fun n => sectionLp (ν := ν) (⇑(v n)) x)
      atTop (𝓝 (sectionLp (ν := ν) M x)) := by
  have hF : ∀ n, AEStronglyMeasurable
      (fun p => ⇑(v n) p - M p) (μ.prod ν) :=
    fun n => (MeasureTheory.Lp.aestronglyMeasurable (v n)).sub
      hM.aestronglyMeasurable
  have hAMterm : ∀ n, AEMeasurable
      (fun x => (eLpNorm (fun y => ⇑(v n) (x, y) - M (x, y))
        2 ν) ^ 2) μ := by
    intro n
    have hAM : AEMeasurable
        (fun p => ‖⇑(v n) p - M p‖ₑ ^ 2) (μ.prod ν) := by
      simp only [pow_two]
      exact ((hF n).aemeasurable.enorm).mul
        ((hF n).aemeasurable.enorm)
    refine (hAM.lintegral_prod_right').congr ?_
    filter_upwards [(hF n).prodMk_left] with x hx
    exact (eLpNorm_two_sq ν hx).symm
  have hterm : ∀ n, (∫⁻ x, (eLpNorm
        (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2 ∂μ)
      ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
    intro n
    have hAM : AEMeasurable
        (fun p => ‖⇑(v n) p - M p‖ₑ ^ 2) (μ.prod ν) := by
      simp only [pow_two]
      exact ((hF n).aemeasurable.enorm).mul
        ((hF n).aemeasurable.enorm)
    have hInt : (∫⁻ x, (eLpNorm
          (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2 ∂μ)
        = (eLpNorm (fun p => ⇑(v n) p - M p)
            2 (μ.prod ν)) ^ 2 := by
      rw [eLpNorm_two_sq (μ.prod ν) (hF n),
        MeasureTheory.lintegral_prod _ hAM]
      apply lintegral_congr_ae
      filter_upwards [(hF n).prodMk_left] with x hx
      exact eLpNorm_two_sq ν hx
    rw [hInt]
    have h1 : (fun p => ⇑(v n) p - M p)
        =ᵐ[μ.prod ν] ⇑(v n - hM.toLp M) := by
      refine ((MeasureTheory.Lp.coeFn_sub (v n)
        (hM.toLp M)).trans ?_).symm
      exact (Filter.EventuallyEq.refl _ _).sub
        (MemLp.coeFn_toLp hM)
    have hd : ENNReal.ofReal ‖v n - hM.toLp M‖
        = eLpNorm (fun p => ⇑(v n) p - M p) 2 (μ.prod ν) := by
      rw [MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.memLp _).ne,
        eLpNorm_congr_ae h1.symm]
    calc (eLpNorm (fun p => ⇑(v n) p - M p) 2 (μ.prod ν)) ^ 2
        = (ENNReal.ofReal ‖v n - hM.toLp M‖) ^ 2 := by rw [← hd]
      _ = ENNReal.ofReal (‖v n - hM.toLp M‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have h2 : ‖v n - hM.toLp M‖ = dist (hM.toLp M) (v n) := by
            rw [dist_eq_norm, norm_sub_rev]
          have h3 : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
            rw [← pow_mul, mul_comm n 2, pow_mul]
            congr 1
            norm_num
          rw [h2, ← h3]
          exact pow_le_pow_left₀ (by positivity) (hdist n).le 2
  have hSfin : ∀ᵐ x ∂μ, (∑' n, (eLpNorm
        (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2) < ∞ := by
    apply ae_lt_top' (AEMeasurable.tsum hAMterm)
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc (∫⁻ x, (∑' n, (eLpNorm
            (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2) ∂μ)
        = ∑' n, ∫⁻ x, (eLpNorm
            (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2 ∂μ :=
          MeasureTheory.lintegral_tsum hAMterm
      _ ≤ ∑' n, ENNReal.ofReal ((1 / 4 : ℝ) ^ n) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' n, (1 / 4 : ℝ) ^ n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            (summable_geometric_of_lt_one (by norm_num)
              (by norm_num))).symm
  filter_upwards [hSfin, memLp_section_ae_fin hM,
    (MeasureTheory.ae_all_iff).mpr (fun n =>
      memLp_section_ae_fin (MeasureTheory.Lp.memLp (v n))),
    (MeasureTheory.ae_all_iff).mpr (fun n =>
      memLp_section_ae_fin
        ((MeasureTheory.Lp.memLp (v n)).sub hM))]
    with x hSx hsecM hsecV hsecD
  have hnorm : ∀ n, ‖sectionLp (ν := ν) (⇑(v n)) x - sectionLp (ν := ν) M x‖
      = (eLpNorm (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν).toReal := by
    intro n
    have h1 : sectionLp (ν := ν) (⇑(v n)) x - sectionLp (ν := ν) M x
        = (hsecD n).toLp
            (fun y => ⇑(v n) (x, y) - M (x, y)) := by
      rw [sectionLp_eq_of_memLp (hsecV n),
        sectionLp_eq_of_memLp hsecM]
      exact (MemLp.toLp_sub (hsecV n) hsecM).symm
    rw [h1, MeasureTheory.Lp.norm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  have htend : Tendsto (fun n => (eLpNorm
        (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2)
      atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hSx.ne
  have htendR : Tendsto (fun n =>
        ‖sectionLp (ν := ν) (⇑(v n)) x - sectionLp (ν := ν) M x‖ ^ 2)
      atTop (𝓝 0) := by
    have h : Tendsto (ENNReal.toReal ∘ (fun n => (eLpNorm
          (fun y => ⇑(v n) (x, y) - M (x, y)) 2 ν) ^ 2))
        atTop (𝓝 0) := by
      have h' := (ENNReal.tendsto_toReal
        (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp htend
      simpa using h'
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall
      fun n => by
        rw [Function.comp_apply]
        show ((eLpNorm (fun y => ⇑(v n) (x, y) - M (x, y))
            2 ν) ^ 2).toReal
          = ‖sectionLp (⇑(v n)) x - sectionLp M x‖ ^ 2
        rw [hnorm n, ENNReal.toReal_pow]) h
  have htendN : Tendsto (fun n =>
        ‖sectionLp (ν := ν) (⇑(v n)) x - sectionLp (ν := ν) M x‖) atTop (𝓝 0) := by
    have hfun : (fun n => ‖sectionLp (ν := ν) (⇑(v n)) x - sectionLp (ν := ν) M x‖)
        = fun n => Real.sqrt
            (‖sectionLp (ν := ν) (⇑(v n)) x - sectionLp (ν := ν) M x‖ ^ 2) := by
      funext n
      rw [Real.sqrt_sq (norm_nonneg _)]
    rw [hfun]
    have h := (Real.continuous_sqrt.tendsto 0).comp htendR
    simp only [Function.comp_apply, Real.sqrt_zero] at h
    exact h
  exact tendsto_sub_nhds_zero_iff.mp
    (tendsto_zero_iff_norm_tendsto_zero.mpr htendN)

/-- For finite measures, the section map of an `L2` product kernel is
a.e. strongly measurable. -/
theorem sectionLp_aestronglyMeasurable_fin {M : α × β → ℂ}
    (hM : MemLp M 2 (μ.prod ν)) :
    AEStronglyMeasurable (sectionLp (ν := ν) M) μ := by
  obtain ⟨v, hv, hdist⟩ := exists_tensor_approx_seq hM
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => sectionLp_aestronglyMeasurable_of_mem_span (hv n)) ?_
  exact sectionLp_tendsto_ae hM v hdist

end FiniteSectionMap

section GeneralKernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
  {K : α × β → ℂ}

/-- The partial-integral function of the kernel operator:
`(integralKernelFun ν K f) x = ∫ y, K (x, y) * f y ∂ν`. -/
noncomputable def integralKernelFun (ν : Measure β) (K : α × β → ℂ)
    (f : β → ℂ) : α → ℂ :=
  fun x => ∫ y, K (x, y) * f y ∂ν

/-- **Sections of an `L2` kernel are `L2`:** for a.e. `x`,
the section `y ↦ K (x, y)` is in `L2` of `ν`. (Q12's
`memLp_section_ae`, generalized: no probability anywhere,
`SFinite` suffices for Tonelli.) -/
theorem memLp_section_ae_gen (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 ν := by
  have hfin : (∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod ν)) ≠ ∞ := by
    have h := eLpNorm_two_sq (μ.prod ν) hK.aestronglyMeasurable
    rw [← h]
    exact ENNReal.pow_ne_top (hK.eLpNorm_lt_top).ne
  have hAM : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod ν) := by
    simp only [pow_two]
    exact (hK.aestronglyMeasurable.aemeasurable.enorm).mul
      hK.aestronglyMeasurable.aemeasurable.enorm
  rw [MeasureTheory.lintegral_prod _ hAM] at hfin
  have hae : ∀ᵐ x ∂μ, (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν) < ∞ :=
    ae_lt_top' hAM.lintegral_prod_right' hfin
  filter_upwards [hK.aestronglyMeasurable.prodMk_left, hae]
    with x hx hsec
  show eLpNorm (fun y => K (x, y)) 2 ν < ∞
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by simp) hx]
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
  rw [h2]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  exact hsec.ne

/-- **Sections of the kernel integrand are integrable:**
for a.e. `x`, the integrand `y ↦ K (x, y) * f y` of the
partial integral is integrable. -/
theorem integrable_integralKernelFun_integrand_ae (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * ⇑f y) ν := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  filter_upwards [memLp_section_ae_gen hK] with x hx
  exact memLp_one_iff_integrable.mp
    (hx.mul (MeasureTheory.Lp.memLp f))

/-- The pointwise Cauchy-Schwarz bound for the partial
integral, a.e. in the output variable. -/
theorem integralKernelFun_norm_sq_le_ae (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    ∀ᵐ x ∂μ, ‖integralKernelFun ν K ⇑f x‖ ^ 2
      ≤ (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * ‖f‖ ^ 2 := by
  filter_upwards [memLp_section_ae_gen hK] with x hx
  have hof2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
  have hKx : MemLp (fun y => ‖K (x, y)‖) (ENNReal.ofReal 2) ν := by
    have h := hx.norm
    rw [← hof2] at h
    exact h
  have hf2 : MemLp (fun y => ‖⇑f y‖) (ENNReal.ofReal 2) ν := by
    show eLpNorm (fun y => ‖⇑f y‖) (ENNReal.ofReal 2) ν < ∞
    rw [hof2]
    exact (MeasureTheory.Lp.memLp f).norm
  have hcs : ∫ y, ‖K (x, y)‖ * ‖⇑f y‖ ∂ν
      ≤ (∫ y, ‖K (x, y)‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
        * (∫ y, ‖⇑f y‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      ((Real.holderConjugate_iff (p := 2) (q := 2)).mpr
      ⟨by norm_num, by norm_num⟩)
      (Filter.Eventually.of_forall fun y => norm_nonneg _)
      (Filter.Eventually.of_forall fun y => norm_nonneg _) hKx hf2
  have hrw : ∀ w : β → ℝ, (∫ y, w y ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ y, w y ^ 2 ∂ν) := by
    intro w
    have e1 : (∫ y, w y ^ (2 : ℝ) ∂ν) = ∫ y, w y ^ 2 ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
    rw [e1]
    exact (Real.sqrt_eq_rpow _).symm
  rw [hrw, hrw] at hcs
  have hnorm : ‖integralKernelFun ν K ⇑f x‖
      ≤ ∫ y, ‖K (x, y)‖ * ‖⇑f y‖ ∂ν := by
    calc ‖integralKernelFun ν K ⇑f x‖
        = ‖∫ y, K (x, y) * ⇑f y ∂ν‖ := rfl
      _ ≤ ∫ y, ‖K (x, y) * ⇑f y‖ ∂ν :=
          norm_integral_le_integral_norm (fun y => K (x, y) * ⇑f y)
      _ = ∫ y, ‖K (x, y)‖ * ‖⇑f y‖ ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun y =>
            norm_mul _ _)
  have hsq : ‖integralKernelFun ν K ⇑f x‖ ^ 2
      ≤ (∫ y, ‖K (x, y)‖ * ‖⇑f y‖ ∂ν) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  refine hsq.trans ?_
  calc (∫ y, ‖K (x, y)‖ * ‖⇑f y‖ ∂ν) ^ 2
      ≤ (Real.sqrt (∫ y, ‖K (x, y)‖ ^ 2 ∂ν)
          * Real.sqrt (∫ y, ‖⇑f y‖ ^ 2 ∂ν)) ^ 2 :=
      pow_le_pow_left₀ (integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun y =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))) hcs 2
    _ = (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * ‖f‖ ^ 2 := by
        rw [mul_pow,
          Real.sq_sqrt (integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun y => by positivity)),
          Real.sq_sqrt (integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun y => by positivity)),
          integral_norm_sq_lp ν f]

/-- The partial integral is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_integralKernelFun (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    AEStronglyMeasurable (integralKernelFun ν K ⇑f) μ := by
  have hH : AEStronglyMeasurable (fun p => K p * ⇑f p.2) (μ.prod ν) :=
    hK.aestronglyMeasurable.mul
      ((MeasureTheory.Lp.aestronglyMeasurable f).comp_snd)
  exact hH.integral_prod_right'

/-- **Squared seminorm bound for the partial integral:**
`(eLpNorm (integralKernelFun ν K ⇑f) 2 μ)^2 ≤ (eLpNorm K 2
(μ.prod ν))^2 * ENNReal.ofReal ‖f‖^2`. This is the
Hilbert-Schmidt bound at the seminorm level; the operator
bound and `MemLp` both follow from it. -/
theorem integralKernel_eLpNorm_sq_le (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    (eLpNorm (integralKernelFun ν K ⇑f) 2 μ) ^ 2
      ≤ (eLpNorm K 2 (μ.prod ν)) ^ 2 * ENNReal.ofReal (‖f‖ ^ 2) := by
  have hpt : ∀ y : ℂ, ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
    intro y
    simp [enorm, ENNReal.ofReal_pow]
  have haesm := aestronglyMeasurable_integralKernelFun hK f
  rw [eLpNorm_two_sq _ haesm]
  calc ∫⁻ x, ‖integralKernelFun ν K ⇑f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal
          ((∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * ‖f‖ ^ 2) ∂μ :=
        lintegral_mono_ae ((integralKernelFun_norm_sq_le_ae hK f).mono
          fun x hx => by
            rw [hpt]
            exact ENNReal.ofReal_le_ofReal hx)
    _ = (∫⁻ x, ENNReal.ofReal (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) ∂μ)
        * ENNReal.ofReal (‖f‖ ^ 2) := by
        rw [← MeasureTheory.lintegral_mul_const'']
        · exact lintegral_congr_ae (Filter.Eventually.of_forall fun x =>
            ENNReal.ofReal_mul
              (integral_nonneg_of_ae
                (Filter.Eventually.of_forall fun y => by positivity)))
        · have hnorm2 : AEStronglyMeasurable (fun p => ‖K p‖ ^ 2)
              (μ.prod ν) :=
            (hK.aestronglyMeasurable.norm.mul
              hK.aestronglyMeasurable.norm).congr
              (Filter.Eventually.of_forall fun p =>
                (pow_two ‖K p‖).symm)
          exact ENNReal.measurable_ofReal.comp_aemeasurable
            (hnorm2.integral_prod_right').aemeasurable
    _ = (∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod ν)) * ENNReal.ofReal (‖f‖ ^ 2) := by
        congr 1
        have hAM : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod ν) := by
          simp only [pow_two]
          exact (hK.aestronglyMeasurable.aemeasurable.enorm).mul
            hK.aestronglyMeasurable.aemeasurable.enorm
        rw [MeasureTheory.lintegral_prod _ hAM]
        apply lintegral_congr_ae
        filter_upwards [memLp_section_ae_gen hK] with x hx
        have hintx : Integrable (fun y => ‖K (x, y)‖ ^ 2) ν := by
          have h := hx.integrable_norm_rpow (p := (2 : ℝ≥0∞))
            (by norm_num) (by simp)
          have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by simp
          rw [h2] at h
          simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast] using h
        rw [ofReal_integral_eq_lintegral_ofReal hintx
          (Filter.Eventually.of_forall fun y => by positivity)]
        exact lintegral_congr_ae (Filter.Eventually.of_forall fun y =>
          (hpt (K (x, y))).symm)
    _ = (eLpNorm K 2 (μ.prod ν)) ^ 2 * ENNReal.ofReal (‖f‖ ^ 2) := by
        rw [eLpNorm_two_sq _ hK.aestronglyMeasurable]

/-- **The partial integral of an `L2` kernel applied to an
`L2` function is `L2`.** -/
theorem memLp_integralKernelFun (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    MemLp (integralKernelFun ν K ⇑f) 2 μ := by
  have hle := integralKernel_eLpNorm_sq_le hK f
  have hfin2 : (eLpNorm (integralKernelFun ν K ⇑f) 2 μ) ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top hK.ne)
        ENNReal.ofReal_lt_top.ne) hle
  have hne : eLpNorm (integralKernelFun ν K ⇑f) 2 μ ≠ ∞ := by
    intro hEq
    rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hfin2
    exact hfin2 rfl
  exact lt_top_iff_ne_top.mpr hne

/-- **Additivity of the partial integral** in the `L2`
argument, a.e. on the output space. -/
theorem integralKernelFun_add_ae (hK : MemLp K 2 (μ.prod ν)) (f g : Lp ℂ 2 ν) :
    integralKernelFun ν K ⇑(f + g)
      =ᵐ[μ] integralKernelFun ν K ⇑f + integralKernelFun ν K ⇑g := by
  filter_upwards [integrable_integralKernelFun_integrand_ae hK f,
    integrable_integralKernelFun_integrand_ae hK g] with x hfx hgx
  have hcoe : ⇑(f + g) =ᵐ[ν] ⇑f + ⇑g := MeasureTheory.Lp.coeFn_add f g
  show (∫ y, K (x, y) * ⇑(f + g) y ∂ν)
    = (∫ y, K (x, y) * ⇑f y ∂ν) + (∫ y, K (x, y) * ⇑g y ∂ν)
  have e1 : (∫ y, K (x, y) * ⇑(f + g) y ∂ν)
      = ∫ y, (K (x, y) * ⇑f y + K (x, y) * ⇑g y) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hcoe] with y hy
    rw [hy, Pi.add_apply, mul_add]
  rw [e1, integral_add hfx hgx]

/-- **Homogeneity of the partial integral** in the `L2`
argument, a.e. on the output space. -/
theorem integralKernelFun_smul_ae (hK : MemLp K 2 (μ.prod ν)) (c : ℂ) (f : Lp ℂ 2 ν) :
    integralKernelFun ν K ⇑(c • f)
      =ᵐ[μ] c • integralKernelFun ν K ⇑f := by
  have hcoe : ⇑(c • f) =ᵐ[ν] c • ⇑f := MeasureTheory.Lp.coeFn_smul c f
  apply Filter.Eventually.of_forall
  intro x
  show (∫ y, K (x, y) * ⇑(c • f) y ∂ν)
    = c • (∫ y, K (x, y) * ⇑f y ∂ν)
  have e1 : (∫ y, K (x, y) * ⇑(c • f) y ∂ν)
      = ∫ y, c * (K (x, y) * ⇑f y) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hcoe] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, integral_const_mul, smul_eq_mul]

/-- The `L2` element of the partial integral. -/
noncomputable def integralKernelRep (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) : Lp ℂ 2 μ :=
  (memLp_integralKernelFun hK f).toLp (integralKernelFun ν K ⇑f)

/-- Representatives of `integralKernelRep` are the partial
integrals. -/
theorem coeFn_integralKernelRep (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ⇑(integralKernelRep hK f) =ᵐ[μ] integralKernelFun ν K ⇑f :=
  MemLp.coeFn_toLp _

/-- **The kernel operator as a linear map:**
`integralKernelLinMap hK f` is the partial integral
against `K`. -/
noncomputable def integralKernelLinMap (hK : MemLp K 2 (μ.prod ν)) :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := integralKernelRep hK f
  map_add' f g := by
    rw [MeasureTheory.Lp.ext_iff]
    calc ⇑(integralKernelRep hK (f + g))
        =ᵐ[μ] integralKernelFun ν K ⇑(f + g) :=
          coeFn_integralKernelRep hK (f + g)
      _ =ᵐ[μ] integralKernelFun ν K ⇑f + integralKernelFun ν K ⇑g :=
          integralKernelFun_add_ae hK f g
      _ =ᵐ[μ] ⇑(integralKernelRep hK f) + ⇑(integralKernelRep hK g) :=
          (coeFn_integralKernelRep hK f).symm.add
            (coeFn_integralKernelRep hK g).symm
      _ =ᵐ[μ] ⇑(integralKernelRep hK f + integralKernelRep hK g) :=
          (MeasureTheory.Lp.coeFn_add _ _).symm
  map_smul' c f := by
    rw [MeasureTheory.Lp.ext_iff]
    calc ⇑(integralKernelRep hK (c • f))
        =ᵐ[μ] integralKernelFun ν K ⇑(c • f) :=
          coeFn_integralKernelRep hK (c • f)
      _ =ᵐ[μ] c • integralKernelFun ν K ⇑f :=
          integralKernelFun_smul_ae hK c f
      _ =ᵐ[μ] c • ⇑(integralKernelRep hK f) :=
          (coeFn_integralKernelRep hK f).symm.const_smul c
      _ =ᵐ[μ] ⇑(c • integralKernelRep hK f) :=
          (MeasureTheory.Lp.coeFn_smul c _).symm

/-- Representatives of `integralKernelLinMap hK f` are the
partial integrals. -/
theorem coeFn_integralKernelLinMap (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ⇑(integralKernelLinMap hK f) =ᵐ[μ] integralKernelFun ν K ⇑f :=
  coeFn_integralKernelRep hK f

/-- **The Hilbert-Schmidt bound for the linear map:**
`‖integralKernelLinMap hK f‖ ≤ ‖K‖₂ * ‖f‖`, from the
squared seminorm bound `integralKernel_eLpNorm_sq_le`. -/
theorem integralKernelLinMap_norm_le (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ‖integralKernelLinMap hK f‖
      ≤ (eLpNorm K 2 (μ.prod ν)).toReal * ‖f‖ := by
  have hnorm : ‖integralKernelLinMap hK f‖
      = (eLpNorm (integralKernelFun ν K ⇑f) 2 μ).toReal := by
    calc ‖integralKernelLinMap hK f‖
        = (eLpNorm (⇑(integralKernelLinMap hK f)) 2 μ).toReal :=
          (MeasureTheory.Lp.norm_def _).symm
      _ = (eLpNorm (integralKernelFun ν K ⇑f) 2 μ).toReal := by
          congr 1
          exact eLpNorm_congr_ae (coeFn_integralKernelLinMap hK f)
  have hsq : ‖integralKernelLinMap hK f‖ ^ 2
      ≤ ((eLpNorm K 2 (μ.prod ν)).toReal * ‖f‖) ^ 2 := by
    rw [hnorm, ← ENNReal.toReal_pow]
    have hfin : (eLpNorm K 2 (μ.prod ν)) ^ 2
        * ENNReal.ofReal (‖f‖ ^ 2) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top hK.ne)
        ENNReal.ofReal_lt_top.ne
    calc ((eLpNorm (integralKernelFun ν K ⇑f) 2 μ) ^ 2).toReal
        ≤ ((eLpNorm K 2 (μ.prod ν)) ^ 2
          * ENNReal.ofReal (‖f‖ ^ 2)).toReal :=
          ENNReal.toReal_mono hfin (integralKernel_eLpNorm_sq_le hK f)
      _ = ((eLpNorm K 2 (μ.prod ν)).toReal * ‖f‖) ^ 2 := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ ‖f‖ ^ 2),
            mul_pow]
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg f)) hsq

/-- **The kernel operator** as a continuous linear map:
`integralKernelOp hK f` is the partial integral
`x ↦ ∫ y, K (x, y) * f y ∂ν`. (Pack 3a-ii item 1: the
output variable is the first kernel variable.) -/
noncomputable def integralKernelOp (hK : MemLp K 2 (μ.prod ν)) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (integralKernelLinMap hK).mkContinuous
    (eLpNorm K 2 (μ.prod ν)).toReal
    (fun f => integralKernelLinMap_norm_le hK f)

theorem integralKernelOp_apply (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    integralKernelOp hK f = integralKernelLinMap hK f :=
  rfl

/-- Representatives of `integralKernelOp hK f` are the
partial integrals, a.e. -/
theorem coeFn_integralKernelOp (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ⇑(integralKernelOp hK f) =ᵐ[μ] integralKernelFun ν K ⇑f :=
  coeFn_integralKernelLinMap hK f

/-- **Boundedness / HS bound** (pack 3a-ii item 3):
`‖integralKernelOp hK‖ ≤ ‖K‖₂`. -/
theorem integralKernelOp_norm_le (hK : MemLp K 2 (μ.prod ν)) :
    ‖integralKernelOp hK‖ ≤ (eLpNorm K 2 (μ.prod ν)).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-! ## The form identity (pack 3a-ii item 2) -/

/-- **Squared seminorm of a tensor factor:** for
`V p = conj (g p.1) * f p.2` on the product space, the
squared seminorm separates under Tonelli. -/
theorem eLpNorm_tensor_sq_gen (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    (eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2 (μ.prod ν)) ^ 2
      = ((eLpNorm (⇑g) 2 μ) * (eLpNorm (⇑f) 2 ν)) ^ 2 := by
  have hpt : ∀ y : ℂ, ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
    intro y
    simp [enorm, ENNReal.ofReal_pow]
  have hgA : AEStronglyMeasurable (⇑g) μ :=
    MeasureTheory.Lp.aestronglyMeasurable g
  have hfA : AEStronglyMeasurable (⇑f) ν :=
    MeasureTheory.Lp.aestronglyMeasurable f
  have hV : AEStronglyMeasurable
      (fun p => star (⇑g p.1) * ⇑f p.2) (μ.prod ν) :=
    (continuous_star.comp_aestronglyMeasurable hgA.comp_fst).mul
      hfA.comp_snd
  rw [eLpNorm_two_sq _ hV, mul_pow, eLpNorm_two_sq _ hgA,
    eLpNorm_two_sq _ hfA]
  have hAM : AEMeasurable
      (fun p => ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2) (μ.prod ν) :=
    ((hgA.aemeasurable.comp_fst).enorm.pow_const 2).mul
      ((hfA.aemeasurable.comp_snd).enorm.pow_const 2)
  calc ∫⁻ p, ‖star (⇑g p.1) * ⇑f p.2‖ₑ ^ 2 ∂(μ.prod ν)
      = ∫⁻ p, ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2 ∂(μ.prod ν) :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
          show ‖star (⇑g p.1) * ⇑f p.2‖ₑ ^ 2
            = ‖⇑g p.1‖ₑ ^ 2 * ‖⇑f p.2‖ₑ ^ 2
          rw [hpt, hpt (⇑g p.1), hpt (⇑f p.2), ← ENNReal.ofReal_mul
            (by positivity)]
          congr 1
          rw [norm_mul, norm_star, mul_pow])
    _ = (∫⁻ x, ‖⇑g x‖ₑ ^ 2 ∂μ) * (∫⁻ y, ‖⇑f y‖ₑ ^ 2 ∂ν) := by
        rw [MeasureTheory.lintegral_prod _ hAM]
        exact MeasureTheory.lintegral_lintegral_mul
          (hgA.aemeasurable.enorm.pow_const 2)
          (hfA.aemeasurable.enorm.pow_const 2)

/-- Tensor factors are `L2` on the product space. -/
theorem memLp_tensor_gen (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    MemLp (fun p => star (⇑g p.1) * ⇑f p.2) 2 (μ.prod ν) := by
  have hsq := eLpNorm_tensor_sq_gen g f
  show eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2 (μ.prod ν) < ∞
  by_contra htop
  push Not at htop
  have hEq : eLpNorm (fun p => star (⇑g p.1) * ⇑f p.2) 2
      (μ.prod ν) = ∞ := le_antisymm le_top htop
  rw [hEq, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  have hfin : ((eLpNorm (⇑g) 2 μ) * (eLpNorm (⇑f) 2 ν)) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.mul_ne_top
      (MeasureTheory.Lp.memLp g).ne (MeasureTheory.Lp.memLp f).ne)
  exact hfin hsq.symm

/-- Integrability of the kernel pairing integrand
`p ↦ star (g p.1) * (K p * f p.2)` on the product space:
it is the product of the kernel with a tensor factor. -/
theorem integrable_kernel_pairing_gen (hK : MemLp K 2 (μ.prod ν))
    (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    Integrable (fun p => star (⇑g p.1) * (K p * ⇑f p.2))
      (μ.prod ν) := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have h1 : Integrable (K * (fun p => star (⇑g p.1) * ⇑f p.2))
      (μ.prod ν) :=
    memLp_one_iff_integrable.mp (hK.mul (memLp_tensor_gen g f))
  refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.mul_apply]
  ring

/-- **The form identity** (pack 3a-ii item 2): the inner
product against `integralKernelOp hK f` is the
product-measure integral of the kernel pairing. -/
theorem integralKernelOp_inner (hK : MemLp K 2 (μ.prod ν))
    (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    ⟪g, integralKernelOp hK f⟫
      = ∫ p, star (⇑g p.1) * (K p * ⇑f p.2) ∂(μ.prod ν) := by
  have h1 : ⟪g, integralKernelOp hK f⟫
      = ∫ x, star (⇑g x) * integralKernelFun ν K ⇑f x ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_integralKernelOp hK f] with x hx
    rw [hx, RCLike.inner_apply]
    show integralKernelFun ν K ⇑f x * (starRingEnd ℂ) (⇑g x)
      = star (⇑g x) * integralKernelFun ν K ⇑f x
    rw [starRingEnd_apply, mul_comm]
  have h2 : (∫ x, star (⇑g x) * integralKernelFun ν K ⇑f x ∂μ)
      = ∫ x, ∫ y, star (⇑g x) * (K (x, y) * ⇑f y) ∂ν ∂μ := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    exact (integral_const_mul (star (⇑g x))
      (fun y => K (x, y) * ⇑f y)).symm
  rw [h1, h2]
  exact MeasureTheory.integral_integral
    (integrable_kernel_pairing_gen hK g f)

/-- **The form identity, iterated form** (the pack's
displayed shape): `⟪g, integralKernelOp hK f⟫`
`= ∫ x, ∫ y, conj (g x) * K (x, y) * f y ∂ν ∂μ`, with
`conj` written as `star` on `ℂ`. -/
theorem integralKernelOp_inner_iterated (hK : MemLp K 2 (μ.prod ν))
    (g : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    ⟪g, integralKernelOp hK f⟫
      = ∫ x, ∫ y, star (⇑g x) * K (x, y) * ⇑f y ∂ν ∂μ := by
  rw [integralKernelOp_inner hK g f]
  have hint2 : Integrable
      (Function.uncurry
        (fun x y => star (⇑g x) * (K (x, y) * ⇑f y))) (μ.prod ν) :=
    (integrable_kernel_pairing_gen hK g f).congr
      (Filter.Eventually.of_forall fun p => rfl)
  have hprod : (∫ p, star (⇑g p.1) * (K p * ⇑f p.2) ∂(μ.prod ν))
      = ∫ x, ∫ y, star (⇑g x) * (K (x, y) * ⇑f y) ∂ν ∂μ := by
    have hcong : (∫ p, star (⇑g p.1) * (K p * ⇑f p.2) ∂(μ.prod ν))
        = ∫ p, star (⇑g p.1) * (K (p.1, p.2) * ⇑f p.2) ∂(μ.prod ν) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => rfl)
    rw [hcong]
    exact (MeasureTheory.integral_integral hint2).symm
  rw [hprod]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  ring

/-! ## The HS identity (pack 3a-ii item 4)

First the pointwise identity (a.e. in the output variable),
then the finite Bessel bound, which gives summability of
the HS family and countable support of the index family -
the two inputs the Tonelli step over a general (possibly
uncountable) Hilbert basis needs. -/

/-- The pointwise Hilbert-Schmidt identity: for a.e. output
variable `x`, the squared Fourier coefficients of the
kernel operator's values on basis vectors sum (in
`ℝ≥0∞`) to the squared `L2` norm of the kernel's section
at `x`. (Q12's `hs_identity_ae`, generalized.) -/
theorem integralKernel_hs_identity_ae (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    ∀ᵐ x ∂μ, ∀ _hz : MemLp (fun y => K (x, y)) 2 ν,
      ∑' i, ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2
        = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν := by
  filter_upwards [memLp_section_ae_gen hK] with x _hzsec hz
  have hpt : ∀ y : ℂ, ENNReal.ofReal (‖y‖ ^ 2) = ‖y‖ₑ ^ 2 := fun y => by
    simp [enorm, ENNReal.ofReal_pow]
  have hsecstar : MemLp (fun y => star (K (x, y))) 2 ν := hz.star
  set u : Lp ℂ 2 ν := hsecstar.toLp _ with hu
  have hstep1 : ∀ i, integralKernelFun ν K (⇑(b i)) x
      = ⟪u, b i⟫ := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    show (∫ y, K (x, y) * ⇑(b i) y ∂ν)
      = ∫ y, ⟪⇑u y, ⇑(b i) y⟫ ∂ν
    apply integral_congr_ae
    filter_upwards [hsecstar.coeFn_toLp] with y hy
    rw [RCLike.inner_apply, hy, starRingEnd_apply, star_star, mul_comm]
  have hnorm : ∀ i, ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2
      = ENNReal.ofReal (‖⟪b i, u⟫‖ ^ 2) := by
    intro i
    have hnn : ‖⟪u, b i⟫‖ = ‖⟪b i, u⟫‖ := by
      rw [← inner_conj_symm, starRingEnd_apply, norm_star]
    rw [← hpt, hstep1 i, hnn]
  rw [tsum_congr hnorm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
      (hsSummable_inner_sq b u),
    hsParseval_tsum b u]
  have hnormE : ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν
      = ∫⁻ y, ‖⇑u y‖ₑ ^ 2 ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hsecstar.coeFn_toLp] with y hy
    rw [hy, ← hpt, ← hpt, norm_star]
  rw [hnormE, ← eLpNorm_two_sq _ (MeasureTheory.Lp.aestronglyMeasurable u),
    MeasureTheory.Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (MeasureTheory.Lp.memLp u).eLpNorm_lt_top.ne]

/-- The `ℝ≥0∞` HS summand: squared seminorm of the kernel
operator's value on a basis vector. -/
noncomputable def hsSummandENN (hK : MemLp K 2 (μ.prod ν)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (i : ι) : ℝ≥0∞ :=
  (eLpNorm (⇑(integralKernelOp hK (b i))) 2 μ) ^ 2

/-- Each `ℝ≥0∞` summand is the integral of the pointwise
summand. -/
theorem hsSummandENN_eq_lintegral (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (i : ι) :
    hsSummandENN hK b i
      = ∫⁻ x, ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2 ∂μ := by
  show (eLpNorm (⇑(integralKernelOp hK (b i))) 2 μ) ^ 2 = _
  rw [eLpNorm_two_sq _ (MeasureTheory.Lp.aestronglyMeasurable _)]
  apply lintegral_congr_ae
  exact (coeFn_integralKernelOp hK (b i)).mono fun x hx => by
    show ‖⇑(integralKernelOp hK (b i)) x‖ₑ ^ 2
      = ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2
    rw [hx]

/-- The pointwise summands are a.e.-measurable. -/
theorem aemeasurable_hsSummand (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (i : ι) :
    AEMeasurable (fun x => ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2)
      μ := by
  have h := ((memLp_integralKernelFun hK (b i)).aestronglyMeasurable).aemeasurable.enorm
  exact (h.mul h).congr (Filter.Eventually.of_forall fun x => by
    show ‖integralKernelFun ν K (⇑(b i)) x‖ₑ
        * ‖integralKernelFun ν K (⇑(b i)) x‖ₑ
      = ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2
    rw [pow_two])

/-- **The finite Bessel bound** (`ℝ≥0∞` form): every finite
partial sum of the HS family is at most the squared `L2`
norm of the kernel. -/
theorem hsSummandENN_finset_sum_le (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (F : Finset ι) :
    ∑ i ∈ F, hsSummandENN hK b i ≤ (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
  have h1 : ∀ i, hsSummandENN hK b i
      = ∫⁻ x, ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2 ∂μ :=
    fun i => hsSummandENN_eq_lintegral hK b i
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    ← MeasureTheory.lintegral_finsetSum' F
      (fun i _ => aemeasurable_hsSummand hK b i)]
  have h2 : ∫⁻ x, ∑ i ∈ F, ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [integralKernel_hs_identity_ae hK b,
      memLp_section_ae_gen hK] with x hid hxsec
    rw [← hid hxsec]
    exact ENNReal.sum_le_tsum F
  refine h2.trans_eq ?_
  have hAM : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod ν) := by
    simp only [pow_two]
    exact (hK.aestronglyMeasurable.aemeasurable.enorm).mul
      hK.aestronglyMeasurable.aemeasurable.enorm
  rw [← MeasureTheory.lintegral_prod _ hAM,
    eLpNorm_two_sq _ hK.aestronglyMeasurable]

/-- The total `ℝ≥0∞` HS sum is at most the squared `L2`
norm of the kernel; in particular it is finite. -/
theorem hsSummandENN_tsum_le (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    ∑' i, hsSummandENN hK b i ≤ (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (fun F => hsSummandENN_finset_sum_le hK b F)

/-- The HS family has countable support: only countably
many basis vectors have nonzero image under the kernel
operator. -/
theorem hs_support_countable (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    (Function.support (hsSummandENN hK b)).Countable := by
  apply Summable.countable_support_ennreal
  refine ne_top_of_le_ne_top ?_ (hsSummandENN_tsum_le hK b)
  exact ENNReal.pow_ne_top hK.ne

/-- The real HS summand: `(hsSummandENN hK b i).toReal`
is `‖integralKernelOp hK (b i)‖ ^ 2`. -/
theorem hsSummandENN_toReal (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (i : ι) :
    (hsSummandENN hK b i).toReal
      = ‖integralKernelOp hK (b i)‖ ^ 2 := by
  show ((eLpNorm (⇑(integralKernelOp hK (b i))) 2 μ) ^ 2).toReal = _
  rw [ENNReal.toReal_pow, MeasureTheory.Lp.norm_def]

/-- **Summability of the HS family** (real form), from the
finite Bessel bound. -/
theorem integralKernel_summable_norm_sq (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    Summable (fun i => ‖integralKernelOp hK (b i)‖ ^ 2) := by
  have hne : ∑' i, hsSummandENN hK b i ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.pow_ne_top hK.ne)
      (hsSummandENN_tsum_le hK b)
  refine (ENNReal.summable_toReal hne).congr (fun i => ?_)
  rw [hsSummandENN_toReal hK b i]

/-- The kernel operator is Hilbert-Schmidt (3a-i sense):
the first half of pack 3a-ii item 4. -/
theorem integralKernel_isHilbertSchmidt (hK : MemLp K 2 (μ.prod ν)) :
    IsHilbertSchmidt (integralKernelOp hK) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  exact (isHilbertSchmidt_iff _ b).mpr
    (integralKernel_summable_norm_sq hK b)

/-- **Compactness** (pack 3a-ii item 5): the kernel
operator is compact, via the HS property and 3a-i's
`IsHilbertSchmidt.isCompactOperator`. (The HS identity
below upgrades the bound to the equality; compactness
itself only needs summability.) -/
theorem integralKernelOp_isCompactOperator
    (hK : MemLp K 2 (μ.prod ν)) :
    IsCompactOperator ⇑(integralKernelOp hK) :=
  (integralKernel_isHilbertSchmidt hK).isCompactOperator

/-- The squared enorm of the kernel is a.e. measurable on the product. -/
theorem aemeasurable_kernel_enorm_sq (hK : MemLp K 2 (μ.prod ν)) :
    AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod ν) := by
  simp only [pow_two]
  exact (hK.aestronglyMeasurable.aemeasurable.enorm).mul
    hK.aestronglyMeasurable.aemeasurable.enorm

/-- A measurable version of the row energy
`x ↦ ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν`. -/
noncomputable def rowEnergy (hK : MemLp K 2 (μ.prod ν)) : α → ℝ≥0∞ :=
  ((aemeasurable_kernel_enorm_sq hK).lintegral_prod_right').mk _

theorem rowEnergy_measurable (hK : MemLp K 2 (μ.prod ν)) :
    Measurable (rowEnergy hK) :=
  ((aemeasurable_kernel_enorm_sq hK).lintegral_prod_right').measurable_mk

theorem rowEnergy_ae_eq (hK : MemLp K 2 (μ.prod ν)) :
    (fun x => ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν) =ᵐ[μ] rowEnergy hK :=
  ((aemeasurable_kernel_enorm_sq hK).lintegral_prod_right').ae_eq_mk

theorem rowEnergy_lintegral (hK : MemLp K 2 (μ.prod ν)) :
    (∫⁻ x, rowEnergy hK x ∂μ) = (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
  rw [lintegral_congr_ae (rowEnergy_ae_eq hK).symm,
    ← MeasureTheory.lintegral_prod _
      (aemeasurable_kernel_enorm_sq hK)]
  exact (eLpNorm_two_sq (μ.prod ν) hK.aestronglyMeasurable).symm

/-- The `n`-th row support set: where the row energy is at least
`(n + 1)⁻¹`. These are measurable, of finite measure, monotone, and
cover the nonzero row energy set. -/
def kernelRowSet (hK : MemLp K 2 (μ.prod ν)) (n : ℕ) : Set α :=
  {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ rowEnergy hK x}

theorem kernelRowSet_measurable (hK : MemLp K 2 (μ.prod ν)) (n : ℕ) :
    MeasurableSet (kernelRowSet hK n) :=
  measurableSet_le measurable_const (rowEnergy_measurable hK)

theorem kernelRowSet_measure_ne_top (hK : MemLp K 2 (μ.prod ν))
    (n : ℕ) : μ (kernelRowSet hK n) ≠ ∞ := by
  have hC : (eLpNorm K 2 (μ.prod ν)) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (hK.eLpNorm_lt_top).ne
  have hmarkov : ((n : ℝ≥0∞) + 1)⁻¹ * μ (kernelRowSet hK n)
      ≤ (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
    calc ((n : ℝ≥0∞) + 1)⁻¹ * μ (kernelRowSet hK n)
        = ∫⁻ _x in kernelRowSet hK n, ((n : ℝ≥0∞) + 1)⁻¹ ∂μ :=
          (MeasureTheory.setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in kernelRowSet hK n, rowEnergy hK x ∂μ :=
          MeasureTheory.setLIntegral_mono'
            (kernelRowSet_measurable hK n) (fun x hx => hx)
      _ ≤ ∫⁻ x, rowEnergy hK x ∂μ :=
          MeasureTheory.setLIntegral_le_lintegral _ _
      _ = (eLpNorm K 2 (μ.prod ν)) ^ 2 := rowEnergy_lintegral hK
  have hcoeff : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩
  by_contra htop
  rw [htop, ENNReal.mul_top hcoeff] at hmarkov
  exact hC (le_antisymm le_top hmarkov)

theorem kernelRowSet_mono (hK : MemLp K 2 (μ.prod ν)) :
    Monotone (kernelRowSet hK) := by
  intro m n hmn x hx
  have hcast : ((m : ℝ≥0∞) + 1) ≤ ((n : ℝ≥0∞) + 1) := by
    have : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hmn
    exact add_le_add_left this 1
  exact le_trans (ENNReal.inv_le_inv.mpr hcast) hx

theorem kernelRowSet_iUnion (hK : MemLp K 2 (μ.prod ν)) :
    ⋃ n, kernelRowSet hK n = {x | rowEnergy hK x ≠ 0} := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (ENNReal.add_ne_top.mpr
        ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
    exact ne_of_gt (lt_of_lt_of_le hpos hn)
  · intro hx
    rw [Set.mem_iUnion]
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt
      (ENNReal.inv_ne_top.mpr hx)
    refine ⟨k, ?_⟩
    have hle : (rowEnergy hK x)⁻¹ ≤ ((k : ℝ≥0∞) + 1) :=
      le_trans hk.le (le_add_of_nonneg_right zero_le)
    have := ENNReal.inv_le_inv.mpr hle
    rwa [inv_inv] at this

/-- The swapped squared enorm of the kernel is a.e. measurable. -/
theorem aemeasurable_kernel_enorm_sq_swap
    (hK : MemLp K 2 (μ.prod ν)) :
    AEMeasurable (fun q : β × α => ‖K (q.2, q.1)‖ₑ ^ 2)
      (ν.prod μ) := by
  have h := aemeasurable_kernel_enorm_sq hK
  rw [← MeasureTheory.Measure.prod_swap] at h
  exact h.comp_measurable measurable_swap

/-- A measurable version of the column energy
`y ↦ ∫⁻ x, ‖K (x, y)‖ₑ ^ 2 ∂μ`. -/
noncomputable def colEnergy (hK : MemLp K 2 (μ.prod ν)) : β → ℝ≥0∞ :=
  ((aemeasurable_kernel_enorm_sq_swap hK).lintegral_prod_right').mk _

theorem colEnergy_measurable (hK : MemLp K 2 (μ.prod ν)) :
    Measurable (colEnergy hK) :=
  ((aemeasurable_kernel_enorm_sq_swap
    hK).lintegral_prod_right').measurable_mk

theorem colEnergy_ae_eq (hK : MemLp K 2 (μ.prod ν)) :
    (fun y => ∫⁻ x, ‖K (x, y)‖ₑ ^ 2 ∂μ) =ᵐ[ν] colEnergy hK :=
  ((aemeasurable_kernel_enorm_sq_swap
    hK).lintegral_prod_right').ae_eq_mk

theorem colEnergy_lintegral (hK : MemLp K 2 (μ.prod ν)) :
    (∫⁻ y, colEnergy hK y ∂ν) = (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
  rw [lintegral_congr_ae (colEnergy_ae_eq hK).symm,
    ← MeasureTheory.lintegral_prod_symm _
      (aemeasurable_kernel_enorm_sq hK)]
  exact (eLpNorm_two_sq (μ.prod ν) hK.aestronglyMeasurable).symm

/-- The `n`-th column support set. -/
def kernelColSet (hK : MemLp K 2 (μ.prod ν)) (n : ℕ) : Set β :=
  {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ colEnergy hK y}

theorem kernelColSet_measurable (hK : MemLp K 2 (μ.prod ν)) (n : ℕ) :
    MeasurableSet (kernelColSet hK n) :=
  measurableSet_le measurable_const (colEnergy_measurable hK)

theorem kernelColSet_measure_ne_top (hK : MemLp K 2 (μ.prod ν))
    (n : ℕ) : ν (kernelColSet hK n) ≠ ∞ := by
  have hC : (eLpNorm K 2 (μ.prod ν)) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (hK.eLpNorm_lt_top).ne
  have hmarkov : ((n : ℝ≥0∞) + 1)⁻¹ * ν (kernelColSet hK n)
      ≤ (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
    calc ((n : ℝ≥0∞) + 1)⁻¹ * ν (kernelColSet hK n)
        = ∫⁻ _y in kernelColSet hK n, ((n : ℝ≥0∞) + 1)⁻¹ ∂ν :=
          (MeasureTheory.setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in kernelColSet hK n, colEnergy hK y ∂ν :=
          MeasureTheory.setLIntegral_mono'
            (kernelColSet_measurable hK n) (fun y hy => hy)
      _ ≤ ∫⁻ y, colEnergy hK y ∂ν :=
          MeasureTheory.setLIntegral_le_lintegral _ _
      _ = (eLpNorm K 2 (μ.prod ν)) ^ 2 := colEnergy_lintegral hK
  have hcoeff : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩
  by_contra htop
  rw [htop, ENNReal.mul_top hcoeff] at hmarkov
  exact hC (le_antisymm le_top hmarkov)

theorem kernelColSet_mono (hK : MemLp K 2 (μ.prod ν)) :
    Monotone (kernelColSet hK) := by
  intro m n hmn y hy
  have hcast : ((m : ℝ≥0∞) + 1) ≤ ((n : ℝ≥0∞) + 1) := by
    have : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hmn
    exact add_le_add_left this 1
  exact le_trans (ENNReal.inv_le_inv.mpr hcast) hy

theorem kernelColSet_iUnion (hK : MemLp K 2 (μ.prod ν)) :
    ⋃ n, kernelColSet hK n = {y | colEnergy hK y ≠ 0} := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨n, hn⟩ := hy
    have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (ENNReal.add_ne_top.mpr
        ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
    exact ne_of_gt (lt_of_lt_of_le hpos hn)
  · intro hy
    rw [Set.mem_iUnion]
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt
      (ENNReal.inv_ne_top.mpr hy)
    refine ⟨k, ?_⟩
    have hle : (colEnergy hK y)⁻¹ ≤ ((k : ℝ≥0∞) + 1) :=
      le_trans hk.le (le_add_of_nonneg_right zero_le)
    have := ENNReal.inv_le_inv.mpr hle
    rwa [inv_inv] at this

/-- The extension-by-zero representative of an `Lp` class on the
restricted measure: the indicator of its measurable representative. -/
noncomputable def zeroExtensionRep (t : Set β)
    (v : Lp ℂ 2 (ν.restrict t)) : β → ℂ :=
  t.indicator ((MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v)

theorem zeroExtensionRep_eLpNorm_sq (t : Set β) (ht : MeasurableSet t)
    (v : Lp ℂ 2 (ν.restrict t)) :
    (eLpNorm (zeroExtensionRep t v) 2 ν) ^ 2
      = (eLpNorm (⇑v) 2 (ν.restrict t)) ^ 2 := by
  have hφ : StronglyMeasurable
      ((MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v) :=
    (MeasureTheory.Lp.aestronglyMeasurable v).stronglyMeasurable_mk
  calc (eLpNorm (zeroExtensionRep t v) 2 ν) ^ 2
      = ∫⁻ y, ‖zeroExtensionRep t v y‖ₑ ^ 2 ∂ν :=
        eLpNorm_two_sq ν (hφ.indicator ht).aestronglyMeasurable
    _ = ∫⁻ y, t.indicator
          (fun y => ‖(MeasureTheory.Lp.aestronglyMeasurable v).mk
            ⇑v y‖ₑ ^ 2) y ∂ν :=
        lintegral_congr fun y => by
          by_cases hy : y ∈ t <;>
            simp [zeroExtensionRep, Set.indicator_of_mem,
              Set.indicator_of_notMem, hy]
    _ = ∫⁻ y in t,
          ‖(MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v y‖ₑ ^ 2
          ∂ν :=
        MeasureTheory.lintegral_indicator ht
          (fun y => ‖(MeasureTheory.Lp.aestronglyMeasurable v).mk
            ⇑v y‖ₑ ^ 2)
    _ = (eLpNorm ((MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v)
          2 (ν.restrict t)) ^ 2 :=
        (eLpNorm_two_sq (ν.restrict t)
          hφ.aestronglyMeasurable).symm
    _ = (eLpNorm (⇑v) 2 (ν.restrict t)) ^ 2 := by
        rw [eLpNorm_congr_ae
          (MeasureTheory.Lp.aestronglyMeasurable v).ae_eq_mk]

theorem zeroExtensionRep_memLp (t : Set β) (ht : MeasurableSet t)
    (v : Lp ℂ 2 (ν.restrict t)) :
    MemLp (zeroExtensionRep t v) 2 ν := by
  have hlt : (eLpNorm (zeroExtensionRep t v) 2 ν) ^ 2 < ∞ := by
    rw [zeroExtensionRep_eLpNorm_sq t ht v]
    exact ENNReal.pow_lt_top (MeasureTheory.Lp.memLp v)
  by_contra hcon
  have hinf : eLpNorm (zeroExtensionRep t v) 2 ν = ∞ :=
    le_antisymm le_top (not_lt.mp hcon)
  rw [hinf, pow_two, ENNReal.top_mul_top] at hlt
  exact (lt_irrefl _) hlt

/-- Extension by zero, as a plain function on `Lp` classes. -/
noncomputable def zeroExtensionFun (t : Set β) (ht : MeasurableSet t)
    (v : Lp ℂ 2 (ν.restrict t)) : Lp ℂ 2 ν :=
  (zeroExtensionRep_memLp t ht v).toLp (zeroExtensionRep t v)

theorem coeFn_zeroExtensionFun (t : Set β) (ht : MeasurableSet t)
    (v : Lp ℂ 2 (ν.restrict t)) :
    ⇑(zeroExtensionFun t ht v) =ᵐ[ν] zeroExtensionRep t v :=
  MemLp.coeFn_toLp _

theorem zeroExtensionFun_norm (t : Set β) (ht : MeasurableSet t)
    (v : Lp ℂ 2 (ν.restrict t)) :
    ‖zeroExtensionFun t ht v‖ = ‖v‖ := by
  have hnet : eLpNorm (zeroExtensionRep t v) 2 ν ≠ ∞ := by
    by_contra hcon
    have hlt : (eLpNorm (zeroExtensionRep t v) 2 ν) ^ 2 < ∞ := by
      rw [zeroExtensionRep_eLpNorm_sq t ht v]
      exact ENNReal.pow_lt_top (MeasureTheory.Lp.memLp v)
    rw [hcon, pow_two, ENNReal.top_mul_top] at hlt
    exact (lt_irrefl _) hlt
  have heq : eLpNorm (zeroExtensionRep t v) 2 ν
      = eLpNorm (⇑v) 2 (ν.restrict t) := by
    have hsq := zeroExtensionRep_eLpNorm_sq t ht v
    have h1 : (eLpNorm (zeroExtensionRep t v) 2 ν).toReal ^ 2
        = (eLpNorm (⇑v) 2 (ν.restrict t)).toReal ^ 2 := by
      rw [← ENNReal.toReal_pow, ← ENNReal.toReal_pow, hsq]
    have h2 : (eLpNorm (zeroExtensionRep t v) 2 ν).toReal
        = (eLpNorm (⇑v) 2 (ν.restrict t)).toReal := by
      have hsq' : (eLpNorm (zeroExtensionRep t v) 2 ν).toReal
            * (eLpNorm (zeroExtensionRep t v) 2 ν).toReal
          = (eLpNorm (⇑v) 2 (ν.restrict t)).toReal
            * (eLpNorm (⇑v) 2 (ν.restrict t)).toReal := by
        rw [← pow_two, ← pow_two]
        exact h1
      rcases mul_self_eq_mul_self_iff.mp hsq' with h | h
      · exact h
      · have ha : (0 : ℝ) ≤ (eLpNorm (zeroExtensionRep t v) 2 ν).toReal :=
          ENNReal.toReal_nonneg
        have hb : (0 : ℝ) ≤ (eLpNorm (⇑v) 2 (ν.restrict t)).toReal :=
          ENNReal.toReal_nonneg
        have hb0 : (eLpNorm (⇑v) 2 (ν.restrict t)).toReal = 0 := by
          linarith
        rw [h, hb0, neg_zero]
    rw [← ENNReal.ofReal_toReal hnet,
      ← ENNReal.ofReal_toReal (MeasureTheory.Lp.memLp v).ne, h2]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def,
    eLpNorm_congr_ae (coeFn_zeroExtensionFun t ht v), heq]

theorem indicator_congr_ae {t : Set β} {f g : β → ℂ}
    (ht : MeasurableSet t) (h : f =ᵐ[ν.restrict t] g) :
    t.indicator f =ᵐ[ν] t.indicator g := by
  have h' : ∀ᵐ y ∂ν, y ∈ t → f y = g y :=
    (MeasureTheory.ae_restrict_iff' ht).mp h
  filter_upwards [h'] with y hy
  by_cases hyt : y ∈ t
  · rw [Set.indicator_of_mem hyt, Set.indicator_of_mem hyt, hy hyt]
  · rw [Set.indicator_of_notMem hyt, Set.indicator_of_notMem hyt]

theorem zeroExtensionFun_add (t : Set β) (ht : MeasurableSet t)
    (v w : Lp ℂ 2 (ν.restrict t)) :
    zeroExtensionFun t ht (v + w)
      = zeroExtensionFun t ht v + zeroExtensionFun t ht w := by
  apply MeasureTheory.Lp.ext
  calc ⇑(zeroExtensionFun t ht (v + w))
      =ᵐ[ν] zeroExtensionRep t (v + w) :=
        coeFn_zeroExtensionFun t ht (v + w)
    _ =ᵐ[ν] t.indicator
          ((MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v
            + (MeasureTheory.Lp.aestronglyMeasurable w).mk ⇑w) :=
        indicator_congr_ae ht (by
          refine ((MeasureTheory.Lp.aestronglyMeasurable
            (v + w)).ae_eq_mk).symm.trans ?_
          refine (MeasureTheory.Lp.coeFn_add v w).trans ?_
          exact ((MeasureTheory.Lp.aestronglyMeasurable
            v).ae_eq_mk).add
            ((MeasureTheory.Lp.aestronglyMeasurable w).ae_eq_mk))
    _ =ᵐ[ν] t.indicator
            ((MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v)
          + t.indicator
            ((MeasureTheory.Lp.aestronglyMeasurable w).mk ⇑w) :=
        Filter.EventuallyEq.of_eq (funext fun y => by
          by_cases hy : y ∈ t <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy,
              Pi.add_apply])
    _ =ᵐ[ν] ⇑(zeroExtensionFun t ht v)
          + ⇑(zeroExtensionFun t ht w) :=
        ((coeFn_zeroExtensionFun t ht v).symm).add
          ((coeFn_zeroExtensionFun t ht w).symm)
    _ =ᵐ[ν] ⇑(zeroExtensionFun t ht v + zeroExtensionFun t ht w) :=
        (MeasureTheory.Lp.coeFn_add _ _).symm

theorem zeroExtensionFun_smul (t : Set β) (ht : MeasurableSet t)
    (c : ℂ) (v : Lp ℂ 2 (ν.restrict t)) :
    zeroExtensionFun t ht (c • v) = c • zeroExtensionFun t ht v := by
  apply MeasureTheory.Lp.ext
  calc ⇑(zeroExtensionFun t ht (c • v))
      =ᵐ[ν] zeroExtensionRep t (c • v) :=
        coeFn_zeroExtensionFun t ht (c • v)
    _ =ᵐ[ν] t.indicator
          (c • (MeasureTheory.Lp.aestronglyMeasurable v).mk ⇑v) :=
        indicator_congr_ae ht (by
          refine ((MeasureTheory.Lp.aestronglyMeasurable
            (c • v)).ae_eq_mk).symm.trans ?_
          refine (MeasureTheory.Lp.coeFn_smul c v).trans ?_
          exact ((MeasureTheory.Lp.aestronglyMeasurable
            v).ae_eq_mk).mono fun y hy => by
            simp only [Pi.smul_apply]
            rw [hy])
    _ =ᵐ[ν] c • zeroExtensionRep t v :=
        Filter.EventuallyEq.of_eq (funext fun y => by
          by_cases hy : y ∈ t <;>
            simp [zeroExtensionRep, Set.indicator_of_mem,
              Set.indicator_of_notMem, hy, Pi.smul_apply])
    _ =ᵐ[ν] c • ⇑(zeroExtensionFun t ht v) :=
        (Filter.EventuallyEq.refl (MeasureTheory.ae ν)
          (fun _ => c)).smul (coeFn_zeroExtensionFun t ht v).symm
    _ =ᵐ[ν] ⇑(c • zeroExtensionFun t ht v) :=
        (MeasureTheory.Lp.coeFn_smul c _).symm

/-- Extension by zero from `Lp ℂ 2 (ν.restrict t)` to `Lp ℂ 2 ν`,
as a continuous linear map (it is an isometry). -/
noncomputable def zeroExtension (t : Set β) (ht : MeasurableSet t) :
    Lp ℂ 2 (ν.restrict t) →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous
    { toFun := zeroExtensionFun t ht,
      map_add' := fun v w => zeroExtensionFun_add t ht v w,
      map_smul' := fun c v => zeroExtensionFun_smul t ht c v }
    1
    (fun v => by
      rw [one_mul]
      exact (zeroExtensionFun_norm t ht v).le)

theorem zeroExtension_apply (t : Set β) (ht : MeasurableSet t)
    (v : Lp ℂ 2 (ν.restrict t)) :
    zeroExtension t ht v = zeroExtensionFun t ht v :=
  rfl

/-- Indicators preserve a.e. equality, for any measure. -/
theorem indicator_congr_ae_gen {γ δ : Type*} [MeasurableSpace γ]
    [Zero δ] {s : Set γ} {f g : γ → δ} {ρ : Measure γ}
    (h : f =ᵐ[ρ] g) :
    s.indicator f =ᵐ[ρ] s.indicator g :=
  h.mono fun p hp => by
    by_cases hps : p ∈ s
    · rw [Set.indicator_of_mem hps, Set.indicator_of_mem hps, hp]
    · rw [Set.indicator_of_notMem hps, Set.indicator_of_notMem hps]

/-- The truncated kernel: the star kernel cut to the rectangle
`kernelRowSet hK m ×ˢ kernelColSet hK n`. -/
noncomputable def kernelTrunc (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) :
    α × β → ℂ :=
  (kernelRowSet hK m ×ˢ kernelColSet hK n).indicator
    (fun p => star (K p))

theorem aestronglyMeasurable_kernelTrunc_of
    {ρ : Measure (α × β)} (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ)
    (hstar : AEStronglyMeasurable (fun p => star (K p)) ρ) :
    AEStronglyMeasurable (kernelTrunc hK m n) ρ := by
  obtain ⟨Ψ, hΨSM, hΨeq⟩ := hstar
  exact ⟨(kernelRowSet hK m ×ˢ kernelColSet hK n).indicator Ψ,
    hΨSM.indicator ((kernelRowSet_measurable hK m).prod
      (kernelColSet_measurable hK n)),
    indicator_congr_ae_gen hΨeq⟩

theorem aestronglyMeasurable_kernelTrunc_prod
    (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) :
    AEStronglyMeasurable (kernelTrunc hK m n) (μ.prod ν) :=
  aestronglyMeasurable_kernelTrunc_of hK m n
    hK.aestronglyMeasurable.star

theorem aestronglyMeasurable_kernelTrunc
    (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) :
    AEStronglyMeasurable (kernelTrunc hK m n)
      ((μ.restrict (kernelRowSet hK m)).prod
        (ν.restrict (kernelColSet hK n))) := by
  rw [MeasureTheory.Measure.prod_restrict]
  exact aestronglyMeasurable_kernelTrunc_of hK m n
    ((hK.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self).star)

theorem kernelTrunc_memLp_prod (hK : MemLp K 2 (μ.prod ν))
    (m n : ℕ) :
    MemLp (kernelTrunc hK m n) 2 (μ.prod ν) := by
  show eLpNorm (kernelTrunc hK m n) 2 (μ.prod ν) < ∞
  have hsq : (eLpNorm (kernelTrunc hK m n) 2 (μ.prod ν)) ^ 2
      ≤ (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
    rw [eLpNorm_two_sq _
        (aestronglyMeasurable_kernelTrunc_prod hK m n),
      eLpNorm_two_sq _ hK.aestronglyMeasurable]
    apply lintegral_mono
    intro p
    show ‖((kernelRowSet hK m ×ˢ kernelColSet hK n).indicator
      (fun p => star (K p))) p‖ₑ ^ 2 ≤ ‖K p‖ₑ ^ 2
    by_cases hp : p ∈ kernelRowSet hK m ×ˢ kernelColSet hK n
    · rw [Set.indicator_of_mem hp]
      simp
    · rw [Set.indicator_of_notMem hp]
      simp
  have hlt : (eLpNorm (kernelTrunc hK m n) 2 (μ.prod ν)) ^ 2
      < ∞ :=
    lt_of_le_of_lt hsq (ENNReal.pow_lt_top hK)
  by_contra hcon
  have hinf : eLpNorm (kernelTrunc hK m n) 2 (μ.prod ν) = ∞ :=
    le_antisymm le_top (not_lt.mp hcon)
  rw [hinf, pow_two, ENNReal.top_mul_top] at hlt
  exact (lt_irrefl _) hlt

theorem kernelTrunc_memLp (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) :
    MemLp (kernelTrunc hK m n) 2
      ((μ.restrict (kernelRowSet hK m)).prod
        (ν.restrict (kernelColSet hK n))) := by
  rw [MeasureTheory.Measure.prod_restrict]
  exact MemLp.mono_measure Measure.restrict_le_self
    (kernelTrunc_memLp_prod hK m n)

/-- The truncated section map, extended back to `Lp ℂ 2 ν` by zero. -/
noncomputable def truncSection (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) :
    α → Lp ℂ 2 ν :=
  fun x => zeroExtension (kernelColSet hK n)
    (kernelColSet_measurable hK n)
    (sectionLp (ν := ν.restrict (kernelColSet hK n))
      (kernelTrunc hK m n) x)

theorem truncSection_aestronglyMeasurable
    (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) :
    AEStronglyMeasurable (truncSection hK m n) μ := by
  haveI : IsFiniteMeasure (μ.restrict (kernelRowSet hK m)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr
        (kernelRowSet_measure_ne_top hK m)⟩
  haveI : IsFiniteMeasure (ν.restrict (kernelColSet hK n)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr
        (kernelColSet_measure_ne_top hK n)⟩
  obtain ⟨Ψ, hΨSM, hΨeq⟩ :=
    sectionLp_aestronglyMeasurable_fin (kernelTrunc_memLp hK m n)
  refine ⟨(kernelRowSet hK m).indicator
    (fun x => zeroExtension (kernelColSet hK n)
      (kernelColSet_measurable hK n) (Ψ x)),
    ((zeroExtension (kernelColSet hK n)
      (kernelColSet_measurable hK n)).continuous.comp_stronglyMeasurable
        hΨSM).indicator (kernelRowSet_measurable hK m), ?_⟩
  have hrestr : ∀ᵐ x ∂μ, x ∈ kernelRowSet hK m →
      zeroExtension (kernelColSet hK n) (kernelColSet_measurable hK n)
          (sectionLp (ν := ν.restrict (kernelColSet hK n))
            (kernelTrunc hK m n) x)
        = zeroExtension (kernelColSet hK n)
            (kernelColSet_measurable hK n) (Ψ x) :=
    (MeasureTheory.ae_restrict_iff'
      (kernelRowSet_measurable hK m)).mp
      (hΨeq.mono fun x hx => congrArg _ hx)
  filter_upwards [hrestr] with x hx
  by_cases hxA : x ∈ kernelRowSet hK m
  · rw [Set.indicator_of_mem hxA]
    exact hx hxA
  · rw [Set.indicator_of_notMem hxA]
    have hsec0 : sectionLp (ν := ν.restrict (kernelColSet hK n))
        (kernelTrunc hK m n) x = 0 := by
      have hfun0 : (fun y => kernelTrunc hK m n (x, y)) = 0 := by
        funext y
        show (kernelRowSet hK m ×ˢ kernelColSet hK n).indicator
          (fun p => star (K p)) (x, y) = 0
        have hnotmem : (x, y) ∉ kernelRowSet hK m
            ×ˢ kernelColSet hK n := by
          intro hmem
          exact hxA (Set.mem_prod.mp hmem).1
        exact Set.indicator_of_notMem hnotmem (fun p => star (K p))
      have hmem : MemLp (fun y => kernelTrunc hK m n (x, y)) 2
          (ν.restrict (kernelColSet hK n)) := by
        rw [hfun0]
        exact MemLp.zero
      rw [sectionLp_eq_of_memLp hmem]
      apply MeasureTheory.Lp.ext
      refine (MemLp.coeFn_toLp hmem).trans ?_
      rw [hfun0]
      exact (MeasureTheory.Lp.coeFn_zero ℂ (2 : ℝ≥0∞)
        (ν.restrict (kernelColSet hK n))).symm
    show truncSection hK m n x = 0
    rw [show truncSection hK m n x
      = zeroExtension (kernelColSet hK n)
          (kernelColSet_measurable hK n)
          (sectionLp (ν := ν.restrict (kernelColSet hK n))
            (kernelTrunc hK m n) x) from rfl, hsec0, map_zero]

/-- Indicators preserve a.e. measurability. -/
theorem aemeasurable_indicator_of {γ : Type*} [MeasurableSpace γ]
    {s : Set γ} (hs : MeasurableSet s) {f : γ → ℝ≥0∞}
    {ρ : Measure γ} (hf : AEMeasurable f ρ) :
    AEMeasurable (s.indicator f) ρ := by
  obtain ⟨Ψ, hΨM, hΨeq⟩ := hf
  exact ⟨s.indicator Ψ, hΨM.indicator hs,
    indicator_congr_ae_gen hΨeq⟩

/-- The column zero set: where the column energy vanishes. -/
def kernelColZeroSet (hK : MemLp K 2 (μ.prod ν)) : Set β :=
  {y | colEnergy hK y = 0}

theorem kernelColZeroSet_measurable (hK : MemLp K 2 (μ.prod ν)) :
    MeasurableSet (kernelColZeroSet hK) :=
  colEnergy_measurable hK (measurableSet_singleton 0)

theorem iInter_compl_kernelColSet (hK : MemLp K 2 (μ.prod ν)) :
    ⋂ n, (kernelColSet hK n)ᶜ = kernelColZeroSet hK := by
  rw [← Set.compl_iUnion, kernelColSet_iUnion]
  ext y
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not,
    kernelColZeroSet]

/-- For almost every `x`, the kernel section vanishes a.e. on the
column zero set. -/
theorem section_vanishing_ae (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∫⁻ y in kernelColZeroSet hK,
      ‖K (x, y)‖ₑ ^ 2 ∂ν = 0 := by
  have hG : AEMeasurable
      (fun p : α × β => (Set.univ ×ˢ kernelColZeroSet hK).indicator
        (fun p => ‖K p‖ₑ ^ 2) p) (μ.prod ν) :=
    aemeasurable_indicator_of
      (MeasurableSet.univ.prod (kernelColZeroSet_measurable hK))
      (aemeasurable_kernel_enorm_sq hK)
  have hinner : (fun x => ∫⁻ y in kernelColZeroSet hK,
        ‖K (x, y)‖ₑ ^ 2 ∂ν)
      = fun x => ∫⁻ y, (Set.univ ×ˢ kernelColZeroSet hK).indicator
          (fun p => ‖K p‖ₑ ^ 2) (x, y) ∂ν := by
    funext x
    rw [← MeasureTheory.lintegral_indicator
      (kernelColZeroSet_measurable hK)]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ kernelColZeroSet hK
    · rw [Set.indicator_of_mem (by
        exact ⟨Set.mem_univ x, hy⟩ : (x, y) ∈
          Set.univ ×ˢ kernelColZeroSet hK),
        Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (by
        intro h
        exact hy (Set.mem_prod.mp h).2 : (x, y) ∉
          Set.univ ×ˢ kernelColZeroSet hK),
        Set.indicator_of_notMem hy]
  have htotal : ∫⁻ x, ∫⁻ y in kernelColZeroSet hK,
      ‖K (x, y)‖ₑ ^ 2 ∂ν ∂μ = 0 := by
    have hstep1 : ∫⁻ x, ∫⁻ y in kernelColZeroSet hK,
          ‖K (x, y)‖ₑ ^ 2 ∂ν ∂μ
        = ∫⁻ y, ∫⁻ x, (Set.univ ×ˢ kernelColZeroSet hK).indicator
            (fun p => ‖K p‖ₑ ^ 2) (x, y) ∂μ ∂ν := by
      rw [hinner, ← MeasureTheory.lintegral_prod _ hG]
      exact MeasureTheory.lintegral_prod_symm _ hG
    rw [hstep1]
    have hstep2 : (fun y => ∫⁻ x,
          (Set.univ ×ˢ kernelColZeroSet hK).indicator
            (fun p => ‖K p‖ₑ ^ 2) (x, y) ∂μ)
        = (kernelColZeroSet hK).indicator
            (fun y => ∫⁻ x, ‖K (x, y)‖ₑ ^ 2 ∂μ) := by
      funext y
      by_cases hy : y ∈ kernelColZeroSet hK
      · rw [Set.indicator_of_mem hy]
        apply lintegral_congr
        intro x
        have hxy : (x, y) ∈ Set.univ ×ˢ kernelColZeroSet hK :=
          Set.mem_prod.mpr ⟨Set.mem_univ x, hy⟩
        rw [Set.indicator_of_mem hxy]
      · rw [Set.indicator_of_notMem hy]
        have hfun : (fun x => (Set.univ ×ˢ kernelColZeroSet hK).indicator
            (fun p => ‖K p‖ₑ ^ 2) (x, y)) = fun _ => 0 :=
          funext fun x => Set.indicator_of_notMem
            (fun h => hy (Set.mem_prod.mp h).2)
            (fun p => ‖K p‖ₑ ^ 2)
        rw [hfun]
        simp
    rw [hstep2, MeasureTheory.lintegral_indicator
      (kernelColZeroSet_measurable hK)]
    have hrestr : (fun y => ∫⁻ x, ‖K (x, y)‖ₑ ^ 2 ∂μ)
        =ᵐ[ν.restrict (kernelColZeroSet hK)] colEnergy hK :=
      (colEnergy_ae_eq hK).filter_mono
        (MeasureTheory.ae_mono Measure.restrict_le_self)
    rw [lintegral_congr_ae hrestr,
      ← MeasureTheory.lintegral_indicator
        (kernelColZeroSet_measurable hK)]
    have hzero : (kernelColZeroSet hK).indicator (colEnergy hK)
        = fun _ => 0 := by
      funext y
      by_cases hy : y ∈ kernelColZeroSet hK
      · rw [Set.indicator_of_mem hy]
        exact hy
      · exact Set.indicator_of_notMem hy _
    rw [hzero]
    simp
  have hAMinner : AEMeasurable (fun x => ∫⁻ y in
      kernelColZeroSet hK, ‖K (x, y)‖ₑ ^ 2 ∂ν) μ := by
    have h := hG.lintegral_prod_right'
    rwa [← hinner] at h
  exact (MeasureTheory.lintegral_eq_zero_iff' hAMinner).mp htotal

/-- For a good `x`, the set-lintegrals of the squared section over
the shrinking column complements converge to the integral over the
column zero set. -/
theorem tendsto_setLIntegral_compl_kernelColSet
    (hK : MemLp K 2 (μ.prod ν)) (x : α) (g : β → ℝ≥0∞)
    (hgM : Measurable g)
    (hgeq : (fun y => ‖K (x, y)‖ₑ ^ 2) =ᵐ[ν] g)
    (hfin : ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν < ∞) :
    Tendsto (fun n => ∫⁻ y in (kernelColSet hK n)ᶜ,
        ‖K (x, y)‖ₑ ^ 2 ∂ν) atTop
      (𝓝 (∫⁻ y in kernelColZeroSet hK,
        ‖K (x, y)‖ₑ ^ 2 ∂ν)) := by
  set ρ : Measure β := ν.withDensity g with hρdef
  have hρ : ∀ s : Set β, MeasurableSet s →
      ρ s = ∫⁻ y in s, ‖K (x, y)‖ₑ ^ 2 ∂ν := by
    intro s hs
    rw [hρdef, MeasureTheory.withDensity_apply g hs]
    apply MeasureTheory.setLIntegral_congr_fun_ae hs
    exact hgeq.symm.mono fun y hy _ => hy
  have htend := MeasureTheory.tendsto_measure_iInter_atTop
    (s := fun n => (kernelColSet hK n)ᶜ)
    (fun n => (kernelColSet_measurable hK n).compl.nullMeasurableSet)
    (fun a b hab => Set.compl_subset_compl.mpr
      (kernelColSet_mono hK hab))
    ⟨0, by
      rw [hρ _ (kernelColSet_measurable hK 0).compl]
      exact ne_top_of_le_ne_top hfin.ne
        (MeasureTheory.setLIntegral_le_lintegral _ _)⟩
  have hlim : ρ (⋂ n, (kernelColSet hK n)ᶜ)
      = ∫⁻ y in kernelColZeroSet hK, ‖K (x, y)‖ₑ ^ 2 ∂ν := by
    rw [iInter_compl_kernelColSet hK]
    exact hρ _ (kernelColZeroSet_measurable hK)
  rw [hlim] at htend
  refine htend.congr (fun n => ?_)
  rw [Function.comp_apply]
  exact hρ _ (kernelColSet_measurable hK n).compl

/-- The truncated kernel is pointwise dominated by the kernel. -/
theorem kernelTrunc_enorm_sq_le (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ)
    (p : α × β) : ‖kernelTrunc hK m n p‖ₑ ^ 2 ≤ ‖K p‖ₑ ^ 2 := by
  by_cases hp : p ∈ kernelRowSet hK m ×ˢ kernelColSet hK n
  · rw [kernelTrunc, Set.indicator_of_mem hp]
    simp
  · rw [kernelTrunc, Set.indicator_of_notMem hp]
    simp

/-- The section operator agrees with the `MemLp.toLp` representative
(general-measure form of the finite-section lemma). -/
theorem sectionLp_eq_of_memLp_gen {M : α × β → ℂ} {x : α}
    (h : MemLp (fun y => M (x, y)) 2 ν) :
    sectionLp M x = h.toLp (fun y => M (x, y)) := by
  classical
  exact dif_pos h

/-- The section operator vanishes off the `MemLp` locus
(general-measure form). -/
theorem sectionLp_eq_zero_of_notMemLp_gen {M : α × β → ℂ} {x : α}
    (h : ¬ MemLp (fun y => M (x, y)) 2 ν) :
    sectionLp (ν := ν) M x = 0 := by
  classical
  exact dif_neg h

/-- For `x` in the `m`-th row set, the truncated section is `MemLp`
on the restricted column measure. -/
theorem kernelTrunc_section_memLp_of_mem_row
    (hK : MemLp K 2 (μ.prod ν)) (m n : ℕ) {x : α}
    (hxA : x ∈ kernelRowSet hK m)
    (hsec : MemLp (fun y => star (K (x, y))) 2 ν) :
    MemLp (fun y => kernelTrunc hK m n (x, y)) 2
      (ν.restrict (kernelColSet hK n)) := by
  have hfun_eq : (fun y => kernelTrunc hK m n (x, y))
      = (kernelColSet hK n).indicator
          (fun y => star (K (x, y))) := by
    funext y
    by_cases hy : y ∈ kernelColSet hK n
    · rw [kernelTrunc, Set.indicator_of_mem
        (Set.mem_prod.mpr ⟨hxA, hy⟩), Set.indicator_of_mem hy]
    · rw [kernelTrunc, Set.indicator_of_notMem
        (fun h => hy (Set.mem_prod.mp h).2),
        Set.indicator_of_notMem hy]
  rw [hfun_eq]
  exact (hsec.indicator
    (kernelColSet_measurable hK n).nullMeasurableSet).mono_measure
    Measure.restrict_le_self

/-- The diagonal truncations converge a.e. to the (starred) section
map. -/
theorem sectionStar_tendsto_ae (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => truncSection hK n n x) atTop
      (𝓝 (sectionLp (ν := ν) (fun p => star (K p)) x)) := by
  filter_upwards [memLp_section_ae_gen hK,
    rowEnergy_ae_eq hK, section_vanishing_ae hK]
    with x hsecK hrow hvan
  have hsecStar : MemLp (fun y => star (K (x, y))) 2 ν := hsecK.star
  obtain ⟨g, hgM, hgeq⟩ : ∃ g : β → ℝ≥0∞, Measurable g ∧
      (fun y => ‖K (x, y)‖ₑ ^ 2) =ᵐ[ν] g := by
    refine ⟨fun y => ‖(hsecK.aestronglyMeasurable.mk
      (fun y => K (x, y))) y‖ₑ
        * ‖(hsecK.aestronglyMeasurable.mk
          (fun y => K (x, y))) y‖ₑ, ?_, ?_⟩
    · have h1 := hsecK.aestronglyMeasurable.measurable_mk.enorm
      exact h1.mul h1
    · refine hsecK.aestronglyMeasurable.ae_eq_mk.mono fun y hy => ?_
      show ‖K (x, y)‖ₑ ^ 2
        = ‖(hsecK.aestronglyMeasurable.mk (fun y => K (x, y))) y‖ₑ
          * ‖(hsecK.aestronglyMeasurable.mk (fun y => K (x, y))) y‖ₑ
      rw [show K (x, y) = (hsecK.aestronglyMeasurable.mk
        (fun y => K (x, y))) y from hy, pow_two]
  have hfin : ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν < ∞ := by
    have h := eLpNorm_two_sq ν hsecK.aestronglyMeasurable
    rw [← h]
    exact ENNReal.pow_lt_top hsecK
  have hSrep : ⇑(sectionLp (ν := ν) (fun p => star (K p)) x)
      =ᵐ[ν] (fun y => star (K (x, y))) := by
    rw [sectionLp_eq_of_memLp_gen hsecStar]
    exact MemLp.coeFn_toLp hsecStar
  by_cases hrowx : rowEnergy hK x = 0
  · -- zero row energy: both sides vanish
    have hraw0 : ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν = 0 := hrow.trans hrowx
    have hS0 : sectionLp (ν := ν) (fun p => star (K p)) x = 0 := by
      apply norm_eq_zero.mp
      rw [MeasureTheory.Lp.norm_def]
      have e1 : (eLpNorm (fun y => star (K (x, y))) 2 ν) ^ 2 = 0 := by
        rw [eLpNorm_two_sq ν hsecStar.aestronglyMeasurable]
        have hstar : (∫⁻ y, ‖star (K (x, y))‖ₑ ^ 2 ∂ν)
            = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν :=
          lintegral_congr fun y => by simp
        rw [hstar, hraw0]
      have heLp : eLpNorm (⇑(sectionLp (ν := ν)
          (fun p => star (K p)) x)) 2 ν = 0 := by
        have h2 := (pow_eq_zero_iff two_ne_zero).mp e1
        rwa [← eLpNorm_congr_ae hSrep] at h2
      rw [show (eLpNorm (⇑(sectionLp (ν := ν) (fun p => star (K p)) x))
          2 ν) = 0 from heLp]
      exact ENNReal.toReal_zero
    have hT0 : ∀ n, truncSection hK n n x = 0 := by
      intro n
      have hsec0 : sectionLp (ν := ν.restrict (kernelColSet hK n))
          (kernelTrunc hK n n) x = 0 := by
        by_cases hmem : MemLp (fun y => kernelTrunc hK n n (x, y)) 2
            (ν.restrict (kernelColSet hK n))
        · rw [sectionLp_eq_of_memLp_gen hmem]
          apply norm_eq_zero.mp
          rw [MeasureTheory.Lp.norm_def]
          have e1 : (eLpNorm (fun y => kernelTrunc hK n n (x, y)) 2
              (ν.restrict (kernelColSet hK n))) ^ 2 = 0 := by
            rw [eLpNorm_two_sq _ hmem.aestronglyMeasurable]
            apply le_antisymm _ zero_le
            refine le_trans (MeasureTheory.setLIntegral_mono'
              (kernelColSet_measurable hK n)
              (fun y _ => kernelTrunc_enorm_sq_le hK n n (x, y))) ?_
            exact le_trans (MeasureTheory.setLIntegral_le_lintegral
              _ _) (le_of_eq hraw0)
          have heLp : eLpNorm (fun y => kernelTrunc hK n n (x, y)) 2
              (ν.restrict (kernelColSet hK n)) = 0 :=
            (pow_eq_zero_iff two_ne_zero).mp e1
          rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hmem), heLp]
          simp
        · exact sectionLp_eq_zero_of_notMemLp_gen hmem
      rw [show truncSection hK n n x
        = zeroExtension (kernelColSet hK n)
            (kernelColSet_measurable hK n)
            (sectionLp (ν := ν.restrict (kernelColSet hK n))
              (kernelTrunc hK n n) x) from rfl, hsec0, map_zero]
    rw [hS0]
    exact tendsto_const_nhds.congr (fun n => (hT0 n).symm)
  · -- positive row energy: the row sets eventually cover `x`
    obtain ⟨N, hN⟩ : ∃ N, x ∈ kernelRowSet hK N := by
      have hx : x ∈ ⋃ n, kernelRowSet hK n := by
        rw [kernelRowSet_iUnion]
        exact hrowx
      exact Set.mem_iUnion.mp hx
    have hnorm : ∀ n, N ≤ n →
        ‖truncSection hK n n x
            - sectionLp (ν := ν) (fun p => star (K p)) x‖
          = Real.sqrt ((∫⁻ y in (kernelColSet hK n)ᶜ,
              ‖K (x, y)‖ₑ ^ 2 ∂ν).toReal) := by
      intro n hn
      have hxA : x ∈ kernelRowSet hK n :=
        kernelRowSet_mono hK hn hN
      have hmem : MemLp (fun y => kernelTrunc hK n n (x, y)) 2
          (ν.restrict (kernelColSet hK n)) :=
        kernelTrunc_section_memLp_of_mem_row hK n n hxA hsecStar
      have hWrep : ⇑(sectionLp (ν := ν.restrict (kernelColSet hK n))
            (kernelTrunc hK n n) x)
          =ᵐ[ν.restrict (kernelColSet hK n)]
            (fun y => kernelTrunc hK n n (x, y)) := by
        rw [sectionLp_eq_of_memLp_gen hmem]
        exact MemLp.coeFn_toLp hmem
      have hpoint : ∀ y, kernelTrunc hK n n (x, y)
          = (kernelColSet hK n).indicator
              (fun y => star (K (x, y))) y := by
        intro y
        by_cases hy : y ∈ kernelColSet hK n
        · rw [kernelTrunc, Set.indicator_of_mem
            (Set.mem_prod.mpr ⟨hxA, hy⟩), Set.indicator_of_mem hy]
        · rw [kernelTrunc, Set.indicator_of_notMem
            (fun h => hy (Set.mem_prod.mp h).2),
            Set.indicator_of_notMem hy]
      have hTrep : ⇑(truncSection hK n n x)
          =ᵐ[ν] (kernelColSet hK n).indicator
            (fun y => star (K (x, y))) := by
        have hval : truncSection hK n n x
            = zeroExtensionFun (kernelColSet hK n)
                (kernelColSet_measurable hK n)
                (sectionLp (ν := ν.restrict (kernelColSet hK n))
                  (kernelTrunc hK n n) x) :=
          zeroExtension_apply _ _ _
        rw [hval]
        refine (coeFn_zeroExtensionFun _ _ _).trans ?_
        have hmk : (Lp.aestronglyMeasurable
              (sectionLp (ν := ν.restrict (kernelColSet hK n))
                (kernelTrunc hK n n) x)).mk
              ⇑(sectionLp (ν := ν.restrict (kernelColSet hK n))
                (kernelTrunc hK n n) x)
            =ᵐ[ν.restrict (kernelColSet hK n)]
              (fun y => kernelTrunc hK n n (x, y)) :=
          (Lp.aestronglyMeasurable _).ae_eq_mk.symm.trans hWrep
        refine (indicator_congr_ae
          (kernelColSet_measurable hK n) hmk).trans ?_
        apply Filter.EventuallyEq.of_eq
        have hfun_eq : (fun y => kernelTrunc hK n n (x, y))
            = (kernelColSet hK n).indicator
                (fun y => star (K (x, y))) :=
          funext hpoint
        rw [hfun_eq]
        funext y
        by_cases hy : y ∈ kernelColSet hK n
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      have hdiff : ⇑(truncSection hK n n x
            - sectionLp (ν := ν) (fun p => star (K p)) x)
          =ᵐ[ν] (fun y => -((kernelColSet hK n)ᶜ.indicator
              (fun y => star (K (x, y))) y)) := by
        refine (MeasureTheory.Lp.coeFn_sub _ _).trans ?_
        refine (hTrep.sub hSrep).trans ?_
        refine Filter.Eventually.of_forall fun y => ?_
        show (kernelColSet hK n).indicator
              (fun y => star (K (x, y))) y - star (K (x, y))
            = -((kernelColSet hK n)ᶜ.indicator
                (fun y => star (K (x, y))) y)
        by_cases hy : y ∈ kernelColSet hK n
        · rw [Set.indicator_of_mem hy,
            Set.indicator_of_notMem
              (fun hmem => (Set.mem_compl_iff _ _).mp hmem hy),
            neg_zero, sub_self]
        · rw [Set.indicator_of_notMem hy,
            Set.indicator_of_mem (Set.mem_compl hy), zero_sub]
      have hsq : ‖truncSection hK n n x
            - sectionLp (ν := ν) (fun p => star (K p)) x‖ ^ 2
          = (∫⁻ y in (kernelColSet hK n)ᶜ,
              ‖K (x, y)‖ₑ ^ 2 ∂ν).toReal := by
        have e1 : (eLpNorm ⇑(truncSection hK n n x
              - sectionLp (ν := ν) (fun p => star (K p)) x) 2 ν) ^ 2
            = ∫⁻ y in (kernelColSet hK n)ᶜ,
                ‖K (x, y)‖ₑ ^ 2 ∂ν := by
          rw [eLpNorm_congr_ae hdiff, eLpNorm_two_sq ν
            ((MeasureTheory.Lp.aestronglyMeasurable _).congr hdiff)]
          rw [← MeasureTheory.lintegral_indicator
            (kernelColSet_measurable hK n).compl]
          apply lintegral_congr
          intro y
          by_cases hy : y ∈ (kernelColSet hK n)ᶜ
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
            simp
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
            simp
        calc ‖truncSection hK n n x
                - sectionLp (ν := ν) (fun p => star (K p)) x‖ ^ 2
            = ((eLpNorm ⇑(truncSection hK n n x
                - sectionLp (ν := ν) (fun p => star (K p)) x)
                  2 ν) ^ 2).toReal := by
              rw [MeasureTheory.Lp.norm_def]
              exact (ENNReal.toReal_pow _ _).symm
          _ = (∫⁻ y in (kernelColSet hK n)ᶜ,
                ‖K (x, y)‖ₑ ^ 2 ∂ν).toReal := by rw [e1]
      rw [← hsq]
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    have hlim0 : Tendsto (fun n => ∫⁻ y in (kernelColSet hK n)ᶜ,
        ‖K (x, y)‖ₑ ^ 2 ∂ν) atTop (𝓝 0) :=
      hvan ▸ tendsto_setLIntegral_compl_kernelColSet hK x g hgM
        hgeq hfin
    have hsqrt : Tendsto (fun n => Real.sqrt
        ((∫⁻ y in (kernelColSet hK n)ᶜ,
          ‖K (x, y)‖ₑ ^ 2 ∂ν).toReal)) atTop (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ∞
        by simp)).comp hlim0
      have h2 := (Real.continuous_sqrt.tendsto _).comp h1
      simpa only [Function.comp_def, ENNReal.toReal_zero,
        Real.sqrt_zero] using h2
    have hev : (fun n => Real.sqrt ((∫⁻ y in (kernelColSet hK n)ᶜ,
          ‖K (x, y)‖ₑ ^ 2 ∂ν).toReal))
        =ᶠ[atTop] (fun n => ‖truncSection hK n n x
          - sectionLp (ν := ν) (fun p => star (K p)) x‖) :=
      Filter.eventually_atTop.mpr ⟨N, fun n hn => (hnorm n hn).symm⟩
    exact tendsto_sub_nhds_zero_iff.mp
      (tendsto_zero_iff_norm_tendsto_zero.mpr (hsqrt.congr' hev))

/-- **Assembly capstone**: the section map of the starred kernel is
a.e. strongly measurable (in the SFinite generality). -/
theorem sectionStar_aestronglyMeasurable (hK : MemLp K 2 (μ.prod ν)) :
    AEStronglyMeasurable (sectionLp (ν := ν) (fun p => star (K p))) μ :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => truncSection_aestronglyMeasurable hK n n)
    (sectionStar_tendsto_ae hK)

/-- The support of the kernel operator on a Hilbert basis: the
countable set of basis indices with nonzero image. -/
noncomputable def kernelSupport (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) : Set ι :=
  Function.support (hsSummandENN hK b)

theorem kernelSupport_countable (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    (kernelSupport hK b).Countable :=
  hs_support_countable hK b

theorem mem_kernelSupport (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (i : ι) :
    i ∈ kernelSupport hK b ↔ integralKernelOp hK (b i) ≠ 0 := by
  have hnorm : (eLpNorm (⇑(integralKernelOp hK (b i))) 2 μ) = 0
      ↔ integralKernelOp hK (b i) = 0 := by
    constructor
    · intro h
      apply norm_eq_zero.mp
      rw [MeasureTheory.Lp.norm_def, h]
      exact ENNReal.toReal_zero
    · intro h
      rw [h]
      have h0 : ⇑(0 : Lp ℂ 2 μ) =ᵐ[μ] (0 : α → ℂ) :=
        MeasureTheory.Lp.coeFn_zero ℂ 2 μ
      rw [eLpNorm_congr_ae h0]
      exact eLpNorm_zero
  show hsSummandENN hK b i ≠ 0 ↔ integralKernelOp hK (b i) ≠ 0
  exact (pow_ne_zero_iff two_ne_zero).trans (not_congr hnorm)

theorem notMem_kernelSupport (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) {i : ι}
    (hi : i ∉ kernelSupport hK b) :
    integralKernelOp hK (b i) = 0 := by
  by_contra hne
  exact hi ((mem_kernelSupport hK b i).mpr hne)

/-- The closed span of the basis vectors with nonzero image under
the kernel operator. -/
noncomputable def kernelSpanClosure (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  (Submodule.span ℂ (⇑b '' kernelSupport hK b)).topologicalClosure

theorem basis_mem_kernelSpanClosure (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) {i : ι}
    (hi : i ∈ kernelSupport hK b) :
    (b i : Lp ℂ 2 ν) ∈ kernelSpanClosure hK b :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem basis_mem_kernelSpanClosure_orthogonal
    (hK : MemLp K 2 (μ.prod ν)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) {i : ι}
    (hi : i ∉ kernelSupport hK b) :
    (b i : Lp ℂ 2 ν) ∈ (kernelSpanClosure hK b)ᗮ := by
  classical
  have horth : ∀ j k : ι, ⟪(b j : Lp ℂ 2 ν), (b k : Lp ℂ 2 ν)⟫
      = if j = k then 1 else 0 :=
    fun j k => orthonormal_iff_ite.mp (b.orthonormal) j k
  have hspan : ∀ u ∈ Submodule.span ℂ
      (⇑b '' kernelSupport hK b), ⟪u, (b i : Lp ℂ 2 ν)⟫ = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨j, hj, rfl⟩ := hw
        have hji : j ≠ i := by
          intro h
          exact hi (h ▸ hj)
        rw [horth j i, if_neg hji]
    | zero => simp
    | add w₁ w₂ _ _ ih₁ ih₂ =>
        rw [inner_add_left, ih₁, ih₂, add_zero]
    | smul c w _ ih =>
        rw [inner_smul_left, ih, mul_zero]
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hu' : u ∈ closure
      ((Submodule.span ℂ (⇑b '' kernelSupport hK b) :
        Submodule ℂ (Lp ℂ 2 ν)) : Set (Lp ℂ 2 ν)) := hu
  have hclosed : IsClosed {u : Lp ℂ 2 ν | ⟪u, (b i : Lp ℂ 2 ν)⟫ = 0} :=
    isClosed_singleton.preimage
      (continuous_id.inner continuous_const)
  exact closure_minimal (fun u hu => hspan u hu) hclosed hu'

/-- The kernel operator vanishes on the orthogonal complement of
its basis support span. -/
theorem integralKernelOp_eq_zero_of_mem_orthogonal
    (hK : MemLp K 2 (μ.prod ν)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) {z : Lp ℂ 2 ν}
    (hz : z ∈ (kernelSpanClosure hK b)ᗮ) :
    integralKernelOp hK z = 0 := by
  have hsum := (b.hasSum_repr z).mapL (integralKernelOp hK)
  have hfun : (fun i => integralKernelOp hK (b.repr z i • (b i)))
      = (fun i => ⟪b i, z⟫ • integralKernelOp hK (b i)) := by
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply]
  rw [hfun] at hsum
  have hzero : ∀ i, ⟪b i, z⟫ • integralKernelOp hK (b i) = 0 := by
    intro i
    by_cases hi : i ∈ kernelSupport hK b
    · rw [hz (b i) (basis_mem_kernelSpanClosure hK b hi), zero_smul]
    · rw [notMem_kernelSupport hK b hi, smul_zero]
  refine hsum.unique ?_
  have hfun0 : (fun i => ⟪b i, z⟫ • integralKernelOp hK (b i))
      = (fun _ : ι => (0 : Lp ℂ 2 μ)) :=
    funext fun i => hzero i
  rw [hfun0]
  exact hasSum_zero

/-- The inner product of a kernel section with a fixed vector is
the integral kernel pairing, a.e. -/
theorem inner_sectionLp_eq (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ∀ᵐ x ∂μ, ⟪sectionLp (ν := ν) (fun p => star (K p)) x, f⟫
      = integralKernelFun ν K ⇑f x := by
  filter_upwards [memLp_section_ae_gen hK.star] with x hsecstar'
  have hsecstar : MemLp (fun y => star (K (x, y))) 2 ν := hsecstar'
  rw [sectionLp_eq_of_memLp_gen hsecstar,
    MeasureTheory.L2.inner_def]
  show (∫ y, ⟪⇑(hsecstar.toLp (fun y => star (K (x, y)))) y,
        ⇑f y⟫ ∂ν)
    = ∫ y, K (x, y) * ⇑f y ∂ν
  apply integral_congr_ae
  filter_upwards [hsecstar.coeFn_toLp] with y hy
  rw [RCLike.inner_apply, hy, starRingEnd_apply, star_star,
    mul_comm]

/-- The squared norm of a kernel section is the row energy, in
`ℝ≥0∞` form, a.e. -/
theorem section_ofReal_norm_sq_eq (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∀ _hz : MemLp (fun y => K (x, y)) 2 ν,
      ENNReal.ofReal
          (‖sectionLp (ν := ν) (fun p => star (K p)) x‖ ^ 2)
        = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν := by
  filter_upwards [memLp_section_ae_gen hK] with x _ hz
  have hsecstar : MemLp (fun y => star (K (x, y))) 2 ν := hz.star
  rw [sectionLp_eq_of_memLp_gen hsecstar]
  have e1 : ENNReal.ofReal
        (‖hsecstar.toLp (fun y => star (K (x, y)))‖ ^ 2)
      = (eLpNorm (fun y => star (K (x, y))) 2 ν) ^ 2 := by
    rw [MeasureTheory.Lp.norm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp hsecstar),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hsecstar.eLpNorm_lt_top.ne]
  rw [e1, eLpNorm_two_sq _ hsecstar.aestronglyMeasurable]
  apply lintegral_congr
  intro y
  simp [enorm]

/-- **Pointwise Parseval identity over the countable support**:
a.e., the sum over the countable support of the squared pointwise
pairings equals the row energy. The proof is the separable-range
residual argument: the section map lands, a.e., in the closed span
of its basis support, because the residual against that span is
orthogonal to a countable dense subset of the separable space it
lives in, hence vanishes. -/
theorem hs_identity_subtype_ae (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    ∀ᵐ x ∂μ, ∑' i : ↥(kernelSupport hK b),
        ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2
      = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν := by
  classical
  haveI : Countable ↥(kernelSupport hK b) :=
    kernelSupport_countable hK b
  haveI : CompleteSpace ↥(kernelSpanClosure hK b) :=
    (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe
  obtain ⟨Ψ, hΨSM, hΨeq⟩ := sectionStar_aestronglyMeasurable hK
  set Z : Submodule ℂ (Lp ℂ 2 ν) :=
    (Submodule.span ℂ (Set.range Ψ
      ∪ Set.range (fun x => (kernelSpanClosure hK b).starProjection
          (Ψ x))
      ∪ ⇑b '' kernelSupport hK b)).topologicalClosure with hZdef
  have hsep1 : TopologicalSpace.IsSeparable (Set.range Ψ) :=
    hΨSM.isSeparable_range
  have hSM2 : StronglyMeasurable
      (fun x => (kernelSpanClosure hK b).starProjection (Ψ x)) :=
    (kernelSpanClosure hK b).starProjection.continuous.comp_stronglyMeasurable
      hΨSM
  have hsep2 : TopologicalSpace.IsSeparable
      (Set.range (fun x => (kernelSpanClosure hK b).starProjection
        (Ψ x))) :=
    hSM2.isSeparable_range
  have hsep3 : TopologicalSpace.IsSeparable
      (⇑b '' kernelSupport hK b) :=
    ((kernelSupport_countable hK b).image ⇑b).isSeparable
  have hZsep : TopologicalSpace.IsSeparable
      (Z : Set (Lp ℂ 2 ν)) := by
    rw [hZdef, Submodule.topologicalClosure_coe]
    exact TopologicalSpace.isSeparable_closure.mpr
      (TopologicalSpace.IsSeparable.span (R := ℂ)
        ((hsep1.union hsep2).union hsep3))
  have hWsep : TopologicalSpace.IsSeparable
      ((Z ⊓ (kernelSpanClosure hK b)ᗮ : Submodule ℂ (Lp ℂ 2 ν)) :
        Set (Lp ℂ 2 ν)) :=
    hZsep.mono (fun x hx =>
      (Submodule.mem_inf.mp (show x ∈ Z ⊓ (kernelSpanClosure hK b)ᗮ
        from hx)).1)
  obtain ⟨c, hcCount, hWclos⟩ := hWsep
  set t : Set (Lp ℂ 2 ν) :=
    (fun e => e - (kernelSpanClosure hK b).starProjection e) '' c
    with htdef
  have htcount : t.Countable := hcCount.image _
  haveI : Countable ↥t := htcount
  have hEe : ∀ e : ↥t, (e : Lp ℂ 2 ν)
      ∈ (kernelSpanClosure hK b)ᗮ := by
    intro e
    obtain ⟨e₀, -, he₀⟩ := e.2
    rw [← he₀]
    exact Submodule.sub_starProjection_mem_orthogonal _
  have hvan : ∀ e : ↥t, ∀ᵐ x ∂μ,
      ⟪sectionLp (ν := ν) (fun p => star (K p)) x
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x),
        (e : Lp ℂ 2 ν)⟫ = 0 := by
    intro e
    have hSe : integralKernelOp hK (e : Lp ℂ 2 ν) = 0 :=
      integralKernelOp_eq_zero_of_mem_orthogonal hK b (hEe e)
    have hge : integralKernelFun ν K ⇑(e : Lp ℂ 2 ν) =ᵐ[μ] 0 :=
      (coeFn_integralKernelOp hK _).symm.trans
        (show ⇑(integralKernelOp hK (e : Lp ℂ 2 ν)) =ᵐ[μ]
          (0 : α → ℂ) by
          rw [hSe]; exact MeasureTheory.Lp.coeFn_zero ℂ 2 μ)
    have hproj : ∀ x, ⟪(kernelSpanClosure hK b).starProjection
        (sectionLp (ν := ν) (fun p => star (K p)) x),
        (e : Lp ℂ 2 ν)⟫ = 0 :=
      fun x => (hEe e) _ (Submodule.starProjection_apply_mem _ _)
    filter_upwards [inner_sectionLp_eq hK (e : Lp ℂ 2 ν), hge]
      with x hx hxge
    rw [inner_sub_left, hx, hproj x, sub_zero]
    exact hxge
  have hall_van : ∀ᵐ x ∂μ, ∀ e : ↥t,
      ⟪sectionLp (ν := ν) (fun p => star (K p)) x
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x),
        (e : Lp ℂ 2 ν)⟫ = 0 :=
    (MeasureTheory.ae_all_iff).mpr hvan
  have hall_inner : ∀ᵐ x ∂μ, ∀ i : ↥(kernelSupport hK b),
      ⟪sectionLp (ν := ν) (fun p => star (K p)) x,
        (b i : Lp ℂ 2 ν)⟫
        = integralKernelFun ν K ⇑(b i) x :=
    (MeasureTheory.ae_all_iff).mpr
      (fun i => inner_sectionLp_eq hK (b i))
  have hpt : ∀ y : ℂ, ENNReal.ofReal (‖y‖ ^ 2) = ‖y‖ₑ ^ 2 :=
    fun y => by simp [enorm, ENNReal.ofReal_pow]
  filter_upwards [hΨeq, memLp_section_ae_gen hK,
    section_ofReal_norm_sq_eq hK, hall_inner, hall_van]
    with x hxΨeq hz hxnorm hxinner hxvan
  -- the residual at `x`, and its vanishing
  have hŨZ : sectionLp (ν := ν) (fun p => star (K p)) x ∈ Z := by
    rw [hxΨeq]
    show Ψ x ∈ (Submodule.span ℂ (Set.range Ψ
      ∪ Set.range (fun x => (kernelSpanClosure hK b).starProjection
          (Ψ x))
      ∪ ⇑b '' kernelSupport hK b)).topologicalClosure
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_range_self x))))
  have hPZ : (kernelSpanClosure hK b).starProjection
      (sectionLp (ν := ν) (fun p => star (K p)) x) ∈ Z := by
    rw [hxΨeq]
    show (kernelSpanClosure hK b).starProjection (Ψ x)
      ∈ (Submodule.span ℂ (Set.range Ψ
        ∪ Set.range (fun x =>
            (kernelSpanClosure hK b).starProjection (Ψ x))
        ∪ ⇑b '' kernelSupport hK b)).topologicalClosure
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_union_left _
        (Set.mem_union_right _ (Set.mem_range_self x))))
  have hrZ : sectionLp (ν := ν) (fun p => star (K p)) x
      - (kernelSpanClosure hK b).starProjection
          (sectionLp (ν := ν) (fun p => star (K p)) x) ∈ Z :=
    Z.sub_mem hŨZ hPZ
  have hrE : sectionLp (ν := ν) (fun p => star (K p)) x
      - (kernelSpanClosure hK b).starProjection
          (sectionLp (ν := ν) (fun p => star (K p)) x)
      ∈ (kernelSpanClosure hK b)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  have hrW : sectionLp (ν := ν) (fun p => star (K p)) x
      - (kernelSpanClosure hK b).starProjection
          (sectionLp (ν := ν) (fun p => star (K p)) x)
      ∈ Z ⊓ (kernelSpanClosure hK b)ᗮ :=
    Submodule.mem_inf.mpr ⟨hrZ, hrE⟩
  have hrclos : sectionLp (ν := ν) (fun p => star (K p)) x
      - (kernelSpanClosure hK b).starProjection
          (sectionLp (ν := ν) (fun p => star (K p)) x)
      ∈ closure t := by
    have hφcont : Continuous
        (fun e : Lp ℂ 2 ν => e
          - (kernelSpanClosure hK b).starProjection e) :=
      continuous_id.sub
        (kernelSpanClosure hK b).starProjection.continuous
    have hPr : (kernelSpanClosure hK b).starProjection
        (sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x)) = 0 := by
      have hidem : (kernelSpanClosure hK b).starProjection
          ((kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x))
          = (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x) :=
        Submodule.starProjection_mem_subspace_eq_self
          ⟨(kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x),
            Submodule.starProjection_apply_mem _ _⟩
      rw [map_sub, hidem, sub_self]
    have hφr : (fun e : Lp ℂ 2 ν => e
          - (kernelSpanClosure hK b).starProjection e)
        (sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x))
        = sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x) := by
      show (sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x))
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x
              - (kernelSpanClosure hK b).starProjection
                  (sectionLp (ν := ν) (fun p => star (K p)) x)) = _
      rw [hPr, sub_zero]
    have hmem : (fun e : Lp ℂ 2 ν => e
          - (kernelSpanClosure hK b).starProjection e)
        (sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x))
        ∈ (fun e : Lp ℂ 2 ν => e
            - (kernelSpanClosure hK b).starProjection e)
          '' closure c :=
      ⟨_, hWclos hrW, rfl⟩
    have h1 := image_closure_subset_closure_image hφcont hmem
    rw [← htdef] at h1
    rwa [hφr] at h1
  have hr0 : sectionLp (ν := ν) (fun p => star (K p)) x
      - (kernelSpanClosure hK b).starProjection
          (sectionLp (ν := ν) (fun p => star (K p)) x) = 0 := by
    obtain ⟨u, hu_mem, hu_lim⟩ :=
      mem_closure_iff_seq_limit.mp hrclos
    have hinner0 : ∀ n, ⟪sectionLp (ν := ν) (fun p => star (K p)) x
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x),
        u n⟫ = 0 :=
      fun n => hxvan ⟨u n, hu_mem n⟩
    have hlim : Tendsto
        (fun n => ⟪sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x),
          u n⟫) atTop
        (𝓝 ⟪sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x),
          sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x)⟫) :=
      tendsto_const_nhds.inner hu_lim
    have hzero_lim : Tendsto
        (fun n => ⟪sectionLp (ν := ν) (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x),
          u n⟫) atTop (𝓝 0) := by
      have hfun0 : (fun n => ⟪sectionLp (ν := ν)
            (fun p => star (K p)) x
          - (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x),
          u n⟫) = fun _ => (0 : ℂ) :=
        funext fun n => hinner0 n
      rw [hfun0]; exact tendsto_const_nhds
    have hself : ⟪sectionLp (ν := ν) (fun p => star (K p)) x
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x),
        sectionLp (ν := ν) (fun p => star (K p)) x
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x)⟫ = 0 :=
      tendsto_nhds_unique hlim hzero_lim
    exact inner_self_eq_zero.mp hself
  have hPeq : (kernelSpanClosure hK b).starProjection
      (sectionLp (ν := ν) (fun p => star (K p)) x)
      = sectionLp (ν := ν) (fun p => star (K p)) x :=
    (sub_eq_zero.mp hr0).symm
  -- coefficient facts at `x`
  have hnorm_i : ∀ i : ↥(kernelSupport hK b),
      ‖⟪(b i : Lp ℂ 2 ν),
        sectionLp (ν := ν) (fun p => star (K p)) x⟫‖
        = ‖integralKernelFun ν K ⇑(b i) x‖ := fun i => by
    rw [← hxinner i, ← inner_conj_symm, starRingEnd_apply, norm_star]
  have hcoef : ∀ i : ↥(kernelSupport hK b),
      ⟪(b i : Lp ℂ 2 ν),
        sectionLp (ν := ν) (fun p => star (K p)) x⟫
        = ⟪(b i : Lp ℂ 2 ν), (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x)⟫ := fun i => by
    have h0 : ⟪(b i : Lp ℂ 2 ν),
        sectionLp (ν := ν) (fun p => star (K p)) x
        - (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x)⟫ = 0 :=
      inner_eq_zero_symm.mp
        (Submodule.starProjection_inner_eq_zero _ _
          (basis_mem_kernelSpanClosure hK b i.2))
    rwa [inner_sub_right, sub_eq_zero] at h0
  have hsupp : Function.support (fun i => ENNReal.ofReal
        (‖⟪(b i : Lp ℂ 2 ν), (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x)⟫‖ ^ 2))
      ⊆ kernelSupport hK b := by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hiA
    apply hi
    have h0 : ⟪(b i : Lp ℂ 2 ν),
        (kernelSpanClosure hK b).starProjection
          (sectionLp (ν := ν) (fun p => star (K p)) x)⟫ = 0 :=
      inner_eq_zero_symm.mp
        ((basis_mem_kernelSpanClosure_orthogonal hK b hiA) _
          (Submodule.starProjection_apply_mem _ _))
    show ENNReal.ofReal
        (‖⟪(b i : Lp ℂ 2 ν), (kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x)⟫‖ ^ 2) = 0
    rw [h0]
    simp
  calc ∑' i : ↥(kernelSupport hK b),
        ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2
      = ∑' i : ↥(kernelSupport hK b), ENNReal.ofReal
          (‖⟪(b i : Lp ℂ 2 ν),
            sectionLp (ν := ν) (fun p => star (K p)) x⟫‖ ^ 2) := by
        apply tsum_congr
        intro i
        rw [← hpt, hnorm_i i]
    _ = ∑' i : ↥(kernelSupport hK b), ENNReal.ofReal
          (‖⟪(b i : Lp ℂ 2 ν), (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x)⟫‖ ^ 2) :=
        tsum_congr fun i => by rw [hcoef i]
    _ = ∑' i, ENNReal.ofReal
          (‖⟪(b i : Lp ℂ 2 ν), (kernelSpanClosure hK b).starProjection
              (sectionLp (ν := ν) (fun p => star (K p)) x)⟫‖ ^ 2) :=
        tsum_subtype_eq_of_support_subset hsupp
    _ = ENNReal.ofReal
          (‖(kernelSpanClosure hK b).starProjection
            (sectionLp (ν := ν) (fun p => star (K p)) x)‖ ^ 2) := by
        rw [← hsParseval_tsum b]
        exact (ENNReal.ofReal_tsum_of_nonneg
          (fun i => sq_nonneg _)
          (hsSummable_inner_sq b _)).symm
    _ = ENNReal.ofReal
          (‖sectionLp (ν := ν) (fun p => star (K p)) x‖ ^ 2) := by
        rw [hPeq]
    _ = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν := hxnorm hz

/-- **Headline Hilbert-Schmidt identity, `ℝ≥0∞` form**: the
`ℝ≥0∞` sum over a Hilbert basis of the squared `L2` norms of the
kernel operator's values equals the squared `L2` norm of the
kernel. Proved by integrating the pointwise Parseval identity
over the countable support (`hs_identity_subtype_ae`) and using
Tonelli. -/
theorem integralKernel_hs_identity_enn (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    ∑' i, hsSummandENN hK b i = (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
  haveI : Countable ↥(kernelSupport hK b) :=
    kernelSupport_countable hK b
  have hsupp : Function.support (hsSummandENN hK b)
      ⊆ kernelSupport hK b :=
    fun _ hi => hi
  calc ∑' i, hsSummandENN hK b i
      = ∑' i : ↥(kernelSupport hK b), hsSummandENN hK b i :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' i : ↥(kernelSupport hK b),
          ∫⁻ x, ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2 ∂μ :=
        tsum_congr fun (i : ↥(kernelSupport hK b)) =>
          hsSummandENN_eq_lintegral hK b (i : ι)
    _ = ∫⁻ x, ∑' i : ↥(kernelSupport hK b),
          ‖integralKernelFun ν K (⇑(b i)) x‖ₑ ^ 2 ∂μ :=
        (MeasureTheory.lintegral_tsum
          fun (i : ↥(kernelSupport hK b)) =>
            aemeasurable_hsSummand hK b (i : ι)).symm
    _ = ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
        apply lintegral_congr_ae
        exact hs_identity_subtype_ae hK b
    _ = (eLpNorm K 2 (μ.prod ν)) ^ 2 := by
        rw [← MeasureTheory.lintegral_prod _
          (aemeasurable_kernel_enorm_sq hK)]
        exact (eLpNorm_two_sq _ hK.aestronglyMeasurable).symm

/-- **Headline Hilbert-Schmidt identity (pack item 4)**: for every
Hilbert basis `b` of `Lp ℂ 2 ν`, the real sum of the squared norms
of the kernel operator's values on `b` equals the squared `L2`
norm of the kernel. -/
theorem integralKernel_tsum_norm_sq_eq (hK : MemLp K 2 (μ.prod ν))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    ∑' i, ‖integralKernelOp hK (b i)‖ ^ 2
      = (eLpNorm K 2 (μ.prod ν)).toReal ^ 2 := by
  have hne : ∀ i, hsSummandENN hK b i ≠ ∞ := by
    intro i
    show (eLpNorm (⇑(integralKernelOp hK (b i))) 2 μ) ^ 2 ≠ ∞
    exact ENNReal.pow_ne_top (MeasureTheory.Lp.memLp _).ne
  calc ∑' i, ‖integralKernelOp hK (b i)‖ ^ 2
      = ∑' i, (hsSummandENN hK b i).toReal :=
        tsum_congr fun i => (hsSummandENN_toReal hK b i).symm
    _ = (∑' i, hsSummandENN hK b i).toReal :=
        (ENNReal.tsum_toReal_eq hne).symm
    _ = ((eLpNorm K 2 (μ.prod ν)) ^ 2).toReal := by
        rw [integralKernel_hs_identity_enn hK b]
    _ = (eLpNorm K 2 (μ.prod ν)).toReal ^ 2 :=
        ENNReal.toReal_pow _ _

/-- The Hilbert-Schmidt norm squared of the kernel operator (in
the sense of `HilbertSchmidt.lean`) is the squared `L2` norm of
the kernel, for every Hilbert basis. -/
theorem integralKernel_hilbertSchmidtNormSq
    (hK : MemLp K 2 (μ.prod ν)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    hilbertSchmidtNormSq (integralKernelOp hK) b
      = (eLpNorm K 2 (μ.prod ν)).toReal ^ 2 :=
  integralKernel_tsum_norm_sq_eq hK b

end GeneralKernel

/-! ## Specialization check at the Q12 seat

The ONLY section of this module that mentions seat-specific
names. It instantiates the general API at Q12's seat
(`LatticeTransferCompact`): the slice space with its slice
measure, and proves that Q12's `kernelOp` agrees there with the
general `integralKernelOp`. -/

section SeatSpecialization

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **Specialization check**: at the Q12 seat, Q12's `kernelOp`
is the general integral kernel operator `integralKernelOp` for
the same kernel. (The probability instance on the slice measure
is the seat's own `isProbabilityMeasure_sliceMeasure`.) -/
theorem kernelOp_eq_integralKernelOp (β : ℝ)
    [IsProbabilityMeasure (sliceMeasure (N := N) μG ρ β)]
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β))) :
    kernelOp μG ρ β hρcont hd K hK = integralKernelOp hK := by
  ext f
  rw [kernelOp_apply]
  exact Filter.EventuallyEq.trans
    (coeFn_kernelLinMap μG ρ β hρcont hd K hK f)
    (Filter.EventuallyEq.trans
      (Filter.Eventually.of_forall fun _ => rfl :
        kernelFun μG ρ β K ⇑f
          =ᵐ[sliceMeasure (N := N) μG ρ β]
            integralKernelFun (sliceMeasure (N := N) μG ρ β) K ⇑f)
      (coeFn_integralKernelOp hK f).symm)

/-- **Seat Hilbert-Schmidt identity**: the headline identity of
`integralKernel_tsum_norm_sq_eq`, at the Q12 seat, for Q12's
`kernelOp`. -/
theorem kernelOp_tsum_norm_sq_eq (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β)))
    {ι : Type*} (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ β)) :
    ∑' i, ‖kernelOp μG ρ β hρcont hd K hK (b i)‖ ^ 2
      = (eLpNorm K 2 ((sliceMeasure (N := N) μG ρ β).prod
          (sliceMeasure (N := N) μG ρ β))).toReal ^ 2 := by
  haveI : IsProbabilityMeasure (sliceMeasure (N := N) μG ρ β) :=
    isProbabilityMeasure_sliceMeasure μG ρ hρcont hd β
  have heq : kernelOp μG ρ β hρcont hd K hK
      = integralKernelOp hK :=
    kernelOp_eq_integralKernelOp μG ρ β hρcont hd K hK
  rw [heq]
  exact integralKernel_tsum_norm_sq_eq hK b

/-- **Seat compactness through the general operator**: Q12's
`kernelOp` is compact because it is the general kernel operator
(compactness is pack item 5, `integralKernelOp_isCompactOperator`). -/
theorem kernelOp_isCompactOperator_seat (β : ℝ)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (K : (↥(sliceLinks (N := N)) → G) × (↥(sliceLinks (N := N)) → G)
      → ℂ)
    (hK : MemLp K 2 ((sliceMeasure (N := N) μG ρ β).prod
      (sliceMeasure (N := N) μG ρ β))) :
    IsCompactOperator ⇑(kernelOp μG ρ β hρcont hd K hK) := by
  haveI : IsProbabilityMeasure (sliceMeasure (N := N) μG ρ β) :=
    isProbabilityMeasure_sliceMeasure μG ρ hρcont hd β
  have heq : kernelOp μG ρ β hρcont hd K hK
      = integralKernelOp hK :=
    kernelOp_eq_integralKernelOp μG ρ β hρcont hd K hK
  rw [heq]
  exact integralKernelOp_isCompactOperator hK

end SeatSpecialization

end ThetLogos
