/-
# FG-2c-0 — the continuous functional calculus for `T̂_c`, and the
# discharge of FG-2b's step 0

Brick FG-2c-0 of the FG-2c gate paper
(`whitepaper/stage2-fg2c-gate-2026-10-25.md`, §3, §4, §7): wire
Mathlib's continuous functional calculus to the completed transfer
operator `sliceHatCompleted`, build the order-to-pairing bridge,
and discharge the step-0 obstruction left by FG-2a/FG-2b — the
mixed pairings `⟪x, T̂_c A_c^j x⟫.re ≥ 0`, i.e. form-order
`T̂_c² ≤ T̂_c`.

PLACEMENT LABEL (consumed from the gate, not re-decided here):
this is a **Stage 2 completeness** item — it finishes the
representation-theoretic content of the S2-4(b) operator seat. It
is NOT frontier progress: Items 3 (uniform estimates) and 4
(continuum) are untouched, and nothing here moves any dial.
Dials 0/4. NO CLAIM.

## What this brick consumes

* `sliceOperator_package` (LatticeSliceOperator): `T̂_c` is a
  self-adjoint contraction on `sliceHilbertSpace`, factored-form
  positive, vacuum fixed.
* `sliceFormDomain_orthogonal_ker` (LatticeSliceFormClosed, FG-2a):
  the form domain lies inside `(ker T̂_c)⊥`.
* `sliceFormClosure` (LatticeSliceFriedrichs, FG-2b): the carrier
  `H'` is the closure of the form domain; `H' ⊆ (ker T̂_c)⊥`.

## What it delivers

* §0 (generic, for any Hilbert space): the Loewner order on
  continuous linear maps is a star order. The pinned Mathlib
  carries no `StarOrderedRing (E →L[ℂ] E)` instance (the
  `IsPositive` file even carries a TODO awaiting it); the instance
  is built here from a CFC square root of a positive operator.
  With it, the whole CFC order API (`cfc_nonneg`, `cfc_mono`,
  `NonnegSpectrumClass`) fires for `T̂_c`.
* §1: `T̂_c` is self-adjoint and positive as a C*-algebra element;
  `spectrum ℝ T̂_c ⊆ [0, 1]`; polynomial agreement of `cfc` at
  `T̂_c` (defect powers, truncations `p_n(μ) = 1 - (1-μ)^n`).
* §2: the order-to-pairing bridge — for continuous `f ≥ 0` on
  `[0, 1]`, `⟪x, cfc f T̂_c x⟫.re ≥ 0`. Headline: form-order
  `T̂_c² ≤ T̂_c`, and the mixed pairings of step 0, in the corpus's
  own function language.
* §3: step 0 discharged — the truncations `p_n(T̂_c)` land in the
  form domain with `form(p_n(T̂_c) x) ≤ form(x)`, `A_c^n x → 0` for
  `x ⊥ ker T̂_c`, hence the form domain is dense in `(ker T̂_c)⊥`
  and `sliceFormClosure = (ker T̂_c)ᗮ`.

Fences: no `osForm` positivity beyond landed labels; FG-2c's
identification `exp(−Ĥ) = T̂_c` is NOT asserted here (this brick
is its step-0 input, per the gate's factorization); TM R2
untouched; Stage 1b-B untouched.
NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceFriedrichs
import ThetLogos.LatticeSliceCircle
import ThetLogos.LatticeSliceRegression
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace ThetLogos

open MeasureTheory Finset Filter Topology
open scoped Matrix ENNReal NNReal InnerProduct ComplexOrder

/-! ## §0. The Loewner order on CLMs is a star order

Generic facts about continuous linear maps on a complex Hilbert
space, proved once here because the step-0 discharge consumes the
CFC order API, which is gated on a `StarOrderedRing` instance the
pinned Mathlib does not carry for `E →L[ℂ] E`. -/

section CLMStarOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- **The spectrum of a positive CLM is nonnegative.** If
`μ < 0`, then `algebraMap μ - S` has pairings bounded below by
`|μ| ‖x‖²` in norm, hence is a unit — so `μ` is not in the
spectrum. -/
theorem clmIsPositive_spectrum_nonneg {S : E →L[ℂ] E}
    (hS : S.IsPositive) {μ : ℝ} (hμ : μ ∈ spectrum ℝ S) :
    0 ≤ μ := by
  by_contra hlt
  push_neg at hlt
  have hμ' : ¬ IsUnit (algebraMap ℝ (E →L[ℂ] E) μ - S) := hμ
  apply hμ'
  -- `algebraMap μ - S` is a unit: its pairings are large.
  have hunit : IsUnit (S - algebraMap ℝ (E →L[ℂ] E) μ) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      (S - algebraMap ℝ (E →L[ℂ] E) μ)
      (c := ⟨|μ|, abs_nonneg μ⟩)
    · exact_mod_cast abs_pos.mpr (ne_of_lt hlt)
    · intro x
      have hSx : inner ℂ (S x) x = ((inner ℂ (S x) x).re : ℂ) := by
        have him : (inner ℂ (S x) x).im = 0 :=
          (Complex.le_def.mp (hS.inner_nonneg_left x)).2.symm
        rw [← Complex.re_add_im (inner ℂ (S x) x)]
        simp [him]
      have h1 : (algebraMap ℝ (E →L[ℂ] E) μ) x = (μ : ℂ) • x := by
        rw [Algebra.algebraMap_eq_smul_one]
        simp [ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, Complex.real_smul]
      have hfx : inner ℂ ((S - algebraMap ℝ (E →L[ℂ] E) μ) x) x
          = (((inner ℂ (S x) x).re - μ * ‖x‖ ^ 2 : ℝ) : ℂ) := by
        rw [ContinuousLinearMap.sub_apply, inner_sub_left, hSx, h1,
          inner_smul_left, inner_self_eq_norm_sq_to_K]
        simp [Complex.conj_ofReal]
      rw [hfx]
      have hcast : ‖(((inner ℂ (S x) x).re - μ * ‖x‖ ^ 2 : ℝ) : ℂ)‖
          = |(inner ℂ (S x) x).re - μ * ‖x‖ ^ 2| :=
        RCLike.norm_ofReal _
      have hnorm : ‖(((inner ℂ (S x) x).re - μ * ‖x‖ ^ 2 : ℝ) : ℂ)‖
          = (inner ℂ (S x) x).re + |μ| * ‖x‖ ^ 2 := by
        have hprod : μ * ‖x‖ ^ 2 = -(|μ| * ‖x‖ ^ 2) := by
          rw [abs_of_neg hlt]
          ring
        have hre : 0 ≤ (inner ℂ (S x) x).re :=
          hS.re_inner_nonneg_left x
        have hμ2 : μ * ‖x‖ ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hlt.le (sq_nonneg ‖x‖)
        have hside : (0 : ℝ) ≤ (inner ℂ (S x) x).re
            - μ * ‖x‖ ^ 2 := by linarith
        rw [hcast, abs_of_nonneg hside]
        linarith
      rw [hnorm]
      have hre : 0 ≤ (inner ℂ (S x) x).re :=
        hS.re_inner_nonneg_left x
      change ‖x‖ ^ 2 * |μ| ≤ (inner ℂ (S x) x).re
        + |μ| * ‖x‖ ^ 2
      nlinarith [sq_nonneg ‖x‖, hre]
  have hneg := hunit.neg
  rwa [neg_sub] at hneg

/-- **A positive CLM is a star square.** The square root is
`cfc Real.sqrt S`, legitimate because the spectrum of `S` is
nonnegative (`clmIsPositive_spectrum_nonneg`). -/
theorem clmIsPositive_exists_star_mul_self {S : E →L[ℂ] E}
    (hS : S.IsPositive) : ∃ B : E →L[ℂ] E, S = star B * B := by
  have hsa : IsSelfAdjoint S := hS.isSelfAdjoint
  have hspec : ∀ μ ∈ spectrum ℝ S, 0 ≤ μ :=
    fun μ hμ => clmIsPositive_spectrum_nonneg hS hμ
  refine ⟨cfc (fun μ : ℝ => Real.sqrt μ) S, ?_⟩
  have hBsa : IsSelfAdjoint (cfc (fun μ : ℝ => Real.sqrt μ) S) := by
    have h : star (cfc (fun μ : ℝ => Real.sqrt μ) S)
        = cfc (fun μ : ℝ => Real.sqrt μ) S := by
      rw [← cfc_star,
        show (fun x : ℝ => star (Real.sqrt x))
          = (fun μ : ℝ => Real.sqrt μ) from
          funext fun x => by simp]
    exact h
  rw [hBsa.star_eq,
    ← cfc_mul _ _ _
      (hf := Real.continuous_sqrt.continuousOn)
      (hg := Real.continuous_sqrt.continuousOn)]
  have h2 : cfc (fun μ : ℝ => Real.sqrt μ * Real.sqrt μ) S = S := by
    conv_rhs => rw [← cfc_id' ℝ S]
    exact cfc_congr (fun μ hμ => Real.mul_self_sqrt (hspec μ hμ))
  simpa only [Pi.mul_apply] using h2.symm

/-- **The Loewner order on `E →L[ℂ] E` is a star order.**
This instance is missing from the pinned Mathlib (the
`IsPositive` API carries a TODO awaiting exactly it); it is what
unlocks `cfc_nonneg` / `cfc_mono` / `NonnegSpectrumClass` for
continuous linear maps. -/
instance : StarOrderedRing (E →L[ℂ] E) :=
  StarOrderedRing.of_nonneg_iff'
    (fun h z => add_le_add (le_refl z) h)
    fun S => by
      constructor
      · intro hS
        exact clmIsPositive_exists_star_mul_self
          (ContinuousLinearMap.nonneg_iff_isPositive.mp hS)
      · rintro ⟨s, rfl⟩
        rw [ContinuousLinearMap.nonneg_iff_isPositive]
        have h1 : star s * s = s† ∘L s := by
          rw [ContinuousLinearMap.star_eq_adjoint]
          ext x
          simp [ContinuousLinearMap.mul_apply',
            ContinuousLinearMap.comp_apply]
        rw [h1]
        exact ContinuousLinearMap.isPositive_adjoint_comp_self s

end CLMStarOrder

/-! ## §1. `cfc` assembled for the completed transfer operator -/

section SliceCfc

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **Shorthand for the completed transfer operator** `T̂_c`, as a
continuous linear map on the completed Hilbert space. -/
noncomputable abbrev sliceTc (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  sliceHatCompleted μG ρ hN2 hρcont hN β hpos

/-- **Shorthand for the completed defect** `A_c = 1 - T̂_c`, as a
continuous linear map. -/
noncomputable abbrev sliceAc (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  sliceDefectCLM μG ρ hN2 hρcont hN β hpos

theorem sliceAc_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceAc μG ρ hN2 hρcont hN β hpos
      = 1 - sliceTc μG ρ hN2 hρcont hN β hpos :=
  rfl

/-- `T̂_c` acts as the completed extension function. -/
theorem sliceTc_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceTc μG ρ hN2 hρcont hN β hpos x
      = sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos x :=
  sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos x

/-- **`T̂_c` is self-adjoint** (as a C*-algebra element): FG-2a/b's
landed symmetry, repackaged. -/
theorem sliceTc_isSelfAdjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    IsSelfAdjoint (sliceTc μG ρ hN2 hρcont hN β hpos) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show inner ℂ (sliceTc μG ρ hN2 hρcont hN β hpos x) y
    = inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos y)
  rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos x,
    sliceTc_apply μG ρ hN2 hρcont hN β hpos y]
  exact sliceHatCompletedFun_symmetric μG ρ hN2 hρcont hN β hpos
    x y

/-- The right pairing of `T̂_c` is real and nonnegative
(factored-form positivity, landed in S2-4(b), in `inner ℂ`
language). -/
theorem sliceTc_inner_right_eq_ofReal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos x)
      = ((inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos
          x)).re : ℂ) := by
  rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos x]
  have him : (inner ℂ x
        (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
          x)).im = 0 := by
    have h := sliceHatCompletedFun_iter_diag_im μG ρ hN2
      hρcont hN β hpos 1 x
    simpa using h
  rw [← Complex.re_add_im (inner ℂ x
    (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos x))]
  simp [him]

/-- The left pairing of `T̂_c` equals the right pairing (landed
symmetry at the diagonal), hence is the same nonnegative real. -/
theorem sliceTc_inner_left_eq_ofReal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceTc μG ρ hN2 hρcont hN β hpos x) x
      = ((inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos
          x)).re : ℂ) := by
  have hsymm : inner ℂ (sliceTc μG ρ hN2 hρcont hN β hpos x) x
      = inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos x) := by
    rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos x]
    exact sliceHatCompletedFun_symmetric μG ρ hN2 hρcont hN β
      hpos x x
  rw [hsymm]
  exact sliceTc_inner_right_eq_ofReal μG ρ hN2 hρcont hN β hpos x

/-- **`T̂_c` is a positive operator** in the Loewner sense. -/
theorem sliceTc_isPositive (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (sliceTc μG ρ hN2 hρcont hN β hpos).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos,
    fun x => ?_⟩
  have hnn : 0 ≤ (inner ℂ x
      (sliceTc μG ρ hN2 hρcont hN β hpos x)).re := by
    rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos x]
    exact sliceHatCompletedFun_inner_nonneg μG ρ hN2 hρcont hN
      β hpos x
  rw [sliceTc_inner_left_eq_ofReal μG ρ hN2 hρcont hN β hpos x]
  exact_mod_cast hnn

/-- `0 ≤ T̂_c` in the Loewner (star) order. -/
theorem sliceTc_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    0 ≤ sliceTc μG ρ hN2 hρcont hN β hpos :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (sliceTc_isPositive μG ρ hN2 hρcont hN β hpos)

/-- **`T̂_c ≤ 1`** in the Loewner order: the defect `1 - T̂_c` is
positive, by Cauchy–Schwarz and the contraction bound. -/
theorem sliceTc_le_one (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceTc μG ρ hN2 hρcont hN β hpos ≤ 1 := by
  rw [ContinuousLinearMap.le_def,
    ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, fun x => ?_⟩
  · have hsa := sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos
    show star (1 - sliceTc μG ρ hN2 hρcont hN β hpos)
      = 1 - sliceTc μG ρ hN2 hρcont hN β hpos
    rw [star_sub, star_one, hsa.star_eq]
  · have hnn : 0 ≤ (inner ℂ x
        (sliceTc μG ρ hN2 hρcont hN β hpos x)).re := by
      rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos x]
      exact sliceHatCompletedFun_inner_nonneg μG ρ hN2 hρcont hN
        β hpos x
    have hle : (inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos
        x)).re ≤ ‖x‖ ^ 2 := by
      have h1 : ‖inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos
          x)‖ ≤ ‖x‖ * ‖sliceTc μG ρ hN2 hρcont hN β hpos x‖ :=
        norm_inner_le_norm x _
      have h2 : ‖sliceTc μG ρ hN2 hρcont hN β hpos x‖ ≤ ‖x‖ := by
        rw [sliceTc_apply μG ρ hN2 hρcont hN β hpos x]
        exact sliceHatCompletedFun_norm_le μG ρ hN2 hρcont hN β
          hpos x
      have h3 : ‖inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos
          x)‖ = (inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos
          x)).re := by
        rw [sliceTc_inner_right_eq_ofReal μG ρ hN2 hρcont hN β
          hpos x]
        exact (RCLike.norm_ofReal _).trans (abs_of_nonneg hnn)
      rw [h3] at h1
      refine h1.trans ?_
      calc ‖x‖ * ‖sliceTc μG ρ hN2 hρcont hN β hpos x‖
          ≤ ‖x‖ * ‖x‖ :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
        _ = ‖x‖ ^ 2 := by ring
    have hre : (inner ℂ ((1 - sliceTc μG ρ hN2 hρcont hN β
          hpos) x) x).re
        = ‖x‖ ^ 2 - (inner ℂ x (sliceTc μG ρ hN2 hρcont hN β
            hpos x)).re := by
      rw [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, inner_sub_left,
        Complex.sub_re,
        sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos x]
      congr 1
      rw [sliceTc_inner_left_eq_ofReal μG ρ hN2 hρcont hN β
        hpos x]
      exact Complex.ofReal_re _
    have him : (inner ℂ ((1 - sliceTc μG ρ hN2 hρcont hN β
          hpos) x) x).im = 0 := by
      rw [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, inner_sub_left,
        Complex.sub_im,
        sliceCompleted_inner_self_im μG ρ hN2 hρcont hN β hpos x]
      have h2 : (inner ℂ (sliceTc μG ρ hN2 hρcont hN β hpos x)
          x).im = 0 := by
        rw [sliceTc_inner_left_eq_ofReal μG ρ hN2 hρcont hN β
          hpos x]
        exact Complex.ofReal_im _
      rw [h2, sub_zero]
    refine Complex.le_def.mpr ⟨?_, ?_⟩
    · rw [Complex.zero_re, hre]
      exact sub_nonneg.mpr hle
    · rw [Complex.zero_im, him]

/-- **The spectrum of `T̂_c` lies in `[0, 1]`.** Lower bound from
positivity via the CFC spectrum characterization; upper bound
from `T̂_c ≤ 1` by shifting the spectrum of the defect. -/
theorem sliceTc_spectrum_subset (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    spectrum ℝ (sliceTc μG ρ hN2 hρcont hN β hpos)
      ⊆ Set.Icc 0 1 := by
  have hsa := sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos
  have hnn := sliceTc_nonneg μG ρ hN2 hρcont hN β hpos
  have hle1 := sliceTc_le_one μG ρ hN2 hρcont hN β hpos
  have hdef : 0 ≤ 1 - sliceTc μG ρ hN2 hρcont hN β hpos :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.le_def.mp hle1)
  intro μ hμ
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · exact (StarOrderedRing.nonneg_iff_spectrum_nonneg
      (sliceTc μG ρ hN2 hρcont hN β hpos)).mp hnn μ hμ
  · -- Upper bound: `μ` is a complex spectral value too, so
    -- `|μ|` is below the spectral radius, which for the
    -- self-adjoint contraction `T̂_c` equals its norm `≤ 1`.
    have hμℂ : (μ : ℂ) ∈ spectrum ℂ
        (sliceTc μG ρ hN2 hρcont hN β hpos) :=
      (IsSelfAdjoint.coe_mem_spectrum_complex hsa).mpr hμ
    have hquasi : (μ : ℂ) ∈ quasispectrum ℂ
        (sliceTc μG ρ hN2 hρcont hN β hpos) :=
      spectrum_subset_quasispectrum ℂ _ hμℂ
    have hrad : (‖(μ : ℂ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ
        (sliceTc μG ρ hN2 hρcont hN β hpos) := by
      show (‖(μ : ℂ)‖₊ : ℝ≥0∞)
        ≤ ⨆ k ∈ quasispectrum ℂ (sliceTc μG ρ hN2 hρcont hN β
            hpos), (‖k‖₊ : ℝ≥0∞)
      exact le_biSup (fun k : ℂ => (‖k‖₊ : ℝ≥0∞)) hquasi
    rw [ContinuousLinearMap.spectralRadius_eq_nnnorm _ hsa]
      at hrad
    have hnnreal : ‖(μ : ℂ)‖₊
        ≤ ‖sliceTc μG ρ hN2 hρcont hN β hpos‖₊ :=
      ENNReal.coe_le_coe.mp hrad
    have hnorm : |μ| ≤ ‖sliceTc μG ρ hN2 hρcont hN β hpos‖ := by
      have h := NNReal.coe_le_coe.mpr hnnreal
      rw [coe_nnnorm, coe_nnnorm] at h
      simpa using h
    refine (le_abs_self μ).trans (hnorm.trans ?_)
    rw [sliceTc]
    exact sliceHatCompleted_norm_le_one μG ρ hN2 hρcont hN β
      hpos


/-! ## §1b. Instance cache for the completed space.

Instance synthesis through the definition of `sliceHilbertSpace`
(a completion of a quotient) is prohibitively slow when repeated
per declaration; the instances below are the canonical ones,
declared once. -/

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceNormedAddCommGroup (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    NormedAddCommGroup (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceInnerProductSpace (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    InnerProductSpace ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceCompleteSpace (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    CompleteSpace (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceModuleComplex (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Module ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceModuleReal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Module ℝ (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceNormedSpaceComplex (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    NormedSpace ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceAlgebraReal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Algebra ℝ (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
      →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceAddCommGroup (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    AddCommGroup (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceSpaceAddGroup (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    AddGroup (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceAlgebraComplex (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Algebra ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
      →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
  inferInstance

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance sliceCfcComplexNormal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    ContinuousFunctionalCalculus ℂ
      (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
        →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
      IsStarNormal :=
  inferInstance

/-! ## §2. Polynomial agreement: `cfc` of a polynomial is its
algebraic evaluation at `T̂_c`. -/

/-- `cfc` of the identity function is `T̂_c` itself. -/
theorem sliceCfc_id (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    cfc (fun μ : ℝ => μ) (sliceTc μG ρ hN2 hρcont hN β hpos)
      = sliceTc μG ρ hN2 hρcont hN β hpos :=
  cfc_id' ℝ _ (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos)

/-- `cfc` of a monomial is the algebraic power. -/
theorem sliceCfc_pow (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    cfc (fun μ : ℝ => μ ^ n) (sliceTc μG ρ hN2 hρcont hN β hpos)
      = (sliceTc μG ρ hN2 hρcont hN β hpos) ^ n :=
  cfc_pow_id _ n (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos)

/-- `cfc` of a constant function is the algebra map. -/
theorem sliceCfc_const (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℝ) :
    cfc (fun _ : ℝ => c) (sliceTc μG ρ hN2 hρcont hN β hpos)
      = algebraMap ℝ
          (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
            sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c :=
  cfc_const c _ (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos)

/-- `cfc` of `1 − μ` is the completed defect `Â_c`. -/
theorem sliceCfc_one_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    cfc (fun μ : ℝ => 1 - μ) (sliceTc μG ρ hN2 hρcont hN β hpos)
      = sliceAc μG ρ hN2 hρcont hN β hpos := by
  calc cfc (fun μ : ℝ => 1 - μ)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = cfc (fun _ : ℝ => (1 : ℝ))
            (sliceTc μG ρ hN2 hρcont hN β hpos)
          - cfc (fun μ : ℝ => μ)
            (sliceTc μG ρ hN2 hρcont hN β hpos) :=
        cfc_sub _ _ _ continuousOn_const
          continuous_id.continuousOn
    _ = 1 - sliceTc μG ρ hN2 hρcont hN β hpos := by
        rw [cfc_const (1 : ℝ) _
          (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos),
          cfc_id' ℝ _
            (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos),
          map_one]
    _ = sliceAc μG ρ hN2 hρcont hN β hpos := (sliceAc_eq μG ρ hN2 hρcont hN β hpos).symm

/-- `cfc` of `(1 − μ)^j` is the `j`-th power of the defect. -/
theorem sliceCfc_defect_pow (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ) :
    cfc (fun μ : ℝ => (1 - μ) ^ j)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = (sliceAc μG ρ hN2 hρcont hN β hpos) ^ j := by
  calc cfc (fun μ : ℝ => (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = (cfc (fun μ : ℝ => 1 - μ)
            (sliceTc μG ρ hN2 hρcont hN β hpos)) ^ j :=
        cfc_pow _ j _
          ((continuous_const.sub continuous_id).continuousOn)
          (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos)
    _ = (sliceAc μG ρ hN2 hρcont hN β hpos) ^ j := by
        rw [sliceCfc_one_sub]

/-- `cfc` of `μ(1 − μ)^j` is `T̂_c Â_c^j`. -/
theorem sliceCfc_mul_defect_pow (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ) :
    cfc (fun μ : ℝ => μ * (1 - μ) ^ j)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = sliceTc μG ρ hN2 hρcont hN β hpos
        * (sliceAc μG ρ hN2 hρcont hN β hpos) ^ j := by
  calc cfc (fun μ : ℝ => μ * (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = cfc (fun μ : ℝ => μ) (sliceTc μG ρ hN2 hρcont hN β hpos)
          * cfc (fun μ : ℝ => (1 - μ) ^ j)
            (sliceTc μG ρ hN2 hρcont hN β hpos) :=
        cfc_mul _ _ _ continuous_id.continuousOn
          ((by fun_prop : Continuous
            fun μ : ℝ => (1 - μ) ^ j).continuousOn)
    _ = sliceTc μG ρ hN2 hρcont hN β hpos
          * (sliceAc μG ρ hN2 hρcont hN β hpos) ^ j := by
        rw [cfc_id' ℝ _
          (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos),
          sliceCfc_defect_pow]

/-- `cfc` of the truncation polynomial `p_n(μ) = 1 − (1 − μ)^n`
is `1 − Â_c^n`. -/
theorem sliceCfc_truncation (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    cfc (fun μ : ℝ => 1 - (1 - μ) ^ n)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = 1 - (sliceAc μG ρ hN2 hρcont hN β hpos) ^ n := by
  calc cfc (fun μ : ℝ => 1 - (1 - μ) ^ n)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = cfc (fun _ : ℝ => (1 : ℝ))
            (sliceTc μG ρ hN2 hρcont hN β hpos)
          - cfc (fun μ : ℝ => (1 - μ) ^ n)
            (sliceTc μG ρ hN2 hρcont hN β hpos) :=
        cfc_sub _ _ _ continuousOn_const
          ((by fun_prop : Continuous
            fun μ : ℝ => (1 - μ) ^ n).continuousOn)
    _ = 1 - (sliceAc μG ρ hN2 hρcont hN β hpos) ^ n := by
        rw [cfc_const (1 : ℝ) _
          (sliceTc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos),
          map_one, sliceCfc_defect_pow]

/-- `cfc` values of real functions at the self-adjoint `T̂_c` are
self-adjoint. -/
theorem sliceCfc_isSelfAdjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (f : ℝ → ℝ) :
    IsSelfAdjoint (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)) := by
  have hfun : (fun x : ℝ => star (f x)) = f := by
    funext μ
    exact star_trivial _
  rw [IsSelfAdjoint, ← cfc_star, hfun]

/-! ## §3. Brick 2 — the order-to-pairing bridge and form-order. -/

/-- **The bridge.** For a real function nonnegative on `[0, 1]`
(in particular on the spectrum of `T̂_c`), the `cfc` value has
nonnegative pairings. -/
theorem sliceCfc_pairing_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (f : ℝ → ℝ)
    (hf : ∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f μ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (inner ℂ x (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)
      x)).re :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (cfc_nonneg fun μ hμ => hf μ
      (sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
        hμ))).re_inner_nonneg_right x

/-- Pairings are monotone in the function, for continuous
functions. -/
theorem sliceCfc_pairing_mono (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ μ ∈ Set.Icc (0 : ℝ) 1, f μ ≤ g μ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x (cfc f (sliceTc μG ρ hN2 hρcont hN β hpos)
      x)).re
      ≤ (inner ℂ x (cfc g (sliceTc μG ρ hN2 hρcont hN β hpos)
        x)).re := by
  have h : 0 ≤ (inner ℂ x
      (cfc (fun μ => g μ - f μ) (sliceTc μG ρ hN2 hρcont hN β
        hpos) x)).re :=
    sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN β hpos _
      (fun μ hμ => sub_nonneg.mpr (hfg μ hμ)) x
  rw [cfc_sub _ _ _ hg.continuousOn hf.continuousOn,
    ContinuousLinearMap.sub_apply, inner_sub_right,
    Complex.sub_re] at h
  linarith

/-- The pairing of a constant function is the constant times the
squared norm. -/
theorem sliceCfc_pairing_const (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℝ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x (cfc (fun _ : ℝ => c)
      (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re
      = c * ‖x‖ ^ 2 := by
  have hmap : (algebraMap ℝ
      (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
        sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c) x
      = (c : ℂ) • x := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  rw [sliceCfc_const μG ρ hN2 hρcont hN β hpos c, hmap,
    inner_smul_right,
    Eq.trans (inner_self_eq_norm_sq_to_K x)
      (RCLike.ofReal_pow ‖x‖ 2).symm]
  show RCLike.re (RCLike.ofReal (K := ℂ) c
    * RCLike.ofReal (K := ℂ) (‖x‖ ^ 2)) = c * ‖x‖ ^ 2
  rw [RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- The value identity behind both form-order statements. -/
theorem sliceCfc_sub_sq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    cfc (fun μ : ℝ => μ - μ ^ 2)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = sliceTc μG ρ hN2 hρcont hN β hpos
        - (sliceTc μG ρ hN2 hρcont hN β hpos) ^ 2 := by
  calc cfc (fun μ : ℝ => μ - μ ^ 2)
          (sliceTc μG ρ hN2 hρcont hN β hpos)
      = cfc (fun μ : ℝ => μ) (sliceTc μG ρ hN2 hρcont hN β hpos)
          - cfc (fun μ : ℝ => μ ^ 2)
              (sliceTc μG ρ hN2 hρcont hN β hpos) :=
        cfc_sub _ _ _ continuous_id.continuousOn
          ((continuous_id.pow 2).continuousOn)
    _ = sliceTc μG ρ hN2 hρcont hN β hpos
          - (sliceTc μG ρ hN2 hρcont hN β hpos) ^ 2 := by
        rw [sliceCfc_id, sliceCfc_pow]

/-- **Headline of Brick 2: form-order `T̂_c² ≤ T̂_c`** (operator
form). -/
theorem sliceTc_sq_le_self (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (sliceTc μG ρ hN2 hρcont hN β hpos) ^ 2
      ≤ sliceTc μG ρ hN2 hρcont hN β hpos := by
  have hnn : (0 : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
        →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
      ≤ cfc (fun μ : ℝ => μ - μ ^ 2)
          (sliceTc μG ρ hN2 hρcont hN β hpos) := by
    refine cfc_nonneg fun μ hμ => ?_
    have hμ' := sliceTc_spectrum_subset μG ρ hN2 hρcont hN β hpos
      hμ
    simp only [Set.mem_Icc] at hμ'
    nlinarith [hμ'.1, hμ'.2,
      mul_nonneg hμ'.1 (sub_nonneg.mpr hμ'.2)]
  rw [sliceCfc_sub_sq μG ρ hN2 hρcont hN β hpos] at hnn
  exact sub_nonneg.mp hnn

/-- **Form-order, pairing form:**
`⟪x, T̂_c² x⟫.re ≤ ⟪x, T̂_c x⟫.re`. -/
theorem sliceTc_sq_pairing_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x (((sliceTc μG ρ hN2 hρcont hN β hpos) ^ 2) x)).re
      ≤ (inner ℂ x (sliceTc μG ρ hN2 hρcont hN β hpos x)).re := by
  have h := sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN β hpos
    (fun μ : ℝ => μ - μ ^ 2)
    (fun μ hμ => by
      simp only [Set.mem_Icc] at hμ
      nlinarith [hμ.1, hμ.2,
        mul_nonneg hμ.1 (sub_nonneg.mpr hμ.2)]) x
  rw [sliceCfc_sub_sq μG ρ hN2 hρcont hN β hpos,
    ContinuousLinearMap.sub_apply, inner_sub_right,
    Complex.sub_re] at h
  linarith

/-- **The mixed pairings of step 0:** `⟪x, T̂_c Â_c^j x⟫.re ≥ 0`
for every `j`. -/
theorem sliceTc_mixed_pairing_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (inner ℂ x ((sliceTc μG ρ hN2 hρcont hN β hpos)
      (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j) x))).re := by
  have h := sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN β hpos
    (fun μ : ℝ => μ * (1 - μ) ^ j)
    (fun μ hμ => by
      simp only [Set.mem_Icc] at hμ
      exact mul_nonneg hμ.1 (pow_nonneg (sub_nonneg.mpr hμ.2) j)) x
  rw [sliceCfc_mul_defect_pow] at h
  exact h

/-- The pure defect pairings: `⟪x, Â_c^j x⟫.re ≥ 0`. -/
theorem sliceAc_pow_pairing_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
      x)).re := by
  have h := sliceCfc_pairing_nonneg μG ρ hN2 hρcont hN β hpos
    (fun μ : ℝ => (1 - μ) ^ j)
    (fun μ hμ => by
      simp only [Set.mem_Icc] at hμ
      exact pow_nonneg (sub_nonneg.mpr hμ.2) j) x
  rwa [sliceCfc_defect_pow] at h

/-! ## §4. Brick 3 — step-0 discharge: density of the form domain
in `(ker T̂_c)⊥` and the carrier equality
`sliceFormClosure = (ker T̂_c)⊥`. -/

/-- The defect `Â_c` is self-adjoint. -/
theorem sliceAc_isSelfAdjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    IsSelfAdjoint (sliceAc μG ρ hN2 hρcont hN β hpos) := by
  rw [← sliceCfc_one_sub μG ρ hN2 hρcont hN β hpos]
  exact sliceCfc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos _

set_option maxHeartbeats 3200000 in
/-- Self-adjoint operators move across the inner product. -/
theorem sliceSelfAdjoint_inner_move (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    {S : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos}
    (hS : IsSelfAdjoint S)
    (u v : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (S u) v = inner ℂ u (S v) := by
  have hS' : ContinuousLinearMap.adjoint S = S := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hS
  calc inner ℂ (S u) v
      = inner ℂ (ContinuousLinearMap.adjoint S u) v := by
        rw [hS']
    _ = inner ℂ u (S v) :=
        ContinuousLinearMap.adjoint_inner_left S v u

/-- The defect applied: `Â_c z = z − T̂_c z`. -/
theorem sliceAc_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (sliceAc μG ρ hN2 hρcont hN β hpos) z
      = z - (sliceTc μG ρ hN2 hρcont hN β hpos) z := by
  rw [sliceAc_eq, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

/-- Powers of the defect are its function iterates, hence the
completed-defect iterates of the form approximants. -/
theorem sliceAc_pow_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j) z
      = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] z := by
  have hiter : ∀ (j : ℕ)
      (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos),
      ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j) z
        = (⇑(sliceAc μG ρ hN2 hρcont hN β hpos))^[j] z := by
    intro j
    induction j with
    | zero =>
        intro z
        rfl
    | succ j ih =>
        intro z
        show ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (j + 1)) z
          = (⇑(sliceAc μG ρ hN2 hρcont hN β hpos))^[j + 1] z
        rw [pow_succ', Function.iterate_succ_apply']
        show (sliceAc μG ρ hN2 hρcont hN β hpos)
            (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j) z)
          = (sliceAc μG ρ hN2 hρcont hN β hpos)
            ((⇑(sliceAc μG ρ hN2 hρcont hN β hpos))^[j] z)
        rw [ih]
  rw [hiter j z, sliceDefectCLM_iterate μG ρ hN2 hρcont hN β
    hpos j z]

/-- The algebra map acts as scalar multiplication. -/
theorem sliceAlgebraMap_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℝ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (algebraMap ℝ
      (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
        sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c) x
      = (c : ℂ) • x := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp

/-- `cfc` commutes with finite sums of functions (the sum
taken pointwise). -/
theorem sliceCfc_sum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    cfc (fun μ => ∑ i ∈ s, f i μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = ∑ i ∈ s, cfc (f i) (sliceTc μG ρ hN2 hρcont hN β
          hpos) := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => (0 : ℝ)
          from rfl, sliceCfc_const μG ρ hN2 hρcont hN β hpos 0,
        map_zero]
  | insert a s has ih =>
      have hfun : (fun μ => ∑ i ∈ insert a s, f i μ)
          = (fun μ => f a μ + ∑ i ∈ s, f i μ) := by
        funext μ
        rw [Finset.sum_insert has]
      rw [hfun, Finset.sum_insert has,
        cfc_add _ _ _
          (hf a (Finset.mem_insert_self a s)).continuousOn
          ((continuous_finsetSum s
            (fun i hi => hf i
              (Finset.mem_insert_of_mem hi))).continuousOn),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- The truncation operator `p_n(T̂_c) = 1 − Â_c^n`, as a
continuous linear map. -/
noncomputable def sliceTrunc (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  cfc (fun μ : ℝ => 1 - (1 - μ) ^ n)
    (sliceTc μG ρ hN2 hρcont hN β hpos)

/-- The truncation applied: `p_n(T̂_c) x = x − Â_c^n x`. -/
theorem sliceTrunc_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceTrunc μG ρ hN2 hρcont hN β hpos n x
      = x - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x := by
  rw [sliceTrunc, sliceCfc_truncation,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

/-- The truncation is self-adjoint. -/
theorem sliceTrunc_isSelfAdjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    IsSelfAdjoint (sliceTrunc μG ρ hN2 hρcont hN β hpos n) :=
  sliceCfc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos _

/-- The truncation, unfolded. -/
theorem sliceTrunc_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ) :
    sliceTrunc μG ρ hN2 hρcont hN β hpos n
      = cfc (fun μ : ℝ => 1 - (1 - μ) ^ n)
          (sliceTc μG ρ hN2 hρcont hN β hpos) :=
  rfl

/-- Factoring a real constant out of a `cfc` pairing (real-part
form). -/
theorem sliceCfc_factor_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℝ)
    (g : ℝ → ℝ) (hg : Continuous g)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x (cfc (fun μ : ℝ => c * g μ)
      (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re
      = c * (inner ℂ x (cfc g
          (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re := by
  have e : cfc (fun μ : ℝ => c * g μ)
        (sliceTc μG ρ hN2 hρcont hN β hpos)
      = (algebraMap ℝ
          (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
            sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c)
        * cfc g (sliceTc μG ρ hN2 hρcont hN β hpos) := by
    calc cfc (fun μ : ℝ => c * g μ)
            (sliceTc μG ρ hN2 hρcont hN β hpos)
        = cfc (fun _ : ℝ => c)
              (sliceTc μG ρ hN2 hρcont hN β hpos)
            * cfc g (sliceTc μG ρ hN2 hρcont hN β hpos) :=
          cfc_mul (fun _ : ℝ => c) g
            (sliceTc μG ρ hN2 hρcont hN β hpos)
            continuous_const.continuousOn hg.continuousOn
      _ = (algebraMap ℝ
              (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
                →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β
                hpos) c)
            * cfc g (sliceTc μG ρ hN2 hρcont hN β hpos) := by
          rw [sliceCfc_const]
  rw [e]
  show (inner ℂ x ((algebraMap ℝ
      (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
        sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) c)
      (cfc g (sliceTc μG ρ hN2 hρcont hN β hpos) x))).re = _
  rw [sliceAlgebraMap_apply, inner_smul_right, Complex.mul_re]
  simp

/-- **The truncation pairing identity** (complex form):
`⟪p_n(T̂_c)x, Â_c^j p_n(T̂_c)x⟫ = ⟪x, p_n²·(1−·)^j (T̂_c) x⟫`. -/
theorem sliceTrunc_pairing (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n j : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
        (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
          (sliceTrunc μG ρ hN2 hρcont hN β hpos n x))
      = inner ℂ x (cfc (fun μ : ℝ => (1 - (1 - μ) ^ n) ^ 2
            * (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos) x) := by
  have key1 : ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
        (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
      = cfc (fun μ : ℝ => (1 - μ) ^ j * (1 - (1 - μ) ^ n))
          (sliceTc μG ρ hN2 hρcont hN β hpos) x := by
    show (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
        * sliceTrunc μG ρ hN2 hρcont hN β hpos n) x = _
    have hcj : Continuous (fun μ : ℝ => (1 - μ) ^ j) := by
      fun_prop
    have hcp : Continuous (fun μ : ℝ => 1 - (1 - μ) ^ n) := by
      fun_prop
    rw [sliceTrunc_eq,
      ← sliceCfc_defect_pow μG ρ hN2 hρcont hN β hpos j,
      ← cfc_mul _ _ _ hcj.continuousOn hcp.continuousOn]
  have key2 : (sliceTrunc μG ρ hN2 hρcont hN β hpos n)
        (cfc (fun μ : ℝ => (1 - μ) ^ j * (1 - (1 - μ) ^ n))
          (sliceTc μG ρ hN2 hρcont hN β hpos) x)
      = cfc (fun μ : ℝ => (1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos) x := by
    show (sliceTrunc μG ρ hN2 hρcont hN β hpos n
        * cfc (fun μ : ℝ => (1 - μ) ^ j * (1 - (1 - μ) ^ n))
          (sliceTc μG ρ hN2 hρcont hN β hpos)) x = _
    have hcp : Continuous (fun μ : ℝ => 1 - (1 - μ) ^ n) := by
      fun_prop
    have hcm : Continuous (fun μ : ℝ =>
        (1 - μ) ^ j * (1 - (1 - μ) ^ n)) := by
      fun_prop
    rw [sliceTrunc_eq,
      ← cfc_mul _ _ _ hcp.continuousOn hcm.continuousOn]
    refine congrArg (fun F => cfc F
      (sliceTc μG ρ hN2 hρcont hN β hpos) x) ?_
    funext μ
    ring
  calc inner ℂ (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
          (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
            (sliceTrunc μG ρ hN2 hρcont hN β hpos n x))
      = inner ℂ (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
          (cfc (fun μ : ℝ => (1 - μ) ^ j * (1 - (1 - μ) ^ n))
            (sliceTc μG ρ hN2 hρcont hN β hpos) x) := by
        rw [key1]
    _ = inner ℂ x ((sliceTrunc μG ρ hN2 hρcont hN β hpos n)
          (cfc (fun μ : ℝ => (1 - μ) ^ j * (1 - (1 - μ) ^ n))
            (sliceTc μG ρ hN2 hρcont hN β hpos) x)) :=
        sliceSelfAdjoint_inner_move μG ρ hN2 hρcont hN β hpos
          (sliceTrunc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos n)
          _ _
    _ = inner ℂ x (cfc (fun μ : ℝ => (1 - (1 - μ) ^ n) ^ 2
            * (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos) x) := by
        rw [key2]

/-- Real parts of finite sums (induction form). -/
theorem sliceRe_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (z : ι → ℂ) :
    (∑ j ∈ s, z j).re = ∑ j ∈ s, (z j).re := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has,
        Complex.add_re, ih]

/-- Applied finite sums of continuous linear maps (induction
form). -/
theorem sliceSum_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) {ι : Type*}
    [DecidableEq ι] (s : Finset ι)
    (S : ι → sliceHilbertSpace μG ρ hN2 hρcont hN β hpos
      →L[ℂ] sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (∑ j ∈ s, S j) x = ∑ j ∈ s, (S j) x := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has,
        ContinuousLinearMap.add_apply, ih]

/-- **The approximant at a truncation, as a single pairing:**
`q_K(p_n(T̂_c)x) = ⟪x, S_{K,n}(T̂_c)x⟫.re` with
`S_{K,n}(μ) = ∑_{j=1}^K j⁻¹ p_n(μ)² (1−μ)^j`. -/
theorem sliceApproxC_trunc_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K n : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
      = (inner ℂ x (cfc (fun μ : ℝ =>
            ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
              * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
          (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re := by
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      (j : ℝ)⁻¹ * (inner ℂ
          (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos))^[j]
            (sliceTrunc μG ρ hN2 hρcont hN β hpos n x))).re
        = (inner ℂ x (cfc (fun μ : ℝ => (j : ℝ)⁻¹
              * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
            (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re := by
    intro j _
    rw [← sliceAc_pow_apply μG ρ hN2 hρcont hN β hpos j,
      congrArg Complex.re (sliceTrunc_pairing μG ρ hN2
        hρcont hN β hpos n j x),
      ← sliceCfc_factor_re μG ρ hN2 hρcont hN β hpos (j : ℝ)⁻¹
        (fun μ : ℝ => (1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j)
        (by fun_prop) x]
  unfold sliceHamFormApproxC
  rw [Finset.sum_congr rfl hterm, sliceCfc_sum μG ρ hN2 hρcont
      hN β hpos (Finset.Icc 1 K)
      (fun j μ => (j : ℝ)⁻¹
        * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
      (fun j _ => by fun_prop),
    sliceSum_apply μG ρ hN2 hρcont hN β hpos (Finset.Icc 1 K)
      _ x, inner_sum, sliceRe_sum]

/-- **The approximant itself, as a single pairing:**
`q_K(x) = ⟪x, T_K(T̂_c)x⟫.re` with
`T_K(μ) = ∑_{j=1}^K j⁻¹ (1−μ)^j`. -/
theorem sliceApproxC_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x
      = (inner ℂ x (cfc (fun μ : ℝ =>
            ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * (1 - μ) ^ j)
          (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re := by
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      (j : ℝ)⁻¹ * (inner ℂ x
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos))^[j] x)).re
        = (inner ℂ x (cfc (fun μ : ℝ => (j : ℝ)⁻¹ * (1 - μ) ^ j)
            (sliceTc μG ρ hN2 hρcont hN β hpos) x)).re := by
    intro j _
    rw [← sliceAc_pow_apply μG ρ hN2 hρcont hN β hpos j,
      ← sliceCfc_defect_pow μG ρ hN2 hρcont hN β hpos j,
      ← sliceCfc_factor_re μG ρ hN2 hρcont hN β hpos (j : ℝ)⁻¹
        (fun μ : ℝ => (1 - μ) ^ j) (by fun_prop) x]
  unfold sliceHamFormApproxC
  rw [Finset.sum_congr rfl hterm, sliceCfc_sum μG ρ hN2 hρcont
      hN β hpos (Finset.Icc 1 K)
      (fun j μ => (j : ℝ)⁻¹ * (1 - μ) ^ j)
      (fun j _ => by fun_prop),
    sliceSum_apply μG ρ hN2 hρcont hN β hpos (Finset.Icc 1 K)
      _ x, inner_sum, sliceRe_sum]

/-! ### Pointwise bounds for the truncation functions. -/

/-- `0 ≤ p_n(μ)` on `[0, 1]`. -/
theorem slicePn_nonneg (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 1 - (1 - μ) ^ n := by
  have h1 : (1 - μ) ^ n ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr hμ.2) (by linarith [hμ.1])
  linarith

/-- Bernoulli: `p_n(μ) ≤ n μ` on `[0, 1]`. -/
theorem slicePn_le (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    1 - (1 - μ) ^ n ≤ (n : ℝ) * μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1m : 0 ≤ 1 - μ := sub_nonneg.mpr hμ.2
      have hstep : 1 - (1 - μ) ^ (n + 1)
          = (1 - (1 - μ) ^ n) + μ * (1 - μ) ^ n := by ring
      have h2 : μ * (1 - μ) ^ n ≤ μ := by
        have hle : (1 - μ) ^ n ≤ 1 :=
          pow_le_one₀ h1m (by linarith [hμ.1])
        calc μ * (1 - μ) ^ n ≤ μ * 1 :=
              mul_le_mul_of_nonneg_left hle hμ.1
          _ = μ := mul_one μ
      rw [hstep]
      have hcast : ((n + 1 : ℕ) : ℝ) * μ = (n : ℝ) * μ + μ := by
        push_cast
        ring
      rw [hcast]
      linarith [ih, h2]

/-- The geometric tail bound: `∑_{j=1}^K (1−μ)^j ≤ 1/μ` for
`μ ∈ (0, 1]`. -/
theorem sliceGeom_le (K : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hμ0 : μ ≠ 0) :
    ∑ j ∈ Finset.Icc 1 K, (1 - μ) ^ j ≤ 1 / μ := by
  have hμpos : 0 < μ := lt_of_le_of_ne hμ.1 (Ne.symm hμ0)
  have h1m0 : 0 ≤ 1 - μ := sub_nonneg.mpr hμ.2
  have h1m1 : (1 - μ) < 1 := by linarith
  have hsum : ∑ j ∈ Finset.Icc 1 K, (1 - μ) ^ j
      = (1 - μ) * ((1 - μ) ^ K - 1) / ((1 - μ) - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    have hcong : ∑ i ∈ Finset.range K, (1 - μ) ^ (1 + i)
        = ∑ i ∈ Finset.range K, (1 - μ) * (1 - μ) ^ i :=
      Finset.sum_congr rfl fun i _ => by rw [pow_add, pow_one]
    rw [hcong, ← Finset.mul_sum, geom_sum_eq (ne_of_lt h1m1) K,
      ← mul_div_assoc]
  rw [hsum]
  have hY : (1 - μ) * (1 - (1 - μ) ^ K) ≤ 1 := by
    have h1 : (1 - μ) ^ K ≤ 1 := pow_le_one₀ h1m0 h1m1.le
    have h2 : 1 - (1 - μ) ^ K ≤ 1 := by
      linarith [pow_nonneg h1m0 K]
    have hmul := mul_le_mul h1m1.le h2
      (sub_nonneg.mpr h1) zero_le_one
    simpa using hmul
  have e2 : (1 - μ) - 1 = -μ := by ring
  have e3 : (1 - μ) * ((1 - μ) ^ K - 1)
      = -((1 - μ) * (1 - (1 - μ) ^ K)) := by ring
  rw [e2, e3, div_neg, neg_div, neg_neg]
  exact div_le_div₀ zero_le_one hY hμpos (le_refl μ)

/-- **The `S_{K,n}` bound:** `S_{K,n}(μ) ≤ n²` on `[0, 1]`. -/
theorem sliceS_le (K n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
        * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
      ≤ (n : ℝ) ^ 2 := by
  have h1m : 0 ≤ 1 - μ := sub_nonneg.mpr hμ.2
  have hpn := slicePn_le n μ hμ
  have hpn0 := slicePn_nonneg n μ hμ
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      (j : ℝ)⁻¹ * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j)
        ≤ (n : ℝ) ^ 2 * μ * (1 - μ) ^ j := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j :=
      by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hsq : (1 - (1 - μ) ^ n) ^ 2 ≤ ((n : ℝ) * μ) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hpn hpn hpn0
        (mul_nonneg (Nat.cast_nonneg n) hμ.1)
    have h3 : (j : ℝ)⁻¹ * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j)
        ≤ (j : ℝ)⁻¹ * (((n : ℝ) * μ) ^ 2 * (1 - μ) ^ j) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsq (pow_nonneg h1m j))
        (inv_nonneg.mpr (Nat.cast_nonneg j))
    have h4 : (j : ℝ)⁻¹ * (((n : ℝ) * μ) ^ 2 * (1 - μ) ^ j)
        ≤ (n : ℝ) ^ 2 * μ * (1 - μ) ^ j := by
      have e : (j : ℝ)⁻¹ * (((n : ℝ) * μ) ^ 2 * (1 - μ) ^ j)
          = ((n : ℝ) ^ 2 * μ * (1 - μ) ^ j) * ((j : ℝ)⁻¹ * μ) := by
        ring
      rw [e]
      have hμj : (j : ℝ)⁻¹ * μ ≤ 1 := by
        have hi : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj1
        have hmul := mul_le_mul hi hμ.2 hμ.1 zero_le_one
        simpa using hmul
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * μ * (1 - μ) ^ j :=
        mul_nonneg (mul_nonneg (by positivity) hμ.1)
          (pow_nonneg h1m j)
      have hmul := mul_le_mul_of_nonneg_left hμj hnn
      simpa using hmul
    exact le_trans h3 h4
  refine le_trans (Finset.sum_le_sum hterm) ?_
  by_cases hμ0 : μ = 0
  · subst hμ0
    have hzero : ∀ j ∈ Finset.Icc 1 K,
        (n : ℝ) ^ 2 * 0 * (1 - 0) ^ j = 0 := by
      intro j _
      simp
    rw [Finset.sum_congr rfl hzero]
    simp only [Finset.sum_const_zero]
    positivity
  · have hfactor : ∑ j ∈ Finset.Icc 1 K,
          (n : ℝ) ^ 2 * μ * (1 - μ) ^ j
        = (n : ℝ) ^ 2 * μ
          * ∑ j ∈ Finset.Icc 1 K, (1 - μ) ^ j := by
      rw [Finset.mul_sum]
    rw [hfactor]
    have hμpos : 0 < μ := lt_of_le_of_ne hμ.1 (Ne.symm hμ0)
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * μ :=
      mul_nonneg (by positivity) hμ.1
    have hmul := mul_le_mul_of_nonneg_left
      (sliceGeom_le K μ hμ hμ0) hnn
    refine le_trans hmul ?_
    have hfin : (n : ℝ) ^ 2 * μ * (1 / μ) = (n : ℝ) ^ 2 := by
      rw [mul_one_div, div_eq_iff hμpos.ne']
    exact le_of_eq hfin

/-- **`S_{K,n} ≤ T_K`** pointwise on `[0, 1]`. -/
theorem sliceS_le_T (K n : ℕ) (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
        * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
      ≤ ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * (1 - μ) ^ j := by
  have h1m : 0 ≤ 1 - μ := sub_nonneg.mpr hμ.2
  have hp20 : 0 ≤ 1 - (1 - μ) ^ n := slicePn_nonneg n μ hμ
  have hp21 : 1 - (1 - μ) ^ n ≤ 1 := by
    have h1 : (1 - μ) ^ n ≤ 1 := pow_le_one₀ h1m (by linarith [hμ.1])
    linarith [pow_nonneg h1m n]
  have hsq1 : (1 - (1 - μ) ^ n) ^ 2 ≤ 1 := pow_le_one₀ hp20 hp21
  refine Finset.sum_le_sum fun j hj => ?_
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hterm : (1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j ≤ (1 - μ) ^ j := by
    calc (1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j
        ≤ 1 * (1 - μ) ^ j :=
          mul_le_mul_of_nonneg_right hsq1 (pow_nonneg h1m j)
      _ = (1 - μ) ^ j := one_mul _
  exact mul_le_mul_of_nonneg_left hterm (inv_nonneg.mpr hj0)

/-! ### Domain membership and form control. -/

/-- **The truncations lie in the form domain**, with the
approximant bound `q_K(p_n(T̂_c)x) ≤ n²‖x‖²`. -/
theorem sliceTrunc_mem_formDomain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceTrunc μG ρ hN2 hρcont hN β hpos n x
      ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos := by
  rw [sliceHamC_mem_domain_iff, sliceHamFormC_ne_top_iff]
  refine ⟨(n : ℝ) ^ 2 * ‖x‖ ^ 2, ?_⟩
  rintro _ ⟨K, rfl⟩
  show sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
      (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
    ≤ (n : ℝ) ^ 2 * ‖x‖ ^ 2
  rw [sliceApproxC_trunc_eq]
  refine le_trans (sliceCfc_pairing_mono μG ρ hN2 hρcont hN β
    hpos
    (fun μ : ℝ => ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
      * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
    (fun _ : ℝ => (n : ℝ) ^ 2) (by fun_prop) continuous_const
    (fun μ hμ => sliceS_le K n μ hμ) x) ?_
  exact (sliceCfc_pairing_const μG ρ hN2 hρcont hN β hpos
    ((n : ℝ) ^ 2) x).le

/-- **Form control:** `form(p_n(T̂_c)x) ≤ form(x)` in `ℝ≥0∞`. -/
theorem sliceFormC_trunc_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormC μG ρ hN2 hρcont hN β hpos
        (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
      ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x := by
  unfold sliceHamFormC
  refine iSup_le fun K => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (le_iSup (fun K => ENNReal.ofReal
      (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x)) K)
  rw [sliceApproxC_trunc_eq, sliceApproxC_eq]
  exact sliceCfc_pairing_mono μG ρ hN2 hρcont hN β hpos
    (fun μ : ℝ => ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
      * ((1 - (1 - μ) ^ n) ^ 2 * (1 - μ) ^ j))
    (fun μ : ℝ => ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹ * (1 - μ) ^ j)
    (by fun_prop) (by fun_prop)
    (fun μ hμ => sliceS_le_T K n μ hμ) x

/-! ### Step 0: convergence on `(ker T̂_c)⊥`. -/

/-- The kernel of the completed transfer operator, as a
submodule. -/
noncomputable abbrev sliceKerTc (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Submodule ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) :=
  LinearMap.ker (sliceTc μG ρ hN2 hρcont hN β hpos).toLinearMap

/-- Membership in the kernel is vanishing under `T̂_c`. -/
theorem sliceKerTc_mem_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (w : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    w ∈ sliceKerTc μG ρ hN2 hρcont hN β hpos
      ↔ sliceTc μG ρ hN2 hρcont hN β hpos w = 0 :=
  Iff.rfl

/-- Powers of the defect are self-adjoint (via their `cfc`
form). -/
theorem sliceAc_pow_isSelfAdjoint (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (k : ℕ) :
    IsSelfAdjoint ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ k) := by
  rw [← sliceCfc_defect_pow μG ρ hN2 hρcont hN β hpos k]
  exact sliceCfc_isSelfAdjoint μG ρ hN2 hρcont hN β hpos _

/-- Defect powers applied, one step at a time. -/
theorem sliceAc_pow_succ_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (z : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (n + 1)) z
      = (sliceAc μG ρ hN2 hρcont hN β hpos)
        (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) z) := by
  rw [pow_succ']
  rfl

/-- One step of the pairing sequence: the drop is a mixed
pairing. -/
theorem sliceASeq_succ (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) (k : ℕ) :
    (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (k + 1))
        x)).re
      = (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ k)
          x)).re
        - (inner ℂ x ((sliceTc μG ρ hN2 hρcont hN β hpos)
            (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ k)
              x))).re := by
  have e : ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (k + 1)) x
      = ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ k) x
        - (sliceTc μG ρ hN2 hρcont hN β hpos)
          (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ k) x) := by
    rw [sliceAc_pow_succ_apply μG ρ hN2 hρcont hN β hpos k x,
      sliceAc_apply]
  rw [e, inner_sub_right, Complex.sub_re]

/-- The pairing sequence `a_k = ⟪x, Â_c^k x⟫.re` is
antitone. -/
theorem sliceASeq_antitone (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    Antitone (fun n => (inner ℂ x
      (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)).re) :=
  antitone_nat_of_succ_le fun k => by
    rw [sliceASeq_succ μG ρ hN2 hρcont hN β hpos x k]
    have hmix := sliceTc_mixed_pairing_nonneg μG ρ hN2 hρcont
      hN β hpos k x
    linarith

/-- The pairing sequence is bounded below by `0`. -/
theorem sliceASeq_bddBelow (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    BddBelow (Set.range fun n => (inner ℂ x
      (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)).re) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact sliceAc_pow_pairing_nonneg μG ρ hN2 hρcont hN β hpos
    n x

/-- The pairing sequence converges. -/
theorem sliceASeq_tendsto (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ∃ L : ℝ, Filter.Tendsto (fun n => (inner ℂ x
        (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)).re)
      Filter.atTop (nhds L) :=
  ⟨⨅ n, (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n)
      x)).re,
    tendsto_atTop_ciInf
      (sliceASeq_antitone μG ρ hN2 hρcont hN β hpos x)
      (sliceASeq_bddBelow μG ρ hN2 hρcont hN β hpos x)⟩

/-- **The Cauchy identity:**
`‖Â_c^m x − Â_c^n x‖² = a_{2m} − 2a_{m+n} + a_{2n}`. -/
theorem sliceAc_pow_sub_norm_sq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (m n : ℕ) :
    ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ m) x
        - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x‖ ^ 2
      = (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ (2 * m)) x)).re
        - 2 * (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ (m + n)) x)).re
        + (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ (2 * n)) x)).re := by
  have hpow : ∀ a b : ℕ,
      ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a)
          (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b) x)
        = ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (a + b)) x := by
    intro a b
    show (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a)
        * ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b)) x = _
    rw [← pow_add]
  have hdiag : ∀ a b : ℕ,
      inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a) x)
          (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b) x)
        = inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ (a + b)) x) := by
    intro a b
    calc inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a) x)
            (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b) x)
        = inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a)
            (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b) x)) :=
          sliceSelfAdjoint_inner_move μG ρ hN2 hρcont hN β hpos
            (sliceAc_pow_isSelfAdjoint μG ρ hN2 hρcont hN β hpos
              a) x _
      _ = inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ (a + b)) x) := by
          rw [hpow a b]
  have hnorm : ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ m) x
        - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x‖ ^ 2
      = (inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ m) x
          - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)
          (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ m) x
          - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)).re :=
    (sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos
      _).symm
  rw [hnorm]
  simp only [inner_sub_left, inner_sub_right, Complex.sub_re]
  rw [hdiag m m, hdiag m n, hdiag n m, hdiag n n,
    Nat.add_comm n m, show m + m = 2 * m from (two_mul m).symm,
    show n + n = 2 * n from (two_mul n).symm]
  ring

/-- The defect orbit of any vector is Cauchy. -/
theorem sliceAc_pow_cauchy (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    CauchySeq (fun n =>
      ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x) := by
  obtain ⟨L, hL⟩ := sliceASeq_tendsto μG ρ hN2 hρcont hN β hpos x
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε2 : (0 : ℝ) < ε ^ 2 / 8 := by
    have h1 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    linarith
  obtain ⟨N₀, hdev⟩ := Metric.tendsto_atTop.mp hL (ε ^ 2 / 8) hε2
  have key : ∀ a b : ℕ, N₀ ≤ a → N₀ ≤ b →
      dist (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a) x)
        (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b) x) < ε := by
    intro a b ha hb
    rw [dist_eq_norm]
    have d1 : |(inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
          hpos) ^ (2 * a)) x)).re - L| < ε ^ 2 / 8 := by
      have h := hdev (2 * a) (by omega)
      rwa [Real.dist_eq] at h
    have d2 : |(inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
          hpos) ^ (a + b)) x)).re - L| < ε ^ 2 / 8 := by
      have h := hdev (a + b) (by omega)
      rwa [Real.dist_eq] at h
    have d3 : |(inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
          hpos) ^ (2 * b)) x)).re - L| < ε ^ 2 / 8 := by
      have h := hdev (2 * b) (by omega)
      rwa [Real.dist_eq] at h
    have hsq : ‖((sliceAc μG ρ hN2 hρcont hN β hpos) ^ a) x
          - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ b) x‖ ^ 2
        < ε ^ 2 := by
      rw [sliceAc_pow_sub_norm_sq μG ρ hN2 hρcont hN β hpos x
        a b]
      have e : (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
            hpos) ^ (2 * a)) x)).re
          - 2 * (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
            hpos) ^ (a + b)) x)).re
          + (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
            hpos) ^ (2 * b)) x)).re
        = ((inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ (2 * a)) x)).re - L)
          - 2 * ((inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
            hpos) ^ (a + b)) x)).re - L)
          + ((inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
            hpos) ^ (2 * b)) x)).re - L) := by ring
      rw [e]
      have t1 : (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
          hpos) ^ (2 * a)) x)).re - L ≤ ε ^ 2 / 8 :=
        le_trans (le_abs_self _) d1.le
      have t2 : -2 * ((inner ℂ x (((sliceAc μG ρ hN2 hρcont
          hN β hpos) ^ (a + b)) x)).re - L) ≤ ε ^ 2 / 4 := by
        have h1 : -((inner ℂ x (((sliceAc μG ρ hN2 hρcont hN
            β hpos) ^ (a + b)) x)).re - L)
            ≤ |(inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
              hpos) ^ (a + b)) x)).re - L| := neg_le_abs _
        linarith [d2.le]
      have t3 : (inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β
          hpos) ^ (2 * b)) x)).re - L ≤ ε ^ 2 / 8 :=
        le_trans (le_abs_self _) d3.le
      have hεsq : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
      linarith
    have habs := abs_lt_of_sq_lt_sq hsq hε.le
    rwa [abs_of_nonneg (norm_nonneg _)] at habs
  refine ⟨N₀, fun n hn => ?_⟩
  have hNN : N₀ ≤ N₀ := le_refl N₀
  try intro m hm
  first
    | exact key n _ hn (by assumption)
    | exact key _ n (by assumption) hn

/-- **The defect orbit dies on `(ker T̂_c)⊥`:**
`Â_c^n x → 0` for `x ⊥ ker T̂_c`. -/
theorem sliceAc_pow_tendsto_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hx : x ∈ (sliceKerTc μG ρ hN2 hρcont hN β hpos)ᗮ) :
    Filter.Tendsto (fun n =>
        ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)
      Filter.atTop (nhds 0) := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (sliceAc_pow_cauchy μG ρ hN2 hρcont hN β hpos x)
  have hshift : Filter.Tendsto (fun n =>
        ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (n + 1)) x)
      Filter.atTop (nhds y) := hy.comp (tendsto_add_atTop_nat 1)
  have hcont : Filter.Tendsto (fun n =>
        (sliceAc μG ρ hN2 hρcont hN β hpos)
          (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x))
      Filter.atTop
      (nhds ((sliceAc μG ρ hN2 hρcont hN β hpos) y)) :=
    ((sliceAc μG ρ hN2 hρcont hN β hpos).continuous.tendsto
      y).comp hy
  have hcont' : Filter.Tendsto (fun n =>
        ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ (n + 1)) x)
      Filter.atTop
      (nhds ((sliceAc μG ρ hN2 hρcont hN β hpos) y)) := by
    have h := hcont
    simp only [← sliceAc_pow_succ_apply μG ρ hN2 hρcont hN β
      hpos] at h
    exact h
  have hAy : (sliceAc μG ρ hN2 hρcont hN β hpos) y = y :=
    tendsto_nhds_unique hcont' hshift
  have hTy : (sliceTc μG ρ hN2 hρcont hN β hpos) y = 0 := by
    have h := hAy
    rw [sliceAc_apply] at h
    exact sub_eq_self.mp h
  have hyker : y ∈ sliceKerTc μG ρ hN2 hρcont hN β hpos :=
    (sliceKerTc_mem_iff μG ρ hN2 hρcont hN β hpos y).mpr hTy
  have horth : ∀ w ∈ sliceKerTc μG ρ hN2 hρcont hN β hpos,
      inner ℂ y w = 0 := by
    intro w hw
    have hw0 : (sliceTc μG ρ hN2 hρcont hN β hpos) w = 0 :=
      (sliceKerTc_mem_iff μG ρ hN2 hρcont hN β hpos w).mp hw
    have hAw : ∀ n : ℕ,
        ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) w = w := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
          rw [sliceAc_pow_succ_apply μG ρ hN2 hρcont hN β hpos
            k w, ih, sliceAc_apply, hw0, sub_zero]
    have hconst : ∀ n : ℕ,
        inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)
          w = 0 := by
      intro n
      have h1 : inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ n) x) w
          = inner ℂ x (((sliceAc μG ρ hN2 hρcont hN β hpos)
            ^ n) w) :=
        sliceSelfAdjoint_inner_move μG ρ hN2 hρcont hN β hpos
          (sliceAc_pow_isSelfAdjoint μG ρ hN2 hρcont hN β hpos
            n) x w
      rw [hAw n] at h1
      have h2 : inner ℂ w x = 0 :=
        (Submodule.mem_orthogonal (sliceKerTc μG ρ hN2 hρcont hN β
          hpos) x).mp hx w hw
      have h3 : inner ℂ x w
          = (starRingEnd ℂ) (inner ℂ w x) :=
        (inner_conj_symm x w).symm
      rw [h2, map_zero] at h3
      rw [h1]
      exact h3
    have hlim : Filter.Tendsto (fun n =>
          inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)
            w) Filter.atTop (nhds (inner ℂ y w)) :=
      hy.inner tendsto_const_nhds
    have hlim0 : Filter.Tendsto (fun n =>
          inner ℂ (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x)
            w) Filter.atTop (nhds 0) := by
      have heq : (fun n => inner ℂ
            (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n) x) w)
          = fun _ => (0 : ℂ) := funext fun n => hconst n
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hlim0
  have hyy : inner ℂ y y = 0 := horth y hyker
  have hy0 : y = 0 := inner_self_eq_zero.mp hyy
  rw [hy0] at hy
  exact hy

/-- **The truncations converge on `(ker T̂_c)⊥`:**
`p_n(T̂_c) x → x`. -/
theorem sliceTrunc_tendsto (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hx : x ∈ (sliceKerTc μG ρ hN2 hρcont hN β hpos)ᗮ) :
    Filter.Tendsto (fun n =>
        sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
      Filter.atTop (nhds x) := by
  have h := sliceAc_pow_tendsto_zero μG ρ hN2 hρcont hN β hpos
    x hx
  have heq : (fun n => sliceTrunc μG ρ hN2 hρcont hN β hpos
        n x)
      = (fun n => x - ((sliceAc μG ρ hN2 hρcont hN β hpos) ^ n)
          x) :=
    funext fun n => sliceTrunc_apply μG ρ hN2 hρcont hN β hpos
      n x
  rw [heq]
  simpa using tendsto_const_nhds.sub h

/-! ### The carrier equality. -/

/-- **Step 0 discharged — the carrier equality:**
`sliceFormClosure = (ker T̂_c)⊥`. The `⊆` direction is FG-2a's
obstruction theorem (landed in FG-2b); the `⊇` direction is the
density of the form domain inside `(ker T̂_c)⊥`, witnessed by
the truncations `p_n(T̂_c)`. -/
theorem sliceFormClosure_eq_ker_orthogonal (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceFormClosure μG ρ hN2 hρcont hN β hpos
      = (sliceKerTc μG ρ hN2 hρcont hN β hpos)ᗮ := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hz0 : inner ℂ z w = 0 :=
      sliceFormClosure_orthogonal_ker μG ρ hN2 hρcont hN β
        hpos ⟨z, hz⟩
        ((sliceKerTc_mem_iff μG ρ hN2 hρcont hN β hpos w).mp hw)
    have hzw : inner ℂ w z
        = (starRingEnd ℂ) (inner ℂ z w) :=
      (inner_conj_symm w z).symm
    rw [hz0, map_zero] at hzw
    exact hzw
  · intro x hx
    rw [sliceFormClosure_mem_iff, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp
      (sliceTrunc_tendsto μG ρ hN2 hρcont hN β hpos x hx) ε hε
    refine ⟨sliceTrunc μG ρ hN2 hρcont hN β hpos n x,
      sliceTrunc_mem_formDomain μG ρ hN2 hρcont hN β hpos n x,
      ?_⟩
    rw [dist_comm]
    exact hn n (le_refl n)

/-- **The FG-2c-0 package** (general `(G, ρ)`, hypothesis
`SliceHPosOne`): form-order `T̂_c² ≤ T̂_c`; the mixed pairings
of step 0; truncations in the form domain with form control;
the carrier equality `sliceFormClosure = (ker T̂_c)⊥`; and
strong convergence `p_n(T̂_c) x → x` on `(ker T̂_c)⊥`. -/
theorem sliceCfc_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    (sliceTc μG ρ hN2 hρcont hN β hpos) ^ 2
        ≤ sliceTc μG ρ hN2 hρcont hN β hpos
      ∧ (∀ (j : ℕ)
          (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos),
          0 ≤ (inner ℂ x ((sliceTc μG ρ hN2 hρcont hN β hpos)
            (((sliceAc μG ρ hN2 hρcont hN β hpos) ^ j)
              x))).re)
      ∧ (∀ (n : ℕ)
          (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos),
          sliceTrunc μG ρ hN2 hρcont hN β hpos n x
            ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos)
      ∧ (∀ (n : ℕ)
          (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos),
          sliceHamFormC μG ρ hN2 hρcont hN β hpos
              (sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
            ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x)
      ∧ sliceFormClosure μG ρ hN2 hρcont hN β hpos
          = (sliceKerTc μG ρ hN2 hρcont hN β hpos)ᗮ
      ∧ (∀ (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos),
          x ∈ (sliceKerTc μG ρ hN2 hρcont hN β hpos)ᗮ →
          Filter.Tendsto (fun n =>
              sliceTrunc μG ρ hN2 hρcont hN β hpos n x)
            Filter.atTop (nhds x)) :=
  ⟨sliceTc_sq_le_self μG ρ hN2 hρcont hN β hpos,
    fun j x => sliceTc_mixed_pairing_nonneg μG ρ hN2 hρcont
      hN β hpos j x,
    fun n x => sliceTrunc_mem_formDomain μG ρ hN2 hρcont hN β
      hpos n x,
    fun n x => sliceFormC_trunc_le μG ρ hN2 hρcont hN β hpos
      n x,
    sliceFormClosure_eq_ker_orthogonal μG ρ hN2 hρcont hN β
      hpos,
    fun x hx => sliceTrunc_tendsto μG ρ hN2 hρcont hN β hpos
      x hx⟩

/-- **The carrier equality at `β = 0`** (free, via
`sliceHPosOne_zero`). -/
theorem sliceFormClosure_eq_ker_orthogonal_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    sliceFormClosure μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
      = (sliceKerTc μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))ᗮ :=
  sliceFormClosure_eq_ker_orthogonal μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)

end SliceCfc

/-- **The carrier equality at the U(1) seat** (free, via
`sliceHPosOne_circle`, every `β ≥ 0`, every even `N ≥ 2`):
the FG-2b carrier `H'` of the circle transfer operator is
exactly `(ker T̂_c)⊥`. -/
theorem sliceFormClosure_eq_ker_orthogonal_circle {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) (hN : Even N) (β : ℝ)
    (hβ : 0 ≤ β) :
    sliceFormClosure (haarProb Circle) circleRep hN2
        circleRep_continuous hN β
        (sliceHPosOne_circle hN2 hN β hβ)
      = (sliceKerTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ))ᗮ :=
  sliceFormClosure_eq_ker_orthogonal (haarProb Circle)
    circleRep hN2 circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ)

end ThetLogos

