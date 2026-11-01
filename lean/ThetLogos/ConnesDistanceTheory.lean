import Mathlib.Tactic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Dual.Lemmas
import ThetLogos.ConnesDistancePost

open scoped Matrix.Norms.L2Operator ENNReal

namespace ThetLogos

/-!
# ThetLogos.ConnesDistanceTheory - GR-DIST-1: general theory of `connesDist`

**Working label only.** The module name `ConnesDistanceTheory` and
the line name GR-DIST are working labels; Jeff names.

**Program ceiling, on the face.** This module is the general
theory of a finite state-space distance: vocabulary-grade
mathematics about the registered `connesDist` of
`ConnesDistancePost`. It seats NO object; Dial 2 = 0. The
distance here is a distance between point states of a finite
commutative algebra seat; it is never a spatial separation and
is never spent as a spatial `r` anywhere in this module.

**What is proved (FULL).** The pin's three GENERAL rows
(diagonal zero, symmetry, extended triangle inequality in
`ENNReal`), the commutant finiteness criterion in both
directions, the pin's two CONDITIONAL rows discharged in their
registered conditional forms, and the scaling sanity law. The
finiteness criterion's hard direction (no commutant obstruction
implies finiteness) was pre-named in the brick pack as this
line's PARTIAL seam; it is PROVED here at the pin's full
generality (see the criterion section), so the brick lands FULL
at that seam, with no remainder and no restriction of the seat,
the index type, or the operator.

**Degeneracy discipline (K-DIST-DEG).** The `D = 0` corollary at
the end is a DEGENERACY finding - at the zero operator every
algebra element commutes, so distinct states sit at distance
infinity - and is worded as a finding, never as a metric success.
-/

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## The commutator, entrywise -/

/-- **Entry formula for the registered commutator.** The
`(x, y)` entry of `commDiag D a` is `D x y * a y - a x * D x y`:
the diagonal algebra element contributes its `y` value on the
right and its `x` value on the left. -/
theorem commDiag_apply (D : Matrix iota iota ℂ) (a : iota -> ℂ)
    (x y : iota) :
    commDiag D a x y = D x y * a y - a x * D x y := by
  simp [commDiag, diagAlg, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The commutator is additive in the algebra element. -/
theorem commDiag_add (D : Matrix iota iota ℂ) (a b : iota -> ℂ) :
    commDiag D (a + b) = commDiag D a + commDiag D b := by
  ext x y
  simp only [commDiag_apply, Pi.add_apply, Matrix.add_apply]
  ring

/-- The commutator is homogeneous in the algebra element, for a
complex scalar. -/
theorem commDiag_smul (D : Matrix iota iota ℂ) (s : ℂ)
    (a : iota -> ℂ) :
    commDiag D (s • a) = s • commDiag D a := by
  ext x y
  simp only [commDiag_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

/-- The commutator is homogeneous in the operator, for a complex
scalar. -/
theorem commDiag_smul_left (s : ℂ) (D : Matrix iota iota ℂ)
    (a : iota -> ℂ) :
    commDiag (s • D) a = s • commDiag D a := by
  ext x y
  simp only [commDiag_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The commutator with a real-scaled operator: a real scalar
acts on a complex matrix entrywise through its complex cast, so
the same homogeneity holds with the cast scalar. -/
theorem commDiag_real_smul_left (c : ℝ) (D : Matrix iota iota ℂ)
    (a : iota -> ℂ) :
    commDiag (c • D) a = (c : ℂ) • commDiag D a := by
  ext x y
  have hentry : (c • D) x y = (c : ℂ) * D x y := by
    simp [Matrix.smul_apply, Complex.real_smul]
  simp only [commDiag_apply, hentry, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## Row 1 - diagonal zero (GENERAL) -/

/-- **Row 1, pointwise form.** `connesDist D i i = 0`: every term
of the defining supremum vanishes at `i = j`. -/
theorem connesDist_self (D : Matrix iota iota ℂ) (i : iota) :
    connesDist D i i = 0 := by
  apply le_antisymm _ zero_le
  rw [connesDist_unfold]
  apply iSup_le
  intro a
  apply iSup_le
  intro _
  simp

/-- **Row 1 discharged.** The pin's registered Prop
`ConnesDistDiagZero` holds for every seat operator `D`. -/
theorem connesDistDiagZero_proved (D : Matrix iota iota ℂ) :
    ConnesDistDiagZero D :=
  fun i => connesDist_self D i

/-! ## Row 2 - symmetry (GENERAL) -/

/-- **Row 2, pointwise form.** `connesDist D i j = connesDist D j i`,
term-wise by symmetry of the norm under swapping the points. -/
theorem connesDist_comm (D : Matrix iota iota ℂ) (i j : iota) :
    connesDist D i j = connesDist D j i := by
  rw [connesDist_unfold, connesDist_unfold]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro _
  rw [norm_sub_rev]

/-- **Row 2 discharged.** The pin's registered Prop
`ConnesDistSymm` holds for every seat operator `D`. -/
theorem connesDistSymm_proved (D : Matrix iota iota ℂ) :
    ConnesDistSymm D :=
  fun i j => connesDist_comm D i j

/-! ## Row 3 - the extended triangle inequality (GENERAL) -/

/-- **Term bound.** Any single admissible term of the defining
supremum is below the distance: if `‖commDiag D a‖ ≤ 1` then
`ENNReal.ofReal ‖a i - a j‖ ≤ connesDist D i j`. -/
theorem ofReal_norm_sub_le_connesDist (D : Matrix iota iota ℂ)
    (a : iota -> ℂ) (h : ‖commDiag D a‖ ≤ 1) (i j : iota) :
    ENNReal.ofReal ‖a i - a j‖ ≤ connesDist D i j :=
  le_iSup_of_le a (le_iSup_of_le h le_rfl)

/-- **Row 3, pointwise form.** The extended triangle inequality
in `ENNReal`: `connesDist D i k ≤ connesDist D i j + connesDist D j k`,
by the pointwise norm triangle inequality and subadditivity of
the supremum. -/
theorem connesDist_triangle (D : Matrix iota iota ℂ) (i j k : iota) :
    connesDist D i k ≤ connesDist D i j + connesDist D j k := by
  rw [connesDist_unfold]
  apply iSup_le
  intro a
  apply iSup_le
  intro h
  have h1 := ofReal_norm_sub_le_connesDist D a h i j
  have h2 := ofReal_norm_sub_le_connesDist D a h j k
  have htri : ‖a i - a k‖ ≤ ‖a i - a j‖ + ‖a j - a k‖ := by
    have heq : a i - a k = (a i - a j) + (a j - a k) := by abel
    rw [heq]
    exact norm_add_le _ _
  calc ENNReal.ofReal ‖a i - a k‖
      ≤ ENNReal.ofReal (‖a i - a j‖ + ‖a j - a k‖) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal ‖a i - a j‖ + ENNReal.ofReal ‖a j - a k‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ connesDist D i j + connesDist D j k := add_le_add h1 h2

/-- **Row 3 discharged.** The pin's registered Prop
`ConnesDistTriangle` holds for every seat operator `D`. -/
theorem connesDistTriangle_proved (D : Matrix iota iota ℂ) :
    ConnesDistTriangle D :=
  fun i j k => connesDist_triangle D i j k

/-! ## The commutant criterion, forward direction (GENERAL) -/

/-- **Scaling a commuting element.** If `a` commutes with `D`
(registered form: `commDiag D a = 0`) and `s : ℂ`, the scaled
element `s • a` still commutes with `D`. -/
theorem commDiag_eq_zero_of_smul {D : Matrix iota iota ℂ}
    {a : iota -> ℂ} (ha : commDiag D a = 0) (s : ℂ) :
    commDiag D (s • a) = 0 := by
  rw [commDiag_smul, ha, smul_zero]

/-- **Criterion, forward direction (general).** If the pair
`(i, j)` carries a commutant obstruction - an algebra element
commuting with `D` yet separating `i` from `j` - then
`connesDist D i j = ⊤`. The obstruction element is scaled by an
arbitrary positive real factor: the commutator bound stays `0`
while the separation scales without bound, so the supremum is
infinite. -/
theorem connesDist_eq_top_of_hasCommutantObstruction
    (D : Matrix iota iota ℂ) {i j : iota}
    (h : HasCommutantObstruction D i j) :
    connesDist D i j = ⊤ := by
  obtain ⟨a, ha0, haij⟩ := h
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  set δ := ‖a i - a j‖ with hδdef
  have hδpos : 0 < δ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr haij)
  set t : ℝ := (r : ℝ) / δ + 1 with htdef
  have ht0 : 0 ≤ t := by
    rw [htdef]
    have h1 : 0 ≤ (r : ℝ) / δ :=
      div_nonneg (NNReal.coe_nonneg r) hδpos.le
    linarith
  set b : iota -> ℂ := ((t : ℂ)) • a with hbdef
  have hcomm : commDiag D b = 0 :=
    commDiag_eq_zero_of_smul ha0 _
  have hnorm : ‖commDiag D b‖ ≤ 1 := by
    rw [hcomm]
    simp
  have hbdiff : ‖b i - b j‖ = t * δ := by
    have hsub : b i - b j = (t : ℂ) * (a i - a j) := by
      simp only [hbdef, Pi.smul_apply, smul_eq_mul]
      rw [mul_sub]
    rw [hsub, norm_mul]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hrt : (r : ℝ) ≤ t * δ := by
    have hcalc : t * δ = (r : ℝ) + δ := by
      rw [htdef]
      field_simp
    rw [hcalc]
    have := hδpos.le
    linarith [NNReal.coe_nonneg r]
  calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) :=
        (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (t * δ) := ENNReal.ofReal_le_ofReal hrt
    _ = ENNReal.ofReal ‖b i - b j‖ := by rw [hbdiff]
    _ ≤ connesDist D i j :=
        ofReal_norm_sub_le_connesDist D b hnorm i j

/-! ## Row 4 - definiteness (CONDITIONAL, registered form) -/

/-- **Row 4, pointwise conditional form.** Under the registered
separating condition `ConnesCommSeparates D`, the distance is
definite: `connesDist D i j = 0` forces `i = j`. Directly: at a
distinct pair the separating element contributes a strictly
positive term to the supremum. -/
theorem eq_of_connesDist_eq_zero_of_separates
    (D : Matrix iota iota ℂ) (hsep : ConnesCommSeparates D)
    (i j : iota) (h : connesDist D i j = 0) : i = j := by
  by_contra hne
  obtain ⟨a, ha1, haij⟩ := hsep i j hne
  have hterm := ofReal_norm_sub_le_connesDist D a ha1 i j
  rw [h] at hterm
  have hpos : 0 < ENNReal.ofReal ‖a i - a j‖ :=
    ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr haij))
  exact not_lt_of_ge hterm (by simpa using hpos)

/-- **Row 4 discharged in its registered form.** The pin's
`ConnesDistDefiniteConditional` holds for every seat operator
`D`: under its named condition on the face, the distance is
definite. -/
theorem connesDistDefiniteConditional_proved
    (D : Matrix iota iota ℂ) :
    ConnesDistDefiniteConditional D :=
  fun hsep i j h => eq_of_connesDist_eq_zero_of_separates D hsep i j h

/-! ## The commutant criterion, hard direction: no obstruction implies finite

This is the brick's pre-named PARTIAL seam, and it closes here.
The argument is finite-dimensional: the coordinate forms of the
commutator are finitely many linear forms on the algebra-element
space; the point-difference form vanishes on the intersection of
their kernels (that is exactly the absence of a commutant
obstruction at the pair), so by the finite-dimensional span lemma
for kernels it is a finite linear combination of the commutator
coordinate forms; entrywise, each commutator entry is bounded by
the operator norm, so the point difference is bounded by a fixed
constant times the commutator norm. No seat, index type, or
operator was restricted to force this: the statement is at the
pin's full generality. -/

/-- **Entry bound by the operator norm.** Every entry of a
matrix is bounded in norm by its L2 operator norm: the entry is
one component of the image of a unit coordinate vector. -/
theorem norm_apply_le_opNorm (M : Matrix iota iota ℂ) (x y : iota) :
    ‖M x y‖ ≤ ‖M‖ := by
  have h2 := Matrix.l2_opNorm_mulVec M (PiLp.single (2 : ℝ≥0∞) y (1 : ℂ))
  rw [PiLp.norm_single, norm_one, mul_one] at h2
  have h1 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv iota ℂ).symm
      (Matrix.mulVec M (WithLp.ofLp (PiLp.single (2 : ℝ≥0∞) y (1 : ℂ))))) x
  have hcomp : (EuclideanSpace.equiv iota ℂ).symm
        (Matrix.mulVec M (WithLp.ofLp (PiLp.single (2 : ℝ≥0∞) y (1 : ℂ)))) x
      = M x y := by
    simp [Matrix.col_apply]
  rw [hcomp] at h1
  exact h1.trans h2

/-- **The commutator coordinate forms.** For a seat point pair
`p`, the linear form on algebra elements reading the `p` entry
of the commutator with `D`. -/
def commEntryLinear (D : Matrix iota iota ℂ) (p : iota × iota) :
    (iota -> ℂ) →ₗ[ℂ] ℂ where
  toFun a := commDiag D a p.1 p.2
  map_add' a b := by simp [commDiag_add, Matrix.add_apply]
  map_smul' s a := by simp [commDiag_smul, Matrix.smul_apply, smul_eq_mul]

/-- **The point-difference form.** The linear form on algebra
elements reading the difference of the point evaluations at
`i` and `j`. -/
def pointDiffLinear (i j : iota) : (iota -> ℂ) →ₗ[ℂ] ℂ where
  toFun a := a i - a j
  map_add' a b := by
    simp only [Pi.add_apply]
    ring
  map_smul' s a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_sub]

/-- **The boundedness step of the criterion.** If the pair
`(i, j)` carries no commutant obstruction for `D`, there is a
constant `C ≥ 0` bounding every point difference by `C` times
the commutator norm: `‖a i - a j‖ ≤ C * ‖commDiag D a‖` for all
algebra elements `a`. This is the finite-dimensional content of
the criterion's hard direction. -/
theorem exists_norm_sub_le_of_no_obstruction (D : Matrix iota iota ℂ)
    {i j : iota} (hno : ¬ HasCommutantObstruction D i j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : iota -> ℂ, ‖a i - a j‖ ≤ C * ‖commDiag D a‖ := by
  have hker : ⨅ p : iota × iota, LinearMap.ker (commEntryLinear D p)
      ≤ LinearMap.ker (pointDiffLinear i j) := by
    intro a ha
    rw [Submodule.mem_iInf] at ha
    have hcomm : commDiag D a = 0 := by
      ext x y
      have hxy := ha (x, y)
      rw [LinearMap.mem_ker] at hxy
      have : commDiag D a x y = 0 := hxy
      rw [this]
      simp
    rw [LinearMap.mem_ker]
    show a i - a j = 0
    by_contra hsub
    exact hno ⟨a, hcomm, sub_ne_zero.mp hsub⟩
  have hspan := mem_span_of_iInf_ker_le_ker hker
  rw [Submodule.mem_span_range_iff_exists_fun ℂ] at hspan
  obtain ⟨c, hc⟩ := hspan
  refine ⟨∑ p, ‖c p‖, Finset.sum_nonneg (fun p _ => norm_nonneg _),
    fun a => ?_⟩
  have hval : a i - a j = ∑ p, c p * commDiag D a p.1 p.2 := by
    have h := congrArg (fun f : (iota -> ℂ) →ₗ[ℂ] ℂ => f a) hc
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h
    calc a i - a j = (pointDiffLinear i j) a := rfl
      _ = ∑ p, c p * commDiag D a p.1 p.2 := by
          rw [← h]
          apply Finset.sum_congr rfl
          intro p _
          rfl
  calc ‖a i - a j‖ = ‖∑ p, c p * commDiag D a p.1 p.2‖ := by rw [hval]
    _ ≤ ∑ p, ‖c p * commDiag D a p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p, ‖c p‖ * ‖commDiag D a‖ :=
        Finset.sum_le_sum (fun p _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (norm_apply_le_opNorm _ _ _) (norm_nonneg _))
    _ = (∑ p, ‖c p‖) * ‖commDiag D a‖ := (Finset.sum_mul ..).symm

/-- **Criterion, hard direction (the pre-named seam, closed).**
If the pair `(i, j)` carries no commutant obstruction for `D`,
then `connesDist D i j < ⊤`: every admissible term is bounded by
the constant of the boundedness step. -/
theorem connesDist_lt_top_of_no_obstruction (D : Matrix iota iota ℂ)
    {i j : iota} (hno : ¬ HasCommutantObstruction D i j) :
    connesDist D i j < ⊤ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sub_le_of_no_obstruction D hno
  have hle : connesDist D i j ≤ ENNReal.ofReal C := by
    rw [connesDist_unfold]
    apply iSup_le
    intro a
    apply iSup_le
    intro h
    apply ENNReal.ofReal_le_ofReal
    exact (hC a).trans (mul_le_of_le_one_right hC0 h)
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- **Row 5 discharged in its registered form.** The pin's
`ConnesDistFiniteConditional` holds for every seat operator
`D`: under its named condition on the face - no commutant
obstruction anywhere - the distance is finite at every pair.
This is the same content as the criterion's hard direction,
stated as one seam, not two. -/
theorem connesDistFiniteConditional_proved
    (D : Matrix iota iota ℂ) :
    ConnesDistFiniteConditional D :=
  fun hno i j => connesDist_lt_top_of_no_obstruction D (hno i j)

/-- **The commutant finiteness criterion, in full.** At any pair
of seat points, `connesDist D i j = ⊤` if and only if the pair
carries a commutant obstruction. Both directions are proved at
the pin's full generality, so the criterion's pre-named hard
direction is closed, not merely named. -/
theorem connesDist_eq_top_iff_hasCommutantObstruction
    (D : Matrix iota iota ℂ) (i j : iota) :
    connesDist D i j = ⊤ ↔ HasCommutantObstruction D i j := by
  constructor
  · intro htop
    by_contra hno
    have hlt := connesDist_lt_top_of_no_obstruction D hno
    rw [htop] at hlt
    exact lt_irrefl _ hlt
  · exact connesDist_eq_top_of_hasCommutantObstruction D

/-! ## The scaling sanity law -/

/-- **Scaling, first inequality.** Scaling the operator by a
positive real `c` scales the distance by at most `c⁻¹` (in the
`ENNReal.ofReal` form): admissible elements for `c • D` are,
after rescaling by `c`, admissible for `D` with separations
scaled by `c`. -/
theorem connesDist_smul_le (D : Matrix iota iota ℂ) {c : ℝ}
    (hc : 0 < c) (i j : iota) :
    connesDist (c • D) i j
      ≤ (ENNReal.ofReal c)⁻¹ * connesDist D i j := by
  rw [connesDist_unfold]
  apply iSup_le
  intro a
  apply iSup_le
  intro h
  set b : iota -> ℂ := (c : ℂ) • a with hbdef
  have hcomm : commDiag D b = commDiag (c • D) a := by
    rw [hbdef, commDiag_smul, commDiag_real_smul_left]
  have hb1 : ‖commDiag D b‖ ≤ 1 := by
    rw [hcomm]
    exact h
  have hdiff : ‖b i - b j‖ = c * ‖a i - a j‖ := by
    have hsub : b i - b j = (c : ℂ) * (a i - a j) := by
      simp only [hbdef, Pi.smul_apply, smul_eq_mul]
      rw [mul_sub]
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
  calc ENNReal.ofReal ‖a i - a j‖
      = ENNReal.ofReal (c⁻¹ * ‖b i - b j‖) := by
        rw [hdiff]
        congr 1
        rw [inv_mul_cancel_left₀ hc.ne']
    _ = (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal ‖b i - b j‖ := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
          ENNReal.ofReal_inv_of_pos hc]
    _ ≤ (ENNReal.ofReal c)⁻¹ * connesDist D i j :=
        mul_le_mul_right (ofReal_norm_sub_le_connesDist D b hb1 i j) _

/-- **Scaling, second inequality.** The distance for `D` is at
most `c` times the distance for the scaled operator `c • D`,
for positive real `c`: admissible elements for `D` rescale to
admissible elements for `c • D` with separations scaled by
`c⁻¹`. -/
theorem connesDist_le_smul (D : Matrix iota iota ℂ) {c : ℝ}
    (hc : 0 < c) (i j : iota) :
    connesDist D i j
      ≤ ENNReal.ofReal c * connesDist (c • D) i j := by
  rw [connesDist_unfold]
  apply iSup_le
  intro b
  apply iSup_le
  intro h
  set a : iota -> ℂ := (c : ℂ)⁻¹ • b with hadef
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcomm : commDiag (c • D) a = commDiag D b := by
    rw [hadef, commDiag_real_smul_left, commDiag_smul, smul_smul,
      mul_inv_cancel₀ hcne, one_smul]
  have ha1 : ‖commDiag (c • D) a‖ ≤ 1 := by
    rw [hcomm]
    exact h
  have hdiff : ‖a i - a j‖ = c⁻¹ * ‖b i - b j‖ := by
    have hsub : a i - a j = (c : ℂ)⁻¹ * (b i - b j) := by
      simp only [hadef, Pi.smul_apply, smul_eq_mul]
      rw [mul_sub]
    rw [hsub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
  calc ENNReal.ofReal ‖b i - b j‖
      = ENNReal.ofReal (c * ‖a i - a j‖) := by
        rw [hdiff]
        congr 1
        rw [mul_inv_cancel_left₀ hc.ne']
    _ = ENNReal.ofReal c * ENNReal.ofReal ‖a i - a j‖ :=
        ENNReal.ofReal_mul hc.le
    _ ≤ ENNReal.ofReal c * connesDist (c • D) i j :=
        mul_le_mul_right
          (ofReal_norm_sub_le_connesDist (c • D) a ha1 i j) _

/-- **The scaling sanity law (exact proved form).** For a real
scalar `c > 0`,
`connesDist (c • D) i j = (ENNReal.ofReal c)⁻¹ * connesDist D i j`
in `ENNReal`: the honest transport of the commutator bound under
scaling the operator - admissibility is preserved after
rescaling the algebra element, and separations scale by `c⁻¹`.
Here `c • D` is the real scalar action on the complex matrix,
read entrywise through the cast `(c : ℂ)`. -/
theorem connesDist_smul (D : Matrix iota iota ℂ) {c : ℝ}
    (hc : 0 < c) (i j : iota) :
    connesDist (c • D) i j
      = (ENNReal.ofReal c)⁻¹ * connesDist D i j := by
  apply le_antisymm (connesDist_smul_le D hc i j)
  have h2 := connesDist_le_smul D hc i j
  have hne0 : ENNReal.ofReal c ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hc).ne'
  have hnetop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  calc (ENNReal.ofReal c)⁻¹ * connesDist D i j
      ≤ (ENNReal.ofReal c)⁻¹
          * (ENNReal.ofReal c * connesDist (c • D) i j) :=
        mul_le_mul_right h2 _
    _ = connesDist (c • D) i j := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]

/-! ## Degenerate seat: `D = 0` (K-DIST-DEG finding) -/

/-- **DEGENERACY FINDING (K-DIST-DEG), not a metric result.** At
the zero operator, every algebra element commutes, so the
coordinate element separating any two distinct seat points is a
commutant obstruction, and by the criterion the distance is
infinity at every distinct pair: the zero operator's distance is
the extended trivial one. Stated as a finding about a degenerate
seat; it decides the separation question negatively there and
is not a metric success. -/
theorem connesDist_zero_eq_top_of_ne {i j : iota} (hij : i ≠ j) :
    connesDist (0 : Matrix iota iota ℂ) i j = ⊤ := by
  apply connesDist_eq_top_of_hasCommutantObstruction
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · ext x y
    simp [commDiag_apply]
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm]
    exact one_ne_zero

end ThetLogos
