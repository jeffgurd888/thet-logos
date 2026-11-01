import ThetLogos.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

open Filter Topology ComplexInnerProductSpace
open scoped ENNReal NNReal InnerProductSpace

namespace ThetLogos

/-!
# Trace-class / Schatten stock at finite seats - SHELF-11

General-API stock, built under the SHELF fill commission
(pack: `routeb-general-scratch/pack-shelf-11.md`). This is the
last unworked seat of the ratified SHELF rotation: trace-class
and Schatten-class stock for the operator seats the corpus
computes with. The neighbour is SHELF-3a-i
(`HilbertSchmidt.lean`: `IsHilbertSchmidt`,
`hilbertSchmidtNormSq`, `hilbertSchmidtNormSq_eq`,
`IsHilbertSchmidt.adjoint`) and SHELF-3a-ii
(`IntegralKernelHS.lean`: `integralKernelOp`,
`integralKernel_hilbertSchmidtNormSq`); both are CITED here,
never forked. In-corpus finite trace usage is `Matrix.trace`
throughout the spectral-action seats (e.g.
`SpectralActionFinite.lean`'s `trace_sq_double_sum` /
`tr_DF_sq_yukawa`, `PartialTrace.lean`'s
`trace_partialTraceRight`, `DixmierTrace.lean`'s finite-level
`dixmierTrace_padProfile`).

## Probe inventory (pin: Mathlib v4.35.0-rc3, grepped 2026-11-01)

* NO `Schatten` definition anywhere in the pin; NO trace-class
  operator definition either - the only "trace class" hits are
  Lean elaborator trace classes (`registerTraceClass`) and one
  TODO comment (a "symmetric trace class operator" wish in
  `Probability/Distributions/Gaussian/Multivariate.lean`).
  NO Hilbert-Schmidt API in the pin either (that is why
  SHELF-3a built it in-corpus).
* What the pin DOES carry, and what this module consumes:
  - `LinearMap.trace` for finite-dimensional spaces
    (`LinearAlgebra/Trace.lean`), with `LinearMap.trace_mul_comm`,
    `LinearMap.trace_comp_comm'`, `LinearMap.trace_eq_matrix_trace`;
  - the Hilbert form `LinearMap.trace_eq_sum_inner`
    (`Analysis/InnerProductSpace/Trace.lean`): the trace of a
    finite-dimensional operator is the sum of
    `⟪b i, T (b i)⟫` over ANY orthonormal basis `b` - the
    linear-algebra fact and its Hilbert form are both owned by
    the pin, so clause 1 below is the stock built ON them
    (adjoint, positivity, the HS weld), not a re-proof;
  - `LinearMap.IsPositive.trace_nonneg` and
    `LinearMap.isPositive_adjoint_comp_self`
    (`Analysis/InnerProductSpace/Positive.lean`);
  - finite-dimensional singular values
    `LinearMap.singularValues` (`Analysis/InnerProductSpace/
    SingularValues.lean`): a finitely supported `ℕ →₀ ℝ`,
    with `LinearMap.singularValues_nonneg`,
    `LinearMap.support_singularValues`,
    `LinearMap.card_support_singularValues`,
    `LinearMap.sq_singularValues_fin`,
    `LinearMap.singularValues_eq_zero_iff`. That file's own
    TODO names the missing infinite-dimensional generalization
    (approximation numbers) - see the seam below;
  - the matrix API: `Matrix.trace_mul_comm`,
    `Matrix.trace_conjTranspose`,
    `Matrix.PosSemidef.trace_nonneg`.
    (`Matrix.trace_conjTranspose_mul_self_eq_zero_iff` also
    exists, but only for ordered star rings - it does not
    apply over `ℂ`, so the diagonal equality case below is
    proved from the HS identity instead.)

## Contents

1. Finite-seat trace stock (linear maps on a finite-dimensional
   Hilbert space over `ℂ`): `opTrace`, its orthonormal-basis
   formula and basis independence, cyclicity (product and
   rectangular composition forms), the adjoint identity
   `tr (T†) = star (tr T)`, additivity / scalar / identity
   values, and positivity for `T† ∘ₗ T` in the sharp form:
   `tr (T† ∘ₗ T)` is the real Hilbert-Schmidt sum
   `∑ i, ‖T (b i)‖ ^ 2`, hence nonnegative, and zero iff
   `T = 0`.
2. The Hilbert-Schmidt weld against SHELF-3a: for a continuous
   linear map at a finite seat, the same trace is
   `hilbertSchmidtNormSq T b.toHilbertBasis` (SHELF-3a-i's
   definition, cited); every finite-seat operator is
   Hilbert-Schmidt (`isHilbertSchmidt_of_finite`), with the
   norm bound `‖T‖₂² ≤ card ι * ‖T‖ ^ 2` in the seat's own
   data, and the trace bound
   `‖tr T‖ ≤ card ι * sqrt (‖T‖₂²)`.
3. Schatten stock at finite seats, from the pin's singular
   values: `schattenOneNorm` (the `ℓ¹` sum of the singular
   values), `schattenTwoNormSq` (the `ℓ²` sum of their
   squares), and `IsTraceClassFin` - summability of the
   singular-value sequence, which at a finite seat is
   DEFINITIONAL (the sequence is a `Finsupp`, finite support
   by construction; the honest content is the norm bound).
   Landed: `schattenOneNorm` is the `tsum` of the singular
   values; every finite-seat operator is trace class in this
   sense; the Schatten bound
   `‖T‖₁ ≤ sqrt (finrank) * sqrt (‖T‖₂²)` (Cauchy-Schwarz on
   the support, whose cardinality is the rank, by the pin);
   and `‖T‖₂²` is exactly the real trace of `T† ∘ₗ T`
   (the eigenvalue weld).
4. A named concrete seat: diagonal matrices. For
   `Matrix.diagonal d` the trace is `∑ i, d i`, its
   Hilbert-Schmidt trace `tr (Dᴴ * D)` is
   `∑ i, ‖d i‖ ^ 2`, and the diagonal trace norm
   `diagTraceNorm d = ∑ i, ‖d i‖` bounds the trace. (The
   corpus's finite Dirac seats are assembled from diagonal /
   Yukawa blocks; this is the Schatten membership of that
   family, with the norm in the seat's own data.)

## The seam (pre-named PARTIAL)

Infinite-dimensional trace-class theory is NOT landed and is
named PARTIAL here, at exactly the missing pin API:
basis-independence of the trace for general (non-finite)
Hilbert spaces, Lidskii's theorem, Schatten ideals as Banach
spaces, and singular values beyond finite dimension (the
pin's `SingularValues.lean` TODO: approximation numbers for
continuous linear maps between possibly-infinite-dimensional
spaces) - none of `TraceClass`, `Schatten`, Lidskii, or an
approximation-number API exists in the pin (probe above), and
SHELF-3a's `IsHilbertSchmidt` / `hilbertSchmidtNormSq` are the
only infinite-dimensional stock the corpus owns in this area.
What lands in this module is the finite-seat theory whole.

NO CLAIM; dials 0/4. General-API stock only.
-/

section FiniteTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]
  {ι : Type*} [Fintype ι]

/-- The trace of a finite-dimensional operator, as Hilbert-seat
stock: this is the pin's `LinearMap.trace ℂ E`, registered here
under the corpus name used by the welds below. -/
noncomputable def opTrace (T : E →ₗ[ℂ] E) : ℂ :=
  LinearMap.trace ℂ E T

/-- **Basis formula (Hilbert form).** The trace is the sum of
the diagonal inner products over any orthonormal basis. This
is the pin's `LinearMap.trace_eq_sum_inner`, cited. -/
theorem opTrace_eq_sum_inner (T : E →ₗ[ℂ] E) (b : OrthonormalBasis ι ℂ E) :
    opTrace T = ∑ i, ⟪b i, T (b i)⟫_ℂ :=
  LinearMap.trace_eq_sum_inner T b

/-- **Basis independence (Hilbert form).** The diagonal-inner-
product sums over any two orthonormal bases agree - both are
`opTrace T`. -/
theorem opTrace_sum_inner_basis_indep (T : E →ₗ[ℂ] E)
    (b : OrthonormalBasis ι ℂ E) {κ : Type*} [Fintype κ]
    (c : OrthonormalBasis κ ℂ E) :
    (∑ i, ⟪b i, T (b i)⟫_ℂ) = ∑ j, ⟪c j, T (c j)⟫_ℂ := by
  rw [← opTrace_eq_sum_inner T b, ← opTrace_eq_sum_inner T c]

/-- **Cyclicity.** `tr (S * T) = tr (T * S)` for endomorphisms
(the pin's `LinearMap.trace_mul_comm`, cited). -/
theorem opTrace_mul_comm (S T : E →ₗ[ℂ] E) :
    opTrace (S * T) = opTrace (T * S) :=
  LinearMap.trace_mul_comm ℂ S T

/-- **Cyclicity, rectangular form.** For `S : E →ₗ[ℂ] F` and
`T : F →ₗ[ℂ] E`, `tr (T ∘ₗ S) = tr (S ∘ₗ T)` (the pin's
`LinearMap.trace_comp_comm'`, cited). -/
theorem opTrace_comp_comm (S : E →ₗ[ℂ] F) (T : F →ₗ[ℂ] E) :
    opTrace (T ∘ₗ S) = opTrace (S ∘ₗ T) :=
  LinearMap.trace_comp_comm' S T

/-- The trace is additive (the pin's trace is a linear map). -/
theorem opTrace_add (S T : E →ₗ[ℂ] E) :
    opTrace (S + T) = opTrace S + opTrace T := by
  simp [opTrace]

/-- The trace is homogeneous (the pin's trace is a linear map). -/
theorem opTrace_smul (c : ℂ) (T : E →ₗ[ℂ] E) :
    opTrace (c • T) = c * opTrace T := by
  simp [opTrace]

/-- The trace of the identity is the (complex) dimension. -/
theorem opTrace_one : opTrace (1 : E →ₗ[ℂ] E) = (Module.finrank ℂ E : ℂ) := by
  rw [opTrace, LinearMap.trace_one]

/-- **Adjoint identity.** `tr (T†) = star (tr T)`, computed in
an orthonormal basis from `LinearMap.adjoint_inner_right` and
`inner_conj_symm`. -/
theorem opTrace_adjoint (T : E →ₗ[ℂ] E) (b : OrthonormalBasis ι ℂ E) :
    opTrace (LinearMap.adjoint T) = star (opTrace T) := by
  rw [opTrace_eq_sum_inner (LinearMap.adjoint T) b, opTrace_eq_sum_inner T b,
    star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.adjoint_inner_right]
  exact (inner_conj_symm (T (b i)) (b i)).symm

/-- **Positivity identity (the sharp form).** For
`T : E →ₗ[ℂ] F` and any orthonormal basis `b` of `E`,
`tr (T† ∘ₗ T)` is the real number `∑ i, ‖T (b i)‖ ^ 2`,
cast to `ℂ`. -/
theorem opTrace_adjoint_comp_self (T : E →ₗ[ℂ] F)
    (b : OrthonormalBasis ι ℂ E) :
    opTrace (LinearMap.adjoint T ∘ₗ T)
      = ((∑ i, ‖T (b i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [opTrace_eq_sum_inner (LinearMap.adjoint T ∘ₗ T) b, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact_mod_cast inner_self_eq_norm_sq_to_K (T (b i))

/-- **Positivity.** `0 ≤ (tr (T† ∘ₗ T)).re`. -/
theorem opTrace_adjoint_comp_self_re_nonneg (T : E →ₗ[ℂ] F)
    (b : OrthonormalBasis ι ℂ E) :
    0 ≤ (opTrace (LinearMap.adjoint T ∘ₗ T)).re := by
  rw [opTrace_adjoint_comp_self T b]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The trace of `T† ∘ₗ T` has zero imaginary part: it is a
nonnegative real, by `opTrace_adjoint_comp_self`. -/
theorem opTrace_adjoint_comp_self_im (T : E →ₗ[ℂ] F)
    (b : OrthonormalBasis ι ℂ E) :
    (opTrace (LinearMap.adjoint T ∘ₗ T)).im = 0 := by
  rw [opTrace_adjoint_comp_self T b]
  simp only [Complex.ofReal_im]

/-- **Positivity, equality case.** `tr (T† ∘ₗ T) = 0` iff
`T = 0`: the Hilbert-Schmidt sum vanishes iff `T` vanishes on
a basis. -/
theorem opTrace_adjoint_comp_self_eq_zero_iff (T : E →ₗ[ℂ] F)
    (b : OrthonormalBasis ι ℂ E) :
    opTrace (LinearMap.adjoint T ∘ₗ T) = 0 ↔ T = 0 := by
  rw [opTrace_adjoint_comp_self T b]
  constructor
  · intro h
    have hsum : (∑ i, ‖T (b i)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
    have hall : ∀ i ∈ Finset.univ, ‖T (b i)‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (‖T (b i)‖))).mp hsum
    have hzero : ∀ i, T (b i) = 0 := by
      intro i
      have hi := hall i (Finset.mem_univ i)
      rwa [sq_eq_zero_iff, norm_eq_zero] at hi
    exact b.toBasis.ext (fun i => by simp [hzero i])
  · intro h
    rw [h]
    simp

end FiniteTrace

section HilbertSchmidtWeld

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] [CompleteSpace E] [CompleteSpace F]
  {ι : Type*} [Fintype ι]

/-- **The Hilbert-Schmidt weld.** For a continuous linear map
`T` at a finite seat, the trace of `T† ∘ₗ T` is exactly
SHELF-3a-i's `hilbertSchmidtNormSq T b.toHilbertBasis`, cast
to `ℂ` - the two landed stocks agree where they overlap.
The adjoint identification is the pin's
`ContinuousLinearMap.adjoint_toLinearMap`. -/
theorem clm_opTrace_adjoint_comp_self_eq_hs (T : E →L[ℂ] E)
    (b : OrthonormalBasis ι ℂ E) :
    opTrace ((ContinuousLinearMap.adjoint T).toLinearMap ∘ₗ T.toLinearMap)
      = ((hilbertSchmidtNormSq T b.toHilbertBasis : ℝ) : ℂ) := by
  have hadj : (ContinuousLinearMap.adjoint T).toLinearMap
      = LinearMap.adjoint T.toLinearMap :=
    ContinuousLinearMap.adjoint_toLinearMap T
  rw [hadj, opTrace_adjoint_comp_self T.toLinearMap b]
  unfold hilbertSchmidtNormSq
  rw [tsum_eq_sum (s := Finset.univ) (fun j hj => absurd (Finset.mem_univ j) hj)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [OrthonormalBasis.coe_toHilbertBasis, ContinuousLinearMap.coe_coe]

/-- **Every finite-seat operator is Hilbert-Schmidt**
(SHELF-3a-i's `IsHilbertSchmidt`): at a finite seat the
defining summability is over the finite index type of
`stdOrthonormalBasis`. -/
theorem isHilbertSchmidt_of_finite (T : E →L[ℂ] F) : IsHilbertSchmidt T := by
  refine (isHilbertSchmidt_iff T
    (stdOrthonormalBasis ℂ E).toHilbertBasis).mpr ?_
  exact Summable.of_finite

/-- **HS norm bound in the seat's own data.**
`‖T‖₂² ≤ card ι * ‖T‖ ^ 2` for any orthonormal basis index
`ι`: each basis vector has norm `1`, so each summand is at
most `‖T‖ ^ 2`. -/
theorem hilbertSchmidtNormSq_le_card_mul_opNorm_sq (T : E →L[ℂ] F)
    (b : OrthonormalBasis ι ℂ E) :
    hilbertSchmidtNormSq T b.toHilbertBasis
      ≤ (Fintype.card ι : ℝ) * ‖T‖ ^ 2 := by
  unfold hilbertSchmidtNormSq
  rw [tsum_eq_sum (s := Finset.univ) (fun j hj => absurd (Finset.mem_univ j) hj)]
  have hnorm : ∀ i, ‖(b.toHilbertBasis) i‖ = 1 := by
    intro i
    rw [OrthonormalBasis.coe_toHilbertBasis]
    exact b.orthonormal.1 i
  have hle : ∀ i ∈ Finset.univ, ‖T ((b.toHilbertBasis) i)‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    intro i _
    have h1 : ‖T ((b.toHilbertBasis) i)‖ ≤ ‖T‖ * ‖(b.toHilbertBasis) i‖ :=
      T.le_opNorm _
    rw [hnorm i, mul_one] at h1
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i, ‖T ((b.toHilbertBasis) i)‖ ^ 2
      ≤ ∑ _i ∈ Finset.univ, ‖T‖ ^ 2 := Finset.sum_le_sum hle
    _ = (Fintype.card ι : ℝ) * ‖T‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Trace bound.** `‖tr T‖ ≤ card ι * sqrt (‖T‖₂²)`: the
trace is a sum of `card ι` inner products, each of norm at
most the Hilbert-Schmidt norm (one summand of a nonnegative
sum). -/
theorem norm_opTrace_le_card_mul_sqrt_hs (T : E →L[ℂ] E)
    (b : OrthonormalBasis ι ℂ E) :
    ‖opTrace T.toLinearMap‖
      ≤ (Fintype.card ι : ℝ)
        * Real.sqrt (hilbertSchmidtNormSq T b.toHilbertBasis) := by
  have hS : ∀ i, ‖T (b i)‖ ^ 2
      ≤ hilbertSchmidtNormSq T b.toHilbertBasis := by
    intro i
    unfold hilbertSchmidtNormSq
    rw [tsum_eq_sum (s := Finset.univ) (fun j hj => absurd (Finset.mem_univ j) hj)]
    have hcoe : ∀ j, ‖T ((b.toHilbertBasis) j)‖ = ‖T (b j)‖ := by
      intro j
      rw [OrthonormalBasis.coe_toHilbertBasis]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hcoe j])]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (‖T (b j)‖))
      (Finset.mem_univ i)
  have hnorm1 : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  calc ‖opTrace T.toLinearMap‖
      = ‖∑ i, ⟪b i, T.toLinearMap (b i)⟫_ℂ‖ := by
        rw [opTrace_eq_sum_inner T.toLinearMap b]
    _ ≤ ∑ i, ‖⟪b i, T.toLinearMap (b i)⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖T (b i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_inner_le_norm (𝕜 := ℂ) (b i) (T (b i))
        rwa [hnorm1 i, one_mul] at h
    _ ≤ ∑ _i ∈ Finset.univ,
          Real.sqrt (hilbertSchmidtNormSq T b.toHilbertBasis) := by
        apply Finset.sum_le_sum
        intro i _
        show ‖T (b i)‖ ≤ _
        rw [← Real.sqrt_sq (norm_nonneg _)]
        exact Real.sqrt_le_sqrt (hS i)
    _ = (Fintype.card ι : ℝ)
          * Real.sqrt (hilbertSchmidtNormSq T b.toHilbertBasis) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end HilbertSchmidtWeld

section SchattenFinite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- The **Schatten-1 (trace) norm at a finite seat**: the sum
of the pin's singular values `LinearMap.singularValues T`
(a finitely supported `ℕ →₀ ℝ`). -/
noncomputable def schattenOneNorm (T : E →ₗ[ℂ] F) : ℝ :=
  T.singularValues.sum (fun _ s => s)

/-- The **Schatten-2 norm squared at a finite seat**: the sum
of the squares of the singular values. By
`schattenTwoNormSq_eq_opTrace_re` below this is the
Hilbert-Schmidt norm squared. -/
noncomputable def schattenTwoNormSq (T : E →ₗ[ℂ] F) : ℝ :=
  T.singularValues.sum (fun _ s => s ^ 2)

/-- **Trace-class at a finite seat (definitional).** `T` is
trace class if its singular-value sequence is summable - the
infinite-dimensional definition, restricted to the seat. At
a finite seat this holds for EVERY operator
(`isTraceClassFin_of_finite`): the pin's singular values are
a `Finsupp`, of finite support by construction. The honest
stock is therefore not the membership but the norm bound
`schattenOneNorm_le` below. -/
def IsTraceClassFin (T : E →ₗ[ℂ] F) : Prop :=
  Summable (fun i => T.singularValues i)

/-- The Schatten-1 norm is the `tsum` of the singular values:
the `Finsupp` sum over the support is the infinite sum, all
of whose off-support terms vanish. -/
theorem schattenOneNorm_eq_tsum (T : E →ₗ[ℂ] F) :
    schattenOneNorm T = ∑' i, T.singularValues i := by
  unfold schattenOneNorm Finsupp.sum
  rw [tsum_eq_sum (s := T.singularValues.support)
    (fun j hj => Finsupp.notMem_support_iff.mp hj)]

/-- **Every finite-seat operator is trace class** in the
sense of `IsTraceClassFin`: its singular values have finite
support. -/
theorem isTraceClassFin_of_finite (T : E →ₗ[ℂ] F) : IsTraceClassFin T := by
  unfold IsTraceClassFin
  exact summable_of_ne_finset_zero (s := T.singularValues.support)
    (fun j hj => Finsupp.notMem_support_iff.mp hj)

/-- The Schatten-1 norm is nonnegative. -/
theorem schattenOneNorm_nonneg (T : E →ₗ[ℂ] F) : 0 ≤ schattenOneNorm T := by
  unfold schattenOneNorm
  exact Finsupp.sum_nonneg (fun i _ => T.singularValues_nonneg i)

/-- The Schatten-2 norm squared is nonnegative. -/
theorem schattenTwoNormSq_nonneg (T : E →ₗ[ℂ] F) :
    0 ≤ schattenTwoNormSq T := by
  unfold schattenTwoNormSq
  exact Finsupp.sum_nonneg (fun i _ => sq_nonneg _)

/-- The Schatten-1 norm vanishes iff the operator does
(the pin's `LinearMap.singularValues_eq_zero_iff`). -/
theorem schattenOneNorm_eq_zero_iff (T : E →ₗ[ℂ] F) :
    schattenOneNorm T = 0 ↔ T = 0 := by
  unfold schattenOneNorm
  constructor
  · intro h
    have hall : ∀ i ∈ T.singularValues.support, T.singularValues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => T.singularValues_nonneg i)).mp h
    have hzero : T.singularValues = 0 := by
      ext i
      by_cases hi : i ∈ T.singularValues.support
      · rw [hall i hi]; simp
      · simp [Finsupp.notMem_support_iff.mp hi]
    exact (LinearMap.singularValues_eq_zero_iff T).mp hzero
  · intro h
    rw [h]
    simp

/-- **Schatten bound.** `‖T‖₁ ≤ sqrt (finrank ℂ E) * ‖T‖₂`:
Cauchy-Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) on the
support of the singular values, whose cardinality is the
rank of `T` (the pin's `card_support_singularValues`), at
most the dimension of the domain. -/
theorem schattenOneNorm_le (T : E →ₗ[ℂ] F) :
    schattenOneNorm T
      ≤ Real.sqrt (Module.finrank ℂ E : ℝ)
        * Real.sqrt (schattenTwoNormSq T) := by
  have hcs : (schattenOneNorm T) ^ 2
      ≤ (T.singularValues.support.card : ℝ) * schattenTwoNormSq T := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq T.singularValues.support
      (fun _ => (1 : ℝ)) (fun i => T.singularValues i)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have hone : schattenOneNorm T
        = ∑ i ∈ T.singularValues.support, T.singularValues i := by
      unfold schattenOneNorm Finsupp.sum
      apply Finset.sum_congr rfl
      intro i _
      simp
    have htwo : schattenTwoNormSq T
        = ∑ i ∈ T.singularValues.support, (T.singularValues i) ^ 2 := by
      unfold schattenTwoNormSq Finsupp.sum
      apply Finset.sum_congr rfl
      intro i _
      simp
    rw [hone, htwo]
    exact h
  have hcard : (T.singularValues.support.card : ℝ)
      ≤ (Module.finrank ℂ E : ℝ) := by
    rw [LinearMap.card_support_singularValues]
    exact_mod_cast LinearMap.finrank_range_le T
  have hle : (schattenOneNorm T) ^ 2
      ≤ (Module.finrank ℂ E : ℝ) * schattenTwoNormSq T :=
    hcs.trans (by
      apply mul_le_mul_of_nonneg_right _ (schattenTwoNormSq_nonneg T)
      exact hcard)
  have hsqrt : schattenOneNorm T
      ≤ Real.sqrt ((Module.finrank ℂ E : ℝ) * schattenTwoNormSq T) :=
    Real.le_sqrt_of_sq_le hle
  rwa [Real.sqrt_mul (by positivity)] at hsqrt

/-- **The Schatten-2 / trace weld.** The Schatten-2 norm
squared is the real trace of `T† ∘ₗ T`: both are the sum of
the eigenvalues of `T† ∘ₗ T` - on the singular side by the
pin's `sq_singularValues_fin`, on the trace side by the
pin's `IsSymmetric.trace_eq_sum_eigenvalues`. Terms past
the rank vanish on both sides. -/
theorem schattenTwoNormSq_eq_opTrace_re (T : E →ₗ[ℂ] F) :
    schattenTwoNormSq T = (opTrace (LinearMap.adjoint T ∘ₗ T)).re := by
  have hsymm : (LinearMap.adjoint T ∘ₗ T).IsSymmetric :=
    T.isSymmetric_adjoint_comp_self
  have hsum : schattenTwoNormSq T
      = ∑ i : Fin (Module.finrank ℂ E), (T.singularValues i) ^ 2 := by
    have h1 : schattenTwoNormSq T
        = ∑ i ∈ Finset.range (Module.finrank ℂ T.range),
            (T.singularValues i) ^ 2 := by
      unfold schattenTwoNormSq Finsupp.sum
      rw [LinearMap.support_singularValues]
    rw [h1, Fin.sum_univ_eq_sum_range
      (fun i => (T.singularValues i) ^ 2) (Module.finrank ℂ E)]
    apply Finset.sum_subset (Finset.range_subset_range.mpr
      (LinearMap.finrank_range_le T))
    intro i _ hi
    have hge : Module.finrank ℂ T.range ≤ i :=
      le_of_not_gt (fun hc => hi (Finset.mem_range.mpr hc))
    have hpos : ¬ 0 < T.singularValues i := by
      rw [LinearMap.singularValues_pos_iff_lt_finrank_range]
      exact not_lt.mpr hge
    have h0 : T.singularValues i = 0 :=
      le_antisymm (le_of_not_gt hpos) (T.singularValues_nonneg i)
    rw [h0]
    simp
  rw [hsum, show (opTrace (LinearMap.adjoint T ∘ₗ T)).re
      = ∑ i, hsymm.eigenvalues rfl i from
        hsymm.re_trace_eq_sum_eigenvalues rfl]
  apply Finset.sum_congr rfl
  intro i _
  exact T.sq_singularValues_fin rfl i

end SchattenFinite

section DiagonalSeat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **diagonal trace norm**: `∑ i, ‖d i‖`, the Schatten-1
norm of the diagonal operator `Matrix.diagonal d` in its own
seat data (its singular values are the `‖d i‖`). -/
noncomputable def diagTraceNorm (d : n → ℂ) : ℝ :=
  ∑ i, ‖d i‖

/-- Trace of a diagonal matrix: `tr (diagonal d) = ∑ i, d i`
(the pin's `Matrix.trace_diagonal`, cited). -/
theorem trace_diagonal_eq_sum (d : n → ℂ) :
    Matrix.trace (Matrix.diagonal d) = ∑ i, d i :=
  Matrix.trace_diagonal d

/-- The diagonal trace norm bounds the trace. -/
theorem norm_trace_diagonal_le (d : n → ℂ) :
    ‖Matrix.trace (Matrix.diagonal d)‖ ≤ diagTraceNorm d := by
  rw [trace_diagonal_eq_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_refl _)

/-- **HS identity at the diagonal seat.**
`tr (Dᴴ * D) = ((∑ i, ‖d i‖ ^ 2 : ℝ) : ℂ)` for
`D = Matrix.diagonal d`. -/
theorem trace_conjTranspose_mul_self_diagonal (d : n → ℂ) :
    Matrix.trace (Matrix.conjTranspose (Matrix.diagonal d)
        * (Matrix.diagonal d))
      = ((∑ i, ‖d i‖ ^ 2 : ℝ) : ℂ) := by
  have hstar : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.ofReal_pow, ← starRingEnd_apply]
    exact RCLike.conj_mul z
  have hprod : Matrix.conjTranspose (Matrix.diagonal d)
        * (Matrix.diagonal d)
      = Matrix.diagonal (fun i => star (d i) * d i) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
  rw [hprod, Matrix.trace_diagonal, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact hstar (d i)

/-- **Positivity at the diagonal seat, equality case.**
Via the HS identity above: the HS trace of a diagonal
matrix vanishes iff every entry does. (The pin's
`Matrix.trace_conjTranspose_mul_self_eq_zero_iff` is stated
for ordered star rings and does not apply over `ℂ`.) -/
theorem trace_conjTranspose_mul_self_diagonal_eq_zero_iff (d : n → ℂ) :
    Matrix.trace (Matrix.conjTranspose (Matrix.diagonal d)
        * (Matrix.diagonal d)) = 0
      ↔ d = 0 := by
  rw [trace_conjTranspose_mul_self_diagonal]
  constructor
  · intro h
    have hsum : (∑ i, ‖d i‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
    funext i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (‖d i‖))).mp hsum i (Finset.mem_univ i)
    have hnorm : ‖d i‖ = 0 := by rwa [sq_eq_zero_iff] at hall
    exact norm_eq_zero.mp hnorm
  · intro h
    rw [h]
    simp

end DiagonalSeat

end ThetLogos
