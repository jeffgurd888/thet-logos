import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Tactic

open Filter Topology ComplexInnerProductSpace
open scoped ENNReal NNReal

namespace ThetLogos

/-!
# Hilbert-Schmidt operators - SHELF-3a-i (the HS core)

General-API stock, built under the SHELF fill commission
(pack: `routeb-general-scratch/pack-shelf-3a.md`). The pin
re-check at dispatch (2026-10-31) re-grepped the vendored
Mathlib v4.35.0-rc3 tree for `HilbertSchmidt`, `Schatten`,
`TraceClass` and `integralKernel`: no Hilbert-Schmidt API
exists in the pin at all (the only "trace class" hit is a
TODO comment; `TraceClass` hits are Lean elaborator trace
classes). This module builds the HS core from scratch, for
arbitrary Hilbert spaces over `ℂ` - no finite-dimensionality,
no seat data (`osSpace`, `sliceMeasure`, `(G, ρ, β, N)`)
anywhere in any statement.

Contents (pack 3a-i): the HS predicate and the HS norm
squared relative to a Hilbert basis (item 1); basis
independence of the HS sum, proved at the `ℝ≥0∞` level by
Parseval in both factors plus Tonelli interchange, then
transported back to `ℝ` (item 2, the mathematical heart);
rank-one and finite-rank operators are HS, with the rank-one
sum computed (item 3); HS implies compact, via finite-rank
truncations along a Hilbert basis, the general
finite-dimensional-range compactness lemma, and the pin's
`isCompactOperator_of_tendsto` (item 4); the operator-norm
bound `‖T‖ ≤ sqrt (HS norm squared)` and closure basics
(item 5, as far as reached - see the module report).

This is the first half of the F2 fence's prerequisite stock:
it does NOT retire the F2 fence (that is SHELF-3b's, gated on
this brick plus the upstream `reflSite` duplicate), and the
kernel-operator half (pack 3a-ii, module
`IntegralKernelHS.lean`) is a separate brick.

NO CLAIM; dials 0/4. General-API stock only.
-/

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## Item 1 - the definition -/

/-- The Hilbert-Schmidt norm squared of `T` relative to a
Hilbert basis `b` of the domain: the real `tsum` of the
squared norms of the images of the basis vectors. -/
noncomputable def hilbertSchmidtNormSq {ι : Type*} (T : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) : ℝ :=
  ∑' i, ‖T (b i)‖ ^ 2

/-- `T` is Hilbert-Schmidt if the squared norms of its values
on some Hilbert basis of the domain are summable. (Basis
independence, `IsHilbertSchmidt.summable_norm_sq_of_basis`
below, upgrades "some" to "every".) -/
def IsHilbertSchmidt (T : E →L[ℂ] F) : Prop :=
  ∃ (ι : Type u) (b : HilbertBasis ι ℂ E), Summable (fun i => ‖T (b i)‖ ^ 2)

/-! ## Parseval preliminaries (the Q12 §4a tools, abstracted) -/

/-- Summability of the squared Fourier coefficients of a vector
in a Hilbert basis. -/
theorem hsSummable_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ E) (v : E) :
    Summable (fun i => ‖⟪b i, v⟫‖ ^ 2) := by
  have hfam : ∀ i, ⟪v, b i⟫ * ⟪b i, v⟫
      = ((‖⟪b i, v⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm]
    exact_mod_cast RCLike.conj_mul (⟪b i, v⟫ : ℂ)
  have hH : HasSum (fun i => ((‖⟪b i, v⟫‖ ^ 2 : ℝ) : ℂ)) ⟪v, v⟫ := by
    simpa only [hfam] using b.hasSum_inner_mul_inner v v
  exact Complex.summable_ofReal.mp hH.summable

/-- Parseval's identity for a Hilbert basis, as a real `tsum`. -/
theorem hsParseval_tsum {ι : Type*} (b : HilbertBasis ι ℂ E) (v : E) :
    ∑' i, ‖⟪b i, v⟫‖ ^ 2 = ‖v‖ ^ 2 := by
  have hfam : ∀ i, ⟪v, b i⟫ * ⟪b i, v⟫
      = ((‖⟪b i, v⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm]
    exact_mod_cast RCLike.conj_mul (⟪b i, v⟫ : ℂ)
  have hH : HasSum (fun i => ((‖⟪b i, v⟫‖ ^ 2 : ℝ) : ℂ)) ⟪v, v⟫ := by
    simpa only [hfam] using b.hasSum_inner_mul_inner v v
  have key : ((∑' i, ‖⟪b i, v⟫‖ ^ 2 : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    have h2 : ((∑' i, ‖⟪b i, v⟫‖ ^ 2 : ℝ) : ℂ) = ⟪v, v⟫ := by
      rw [Complex.ofReal_tsum]
      exact hH.tsum_eq
    rw [h2]
    exact_mod_cast inner_self_eq_norm_sq_to_K v
  exact_mod_cast key

/-- The Fourier coefficients of `T` against a codomain basis and
of the adjoint against a domain basis have the same norms. -/
theorem hs_norm_inner_adjoint {ι κ : Type*} (T : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) (i : ι) (k : κ) :
    ‖⟪b i, (ContinuousLinearMap.adjoint T) (d k)⟫‖ = ‖⟪d k, T (b i)⟫‖ := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← RCLike.norm_conj ⟪d k, T (b i)⟫, inner_conj_symm]

/-! ## Item 2 - basis independence, at the `ℝ≥0∞` level first

The HS total of `T` over a domain basis and the HS total of the
adjoint `T†` over a codomain basis both equal the same double
sum of squared Fourier coefficients (Parseval in the other
factor + `ENNReal.tsum_comm`). In `ℝ≥0∞` no summability
hypothesis is needed, so the equality is unconditional; the
real statement is transported back afterwards. -/

/-- Parseval in the codomain, at the `ℝ≥0∞` level: the HS total
of `T` over `b` is the double sum over `b` and a codomain
basis `d`. -/
theorem hs_ofReal_tsum_eq_double (T : E →L[ℂ] F) {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) :
    ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' i, ∑' k, ENNReal.ofReal (‖⟪d k, T (b i)⟫‖ ^ 2) := by
  apply tsum_congr
  intro i
  rw [← hsParseval_tsum d (T (b i))]
  exact ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _)
    (hsSummable_inner_sq d (T (b i)))

/-- The same double sum, read from the adjoint side. -/
theorem hs_ofReal_tsum_adjoint_eq_double (T : E →L[ℂ] F) {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) :
    ∑' k, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint T) (d k)‖ ^ 2)
      = ∑' i, ∑' k, ENNReal.ofReal (‖⟪d k, T (b i)⟫‖ ^ 2) := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro k
  rw [← hsParseval_tsum b ((ContinuousLinearMap.adjoint T) (d k))]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (hsSummable_inner_sq b ((ContinuousLinearMap.adjoint T) (d k)))]
  apply tsum_congr
  intro i
  rw [hs_norm_inner_adjoint T b d i k]

/-- **Basis independence at the `ℝ≥0∞` level** (unconditional):
the HS totals of `T` over any two Hilbert bases of the domain
are equal in `ℝ≥0∞` - both equal the HS total of the adjoint
over a codomain basis. -/
theorem hs_ofReal_tsum_basis_indep (T : E →L[ℂ] F) {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖T (c j)‖ ^ 2) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis ℂ F
  rw [hs_ofReal_tsum_eq_double T b d, ← hs_ofReal_tsum_adjoint_eq_double T b d,
    hs_ofReal_tsum_eq_double T c d, ← hs_ofReal_tsum_adjoint_eq_double T c d]

/-- Summability transport: if the squared norms over one basis
are summable and the `ℝ≥0∞` totals agree, the squared norms
over the other basis are summable. -/
theorem hs_summable_of_ofReal_tsum_eq {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) (hsum : Summable f)
    (heq : ∑' i, ENNReal.ofReal (f i) = ∑' j, ENNReal.ofReal (g j)) :
    Summable g := by
  have hne : ∑' j, ENNReal.ofReal (g j) ≠ ⊤ := by
    rw [← heq]
    exact hsum.tsum_ofReal_ne_top
  refine (ENNReal.summable_toReal hne).congr (fun j => ?_)
  rw [ENNReal.toReal_ofReal]
  exact hg j

/-- **Basis independence (real form).** If `T` is HS relative
to one Hilbert basis, it is HS relative to every Hilbert
basis. -/
theorem IsHilbertSchmidt.summable_norm_sq {ι : Type*} {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ι ℂ E) :
    Summable (fun i => ‖T (b i)‖ ^ 2) := by
  obtain ⟨ι₀, b₀, h₀⟩ := hT
  exact hs_summable_of_ofReal_tsum_eq (fun i => sq_nonneg _) (fun i => sq_nonneg _)
    h₀ (hs_ofReal_tsum_basis_indep T b₀ b)

/-- **Basis independence (equality of sums).** The HS norm
squared does not depend on the Hilbert basis. -/
theorem hilbertSchmidtNormSq_eq {ι κ : Type*} {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    hilbertSchmidtNormSq T b = hilbertSchmidtNormSq T c := by
  have hb : Summable (fun i => ‖T (b i)‖ ^ 2) := hT.summable_norm_sq b
  have hc : Summable (fun i => ‖T (c i)‖ ^ 2) := hT.summable_norm_sq c
  have hEq : ENNReal.ofReal (hilbertSchmidtNormSq T b)
      = ENNReal.ofReal (hilbertSchmidtNormSq T c) := by
    unfold hilbertSchmidtNormSq
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hb,
      ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hc]
    exact hs_ofReal_tsum_basis_indep T b c
  have h2 := congrArg ENNReal.toReal hEq
  unfold hilbertSchmidtNormSq at h2
  rwa [ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _)),
    ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _))] at h2

/-- Membership form: relative to a named basis, `T` is HS iff
the squared-norm family over that basis is summable. -/
theorem isHilbertSchmidt_iff {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E) :
    IsHilbertSchmidt T ↔ Summable (fun i => ‖T (b i)‖ ^ 2) := by
  constructor
  · intro hT
    exact hT.summable_norm_sq b
  · intro h
    obtain ⟨w, d, -⟩ := exists_hilbertBasis ℂ E
    exact ⟨↥w, d, hs_summable_of_ofReal_tsum_eq (fun i => sq_nonneg _)
      (fun i => sq_nonneg _) h (hs_ofReal_tsum_basis_indep T b d)⟩

/-! ## Item 5 (first piece) - the adjoint

The adjoint of an HS operator is HS: at the `ℝ≥0∞` level this
is the same double sum (`hs_ofReal_tsum_adjoint_eq_double`). -/

/-- The adjoint of a Hilbert-Schmidt operator is
Hilbert-Schmidt. -/
theorem IsHilbertSchmidt.adjoint {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) := by
  obtain ⟨ι₀, b₀, h₀⟩ := hT
  obtain ⟨w, d, -⟩ := exists_hilbertBasis ℂ F
  refine ⟨↥w, d, ?_⟩
  exact hs_summable_of_ofReal_tsum_eq (fun i => sq_nonneg _) (fun i => sq_nonneg _)
    h₀ ((hs_ofReal_tsum_eq_double T b₀ d).trans
      (hs_ofReal_tsum_adjoint_eq_double T b₀ d).symm)

/-- The HS norm squared of the adjoint (over a codomain basis)
equals the HS norm squared of `T` (over a domain basis). -/
theorem hilbertSchmidtNormSq_adjoint {ι κ : Type*} {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) :
    hilbertSchmidtNormSq (ContinuousLinearMap.adjoint T) d
      = hilbertSchmidtNormSq T b := by
  have hb : Summable (fun i => ‖T (b i)‖ ^ 2) := hT.summable_norm_sq b
  have hd : Summable (fun k => ‖(ContinuousLinearMap.adjoint T) (d k)‖ ^ 2) :=
    hT.adjoint.summable_norm_sq d
  have hEq : ENNReal.ofReal (hilbertSchmidtNormSq (ContinuousLinearMap.adjoint T) d)
      = ENNReal.ofReal (hilbertSchmidtNormSq T b) := by
    unfold hilbertSchmidtNormSq
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hd,
      ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hb,
      hs_ofReal_tsum_adjoint_eq_double T b d, hs_ofReal_tsum_eq_double T b d]
  have h2 := congrArg ENNReal.toReal hEq
  unfold hilbertSchmidtNormSq at h2
  rwa [ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _)),
    ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _))] at h2

/-! ## Item 3 - rank-one and finite-rank operators are HS -/

/-- The HS norm squared of a rank-one operator, computed:
`‖x‖^2 * ‖y‖^2`, for every Hilbert basis of the domain. -/
theorem hilbertSchmidtNormSq_rankOne {ι : Type*} (x : F) (y : E)
    (b : HilbertBasis ι ℂ E) :
    hilbertSchmidtNormSq (InnerProductSpace.rankOne ℂ x y) b
      = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hnorm : ∀ i, ‖⟪y, b i⟫‖ = ‖⟪b i, y⟫‖ := fun i => by
    rw [← RCLike.norm_conj ⟪b i, y⟫, inner_conj_symm]
  unfold hilbertSchmidtNormSq
  have h1 : (fun i => ‖(InnerProductSpace.rankOne ℂ x y) (b i)‖ ^ 2)
      = (fun i => ‖⟪b i, y⟫‖ ^ 2 * ‖x‖ ^ 2) := by
    funext i
    rw [InnerProductSpace.rankOne_apply, norm_smul, hnorm i, mul_pow]
  rw [h1, tsum_mul_right, hsParseval_tsum b y, mul_comm]

/-- A rank-one operator is Hilbert-Schmidt. -/
theorem isHilbertSchmidt_rankOne (x : F) (y : E) :
    IsHilbertSchmidt (InnerProductSpace.rankOne ℂ x y) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  refine (isHilbertSchmidt_iff _ b).mpr ?_
  have hnorm : ∀ i, ‖⟪y, b i⟫‖ = ‖⟪b i, y⟫‖ := fun i => by
    rw [← RCLike.norm_conj ⟪b i, y⟫, inner_conj_symm]
  have h1 : (fun i => ‖(InnerProductSpace.rankOne ℂ x y) (b i)‖ ^ 2)
      = (fun i => ‖⟪b i, y⟫‖ ^ 2 * ‖x‖ ^ 2) := by
    funext i
    rw [InnerProductSpace.rankOne_apply, norm_smul, hnorm i, mul_pow]
  rw [h1]
  exact (hsSummable_inner_sq b y).mul_right _

/-- The zero operator is Hilbert-Schmidt. -/
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : E →L[ℂ] F) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  refine (isHilbertSchmidt_iff _ b).mpr ?_
  simp

/-- HS operators are closed under addition. -/
theorem IsHilbertSchmidt.add {S T : E →L[ℂ] F}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  refine (isHilbertSchmidt_iff _ b).mpr ?_
  have hSb := hS.summable_norm_sq b
  have hTb := hT.summable_norm_sq b
  have hbound : ∀ i, ‖(S + T) (b i)‖ ^ 2
      ≤ 2 * ‖S (b i)‖ ^ 2 + 2 * ‖T (b i)‖ ^ 2 := by
    intro i
    rw [add_apply]
    have h1 : ‖S (b i) + T (b i)‖ ≤ ‖S (b i)‖ + ‖T (b i)‖ := norm_add_le _ _
    nlinarith [mul_le_mul h1 h1 (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      sq_nonneg (‖S (b i)‖ - ‖T (b i)‖), norm_nonneg (S (b i)),
      norm_nonneg (T (b i))]
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) hbound ?_
  exact (hSb.mul_left 2).add (hTb.mul_left 2)

/-- HS operators are closed under scalar multiplication. -/
theorem IsHilbertSchmidt.smul {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) (c : ℂ) :
    IsHilbertSchmidt (c • T) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  refine (isHilbertSchmidt_iff _ b).mpr ?_
  have h1 : (fun i => ‖(c • T) (b i)‖ ^ 2)
      = (fun i => ‖c‖ ^ 2 * ‖T (b i)‖ ^ 2) := by
    funext i
    rw [smul_apply, norm_smul, mul_pow]
  rw [h1]
  exact (hT.summable_norm_sq b).mul_left _

/-- A finite sum of rank-one operators is Hilbert-Schmidt. -/
theorem isHilbertSchmidt_sum_rankOne {ι : Type*} (s : Finset ι)
    (x : ι → F) (y : ι → E) :
    IsHilbertSchmidt (∑ i ∈ s, InnerProductSpace.rankOne ℂ (x i) (y i)) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isHilbertSchmidt_zero (E := E) (F := F)
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      exact (isHilbertSchmidt_rankOne (x a) (y a)).add ih

/-! ## Item 4 - HS implies compact

First the general pin-missing lemma (Q12's seat proof was the
method template; this is the general statement): an operator
whose range lies in a finite-dimensional subspace is compact. -/

section FiniteRange

variable {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- A continuous linear operator whose range lies in a
finite-dimensional subspace is compact: the closure of the
image of the unit ball is a closed bounded subset of that
subspace, hence compact (Heine-Borel in the subspace). -/
theorem hs_isCompactOperator_of_range_le_finiteDimensional
    (T : E' →L[ℂ] F') (M : Submodule ℂ F') (hM : FiniteDimensional ℂ M)
    (hle : LinearMap.range T.toLinearMap ≤ M) :
    IsCompactOperator ⇑T := by
  classical
  haveI := hM
  have hsubM : closure (⇑T '' Metric.ball 0 1) ⊆ (M : Set F') := by
    apply closure_minimal _ M.closed_of_finiteDimensional
    intro y hy
    obtain ⟨x, -, rfl⟩ := hy
    exact hle (LinearMap.mem_range_self T.toLinearMap x)
  have hsubB : closure (⇑T '' Metric.ball 0 1) ⊆ Metric.closedBall 0 ‖T‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ ‖T‖ := by
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        rw [Metric.mem_ball, dist_zero_right] at hx
        exact hx.le
  set A' : Set M := Subtype.val ⁻¹' closure (⇑T '' Metric.ball 0 1) with hA'
  have hA'closed : IsClosed A' := isClosed_closure.preimage continuous_subtype_val
  have hA'bdd : Bornology.IsBounded A' := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * ‖T‖, fun x hx y hy => ?_⟩
    have hx2 : ‖(x : F')‖ ≤ ‖T‖ := by
      have h := hsubB hx
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hy2 : ‖(y : F')‖ ≤ ‖T‖ := by
      have h := hsubB hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    calc dist x y = dist (x : F') (y : F') := Subtype.dist_eq x y
      _ = ‖(x : F') - (y : F')‖ := dist_eq_norm _ _
      _ ≤ ‖(x : F')‖ + ‖(y : F')‖ := norm_sub_le _ _
      _ ≤ 2 * ‖T‖ := by linarith
  haveI : ProperSpace M := FiniteDimensional.proper ℂ M
  have hA'comp : IsCompact A' :=
    Metric.isCompact_of_isClosed_isBounded hA'closed hA'bdd
  have hAeq : Subtype.val '' A' = closure (⇑T '' Metric.ball 0 1) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      exact ⟨⟨y, hsubM hy⟩, hy, rfl⟩
  have hcomp : IsCompact (closure (⇑T '' Metric.ball 0 1)) := by
    rw [← hAeq]
    exact hA'comp.image continuous_subtype_val
  refine ⟨closure (⇑T '' Metric.ball 0 1), hcomp, ?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
    (fun x hx => subset_closure ⟨x, hx, rfl⟩)

end FiniteRange

/-! ### Basis projections and the HS tail -/

/-- The finite basis projection: partial sum of the Fourier
expansion at the finite set `F`, as a continuous linear map. -/
noncomputable def hsProjSum {ι : Type*} (b : HilbertBasis ι ℂ E) (F : Finset ι) :
    E →L[ℂ] E :=
  ∑ i ∈ F, (innerSL ℂ (b i)).smulRight (b i)

theorem hsProjSum_apply {ι : Type*} (b : HilbertBasis ι ℂ E) (F : Finset ι) (x : E) :
    hsProjSum b F x = ∑ i ∈ F, ⟪b i, x⟫ • (b i) := by
  show (∑ i ∈ F, (innerSL ℂ (b i)).smulRight (b i)) x = _
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- The Fourier coefficients of the residual `x - hsProjSum F x`
vanish at indices in `F`. -/
theorem hs_inner_projSum_residual_of_mem {ι : Type*} (b : HilbertBasis ι ℂ E)
    (F : Finset ι) (x : E) {i : ι} (hi : i ∈ F) :
    ⟪b i, x - hsProjSum b F x⟫ = 0 := by
  classical
  have hterm : ∀ j ∈ F, ⟪b i, ⟪b j, x⟫ • (b j)⟫
      = if j = i then ⟪b j, x⟫ else 0 := by
    intro j _
    rw [inner_smul_right, (orthonormal_iff_ite.mp b.orthonormal) i j]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (fun hj : j = i => h hj.symm)]
      simp
  rw [inner_sub_right, hsProjSum_apply, inner_sum,
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hi]
  exact sub_self _

/-- The Fourier coefficients of the residual `x - hsProjSum F x`
agree with those of `x` at indices outside `F`. -/
theorem hs_inner_projSum_residual_of_not_mem {ι : Type*} (b : HilbertBasis ι ℂ E)
    (F : Finset ι) (x : E) {i : ι} (hi : i ∉ F) :
    ⟪b i, x - hsProjSum b F x⟫ = ⟪b i, x⟫ := by
  classical
  have hterm : ∀ j ∈ F, ⟪b i, ⟪b j, x⟫ • (b j)⟫
      = if j = i then ⟪b j, x⟫ else 0 := by
    intro j _
    rw [inner_smul_right, (orthonormal_iff_ite.mp b.orthonormal) i j]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (fun hj : j = i => h hj.symm)]
      simp
  rw [inner_sub_right, hsProjSum_apply, inner_sum,
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_neg hi]
  exact sub_zero _

/-- The tail of the HS sum outside a finite set `F`: the `tsum`
of `‖T (b i)‖^2` over the complement subtype. -/
noncomputable def hsTailSq {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (F : Finset ι) : ℝ :=
  ∑' i : ↥(F : Set ι)ᶜ, ‖T (b i)‖ ^ 2

/-- The tail family is summable. -/
theorem hs_summable_tail {ι : Type*} {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ E) (F : Finset ι) :
    Summable (fun i : ↥(F : Set ι)ᶜ => ‖T (b i)‖ ^ 2) := by
  simpa only [Function.comp_def] using
    (hT.summable_norm_sq b).comp_injective
      (i := fun i : ↥(F : Set ι)ᶜ => (i : ι)) Subtype.coe_injective

/-- Finite partial sums of the HS family over a finset `A`
disjoint from `F` are bounded by the tail outside `F`. -/
theorem hs_sum_le_tail {ι : Type*} {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ E) (F A : Finset ι) (hA : ∀ i ∈ A, i ∉ F) :
    ∑ i ∈ A, ‖T (b i)‖ ^ 2 ≤ hsTailSq T b F := by
  classical
  let s' : Finset ↥(F : Set ι)ᶜ := A.subtype (fun i => i ∉ F)
  have hsum : (∑ i ∈ A, ‖T (b i)‖ ^ 2)
      = ∑ x ∈ s', ‖T (b x)‖ ^ 2 := by
    show (∑ i ∈ A, ‖T (b i)‖ ^ 2)
      = ∑ x ∈ A.subtype (fun i => i ∉ F), ‖T (b x)‖ ^ 2
    rw [Finset.sum_subtype_eq_sum_filter (fun i => ‖T (b i)‖ ^ 2)]
    congr 1
    exact (Finset.filter_true_of_mem hA).symm
  rw [hsum]
  show (∑ x ∈ s', ‖T (b x)‖ ^ 2) ≤ ∑' i : ↥(F : Set ι)ᶜ, ‖T (b i)‖ ^ 2
  exact Summable.sum_le_tsum s' (fun x _ => sq_nonneg _) (hs_summable_tail hT b F)

/-- The HS tail vanishes along the finite sets. -/
theorem hs_tailSq_tendsto_zero {ι : Type*} {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ E) :
    Filter.Tendsto (hsTailSq T b) Filter.atTop (nhds 0) := by
  have hTot : (∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)) ≠ ⊤ :=
    (hT.summable_norm_sq b).tsum_ofReal_ne_top
  have hfin : ∀ F : Finset ι,
      (∑' i : {x // x ∉ F}, ENNReal.ofReal (‖T (b (i : ι))‖ ^ 2)) ≠ ⊤ := by
    intro F
    apply ne_top_of_le_ne_top hTot
    rw [← ENNReal.sum_add_tsum_compl F (fun i => ENNReal.ofReal (‖T (b i)‖ ^ 2))]
    exact le_add_self
  have hEq : ∀ F : Finset ι, hsTailSq T b F
      = (∑' i : {x // x ∉ F}, ENNReal.ofReal (‖T (b (i : ι))‖ ^ 2)).toReal := by
    intro F
    unfold hsTailSq
    show (∑' i : {x // x ∉ F}, ‖T (b (i : ι))‖ ^ 2)
      = (∑' i : {x // x ∉ F}, ENNReal.ofReal (‖T (b (i : ι))‖ ^ 2)).toReal
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
    apply tsum_congr
    intro i
    exact (ENNReal.toReal_ofReal (sq_nonneg _)).symm
  have h2 : Filter.Tendsto (fun F : Finset ι =>
      (∑' i : {x // x ∉ F}, ENNReal.ofReal (‖T (b (i : ι))‖ ^ 2)).toReal)
      Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff hfin).mpr
      (ENNReal.tendsto_tsum_compl_atTop_zero hTot)
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun F => (hEq F).symm) h2

/-! ### Finite-rank truncations and the approximation bound -/

/-- Finite Cauchy-Schwarz bound for a partial Fourier sum:
if the HS partial sum over `A` is at most `C`, the partial sum
applied to `x` has norm at most `sqrt C * ‖x‖` (Bessel on the
coefficient side). -/
theorem hs_norm_partialSum_le {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (x : E) (A : Finset ι) (C : ℝ) (hC : ∑ i ∈ A, ‖T (b i)‖ ^ 2 ≤ C) :
    ‖∑ i ∈ A, ⟪b i, x⟫ • T (b i)‖ ≤ Real.sqrt C * ‖x‖ := by
  have hnormsum : ‖∑ i ∈ A, ⟪b i, x⟫ • T (b i)‖
      ≤ ∑ i ∈ A, ‖⟪b i, x⟫‖ * ‖T (b i)‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq A
    (fun i => ‖⟪b i, x⟫‖) (fun i => ‖T (b i)‖)
  have hP : (∑ i ∈ A, ‖⟪b i, x⟫‖ ^ 2) ≤ ‖x‖ ^ 2 := by
    have h := Summable.sum_le_tsum A (fun i _ => sq_nonneg _)
      (hsSummable_inner_sq b x)
    rwa [hsParseval_tsum b x] at h
  have hnn : 0 ≤ ∑ i ∈ A, ‖⟪b i, x⟫‖ * ‖T (b i)‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsqrtP : Real.sqrt (∑ i ∈ A, ‖⟪b i, x⟫‖ ^ 2) ≤ ‖x‖ := by
    rw [← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hP
  calc ‖∑ i ∈ A, ⟪b i, x⟫ • T (b i)‖
      ≤ ∑ i ∈ A, ‖⟪b i, x⟫‖ * ‖T (b i)‖ := hnormsum
    _ = Real.sqrt ((∑ i ∈ A, ‖⟪b i, x⟫‖ * ‖T (b i)‖) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((∑ i ∈ A, ‖⟪b i, x⟫‖ ^ 2)
          * (∑ i ∈ A, ‖T (b i)‖ ^ 2)) := Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (∑ i ∈ A, ‖⟪b i, x⟫‖ ^ 2)
          * Real.sqrt (∑ i ∈ A, ‖T (b i)‖ ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _)) _
    _ ≤ ‖x‖ * Real.sqrt C :=
        mul_le_mul hsqrtP (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)
          (norm_nonneg _)
    _ = Real.sqrt C * ‖x‖ := mul_comm _ _

/-- The finite-rank truncation of `T` along the basis `b` at
the finite set `F`: the partial sum of rank-one operators
`rankOne ℂ (T (b i)) (b i)`. -/
noncomputable def hsApprox {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (s : Finset ι) : E →L[ℂ] F :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (T (b i)) (b i)

theorem hsApprox_apply {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (F : Finset ι) (x : E) :
    hsApprox T b F x = ∑ i ∈ F, ⟪b i, x⟫ • T (b i) := by
  show (∑ i ∈ F, InnerProductSpace.rankOne ℂ (T (b i)) (b i)) x = _
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [InnerProductSpace.rankOne_apply]

/-- The range of the truncation lies in the span of the
finitely many vectors `T (b i)`, `i ∈ F`. -/
theorem hsApprox_range_le {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (F : Finset ι) :
    LinearMap.range (hsApprox T b F).toLinearMap
      ≤ Submodule.span ℂ ((fun i => T (b i)) '' (F : Set ι)) := by
  rintro y ⟨x, rfl⟩
  have h1 : hsApprox T b F x = ∑ i ∈ F, ⟪b i, x⟫ • T (b i) :=
    hsApprox_apply T b F x
  show (hsApprox T b F) x ∈ Submodule.span ℂ ((fun i => T (b i)) '' (F : Set ι))
  rw [h1]
  apply sum_mem
  intro i hi
  exact Submodule.smul_mem _ _
    (Submodule.subset_span
      (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hi)))

/-- Each truncation is compact (finite-dimensional range). -/
theorem hsApprox_isCompact {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (F : Finset ι) :
    IsCompactOperator ⇑(hsApprox T b F) :=
  hs_isCompactOperator_of_range_le_finiteDimensional _
    (Submodule.span ℂ ((fun i => T (b i)) '' (F : Set ι)))
    (FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet F).image _))
    (hsApprox_range_le T b F)

/-- Partial Fourier sums of `T x` along `b` converge to `T x`. -/
theorem hs_hasSum_apply {ι : Type*} (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E)
    (x : E) :
    HasSum (fun i => ⟪b i, x⟫ • T (b i)) (T x) := by
  have hfun : (fun i => T (b.repr x i • b i))
      = (fun i => ⟪b i, x⟫ • T (b i)) := by
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply]
  have h := (b.hasSum_repr x).mapL T
  rwa [hfun] at h

/-- The approximation error, pointwise in the input:
`‖T x - hsApprox F x‖ ≤ sqrt (tailSq F) * ‖x‖`. -/
theorem hs_approx_bound {ι : Type*} {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ E) (F : Finset ι) (x : E) :
    ‖T x - hsApprox T b F x‖ ≤ Real.sqrt (hsTailSq T b F) * ‖x‖ := by
  classical
  set y := x - hsProjSum b F x with hy
  have hdiff : T x - hsApprox T b F x = T y := by
    have h1 : T (hsProjSum b F x) = hsApprox T b F x := by
      rw [hsApprox_apply, hsProjSum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    show T x - hsApprox T b F x = T (x - hsProjSum b F x)
    rw [← h1, ← map_sub]
  rw [hdiff]
  have htend : Filter.Tendsto
      (fun A : Finset ι => ∑ i ∈ A, ⟪b i, y⟫ • T (b i))
      Filter.atTop (nhds (T y)) := hs_hasSum_apply T b y
  have hbound : ∀ A : Finset ι,
      ‖∑ i ∈ A, ⟪b i, y⟫ • T (b i)‖ ≤ Real.sqrt (hsTailSq T b F) * ‖x‖ := by
    intro A
    have hA1 : (∑ i ∈ A, ⟪b i, y⟫ • T (b i))
        = ∑ i ∈ A \ F, ⟪b i, y⟫ • T (b i) := by
      symm
      apply Finset.sum_subset Finset.sdiff_subset
      intro i hiA hiAF
      have hiF : i ∈ F := by
        by_contra hniF
        exact hiAF (Finset.mem_sdiff.mpr ⟨hiA, hniF⟩)
      rw [hs_inner_projSum_residual_of_mem b F x hiF, zero_smul]
    have hA2 : (∑ i ∈ A \ F, ⟪b i, y⟫ • T (b i))
        = ∑ i ∈ A \ F, ⟪b i, x⟫ • T (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_sdiff] at hi
      rw [hs_inner_projSum_residual_of_not_mem b F x hi.2]
    rw [hA1, hA2]
    exact hs_norm_partialSum_le T b x (A \ F) (hsTailSq T b F)
      (hs_sum_le_tail hT b F (A \ F) (fun i hi => (Finset.mem_sdiff.mp hi).2))
  have hnorm : Filter.Tendsto
      (fun A : Finset ι => ‖∑ i ∈ A, ⟪b i, y⟫ • T (b i)‖)
      Filter.atTop (nhds ‖T y‖) :=
    (continuous_norm.tendsto _).comp htend
  exact le_of_tendsto hnorm (Filter.Eventually.of_forall hbound)

/-- The finite-rank truncations converge to `T` in operator
norm, since the HS tail vanishes along the finite sets. -/
theorem hs_tendsto_approx {ι : Type*} {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (b : HilbertBasis ι ℂ E) :
    Filter.Tendsto (fun F : Finset ι => hsApprox T b F)
      Filter.atTop (nhds T) := by
  have hnormbound : ∀ F : Finset ι,
      ‖hsApprox T b F - T‖ ≤ Real.sqrt (hsTailSq T b F) := by
    intro F
    have h := ContinuousLinearMap.opNorm_le_bound (T - hsApprox T b F)
      (Real.sqrt_nonneg _) (fun x => by
        rw [ContinuousLinearMap.sub_apply]
        exact hs_approx_bound hT b F x)
    rwa [norm_sub_rev] at h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun F => Real.sqrt (hsTailSq T b F))
    (fun F => dist_nonneg) (fun F => ?_) ?_
  · rw [dist_eq_norm]
    exact hnormbound F
  · have h := (Real.continuous_sqrt.tendsto 0).comp
      (hs_tailSq_tendsto_zero hT b)
    simpa only [Real.sqrt_zero, Function.comp_def] using h

/-- **HS implies compact.** A Hilbert-Schmidt operator is the
operator-norm limit of its finite-rank basis truncations,
each of which is compact; conclude via the pin's
`isCompactOperator_of_tendsto`. -/
theorem IsHilbertSchmidt.isCompactOperator {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) :
    IsCompactOperator ⇑T := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  apply isCompactOperator_of_tendsto
    (F := fun F : Finset ↥w => hsApprox T b F) (f := T)
    (hs_tendsto_approx hT b)
  apply Filter.Eventually.of_forall
  intro F
  exact hsApprox_isCompact T b F

/-! ## Item 5 (second piece) - operator-norm bound and ideal -/

/-- The operator norm is at most the HS norm:
`‖T‖ ≤ sqrt (hilbertSchmidtNormSq T b)` for every basis `b`. -/
theorem IsHilbertSchmidt.opNorm_le {ι : Type*} {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ι ℂ E) :
    ‖T‖ ≤ Real.sqrt (hilbertSchmidtNormSq T b) := by
  refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) (fun x => ?_)
  have htend : Filter.Tendsto
      (fun A : Finset ι => ∑ i ∈ A, ⟪b i, x⟫ • T (b i))
      Filter.atTop (nhds (T x)) := hs_hasSum_apply T b x
  have hbound : ∀ A : Finset ι,
      ‖∑ i ∈ A, ⟪b i, x⟫ • T (b i)‖
        ≤ Real.sqrt (hilbertSchmidtNormSq T b) * ‖x‖ := by
    intro A
    refine hs_norm_partialSum_le T b x A (hilbertSchmidtNormSq T b) ?_
    exact Summable.sum_le_tsum A (fun i _ => sq_nonneg _) (hT.summable_norm_sq b)
  have hnorm : Filter.Tendsto
      (fun A : Finset ι => ‖∑ i ∈ A, ⟪b i, x⟫ • T (b i)‖)
      Filter.atTop (nhds ‖T x‖) :=
    (continuous_norm.tendsto _).comp htend
  exact le_of_tendsto hnorm (Filter.Eventually.of_forall hbound)

/-- Termwise bound for left composition: composing an HS
operator with a bounded operator on the left stays HS, with
the product bound on the squared HS norms. -/
theorem hs_norm_sq_comp_apply_le {ι : Type*} {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {T : E →L[ℂ] F} (S : F →L[ℂ] G)
    (b : HilbertBasis ι ℂ E) (i : ι) :
    ‖(S ∘L T) (b i)‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖T (b i)‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply]
  have h := S.le_opNorm (T (b i))
  have h2 : ‖S (T (b i))‖ ^ 2 ≤ (‖S‖ * ‖T (b i)‖) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul h h (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rwa [mul_pow] at h2

/-- Left ideal property: `S ∘L T` is HS when `T` is. -/
theorem IsHilbertSchmidt.comp_left {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (S : F →L[ℂ] G) :
    IsHilbertSchmidt (S ∘L T) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  refine (isHilbertSchmidt_iff _ b).mpr ?_
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _)
    (fun i => hs_norm_sq_comp_apply_le S b i) ?_
  exact (hT.summable_norm_sq b).mul_left _

/-- The product bound for left composition. -/
theorem hilbertSchmidtNormSq_comp_left_le {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {ι : Type*} {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (S : F →L[ℂ] G) (b : HilbertBasis ι ℂ E) :
    hilbertSchmidtNormSq (S ∘L T) b ≤ ‖S‖ ^ 2 * hilbertSchmidtNormSq T b := by
  unfold hilbertSchmidtNormSq
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => hs_norm_sq_comp_apply_le S b i)
    (hT.comp_left S |>.summable_norm_sq b) ((hT.summable_norm_sq b).mul_left _)

/-- Right ideal property: `T ∘L S` is HS when `T` is (via the
adjoint and the left ideal property). -/
theorem IsHilbertSchmidt.comp_right {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (S : G →L[ℂ] E) :
    IsHilbertSchmidt (T ∘L S) := by
  have h := (hT.adjoint.comp_left (ContinuousLinearMap.adjoint S))
  have h2 := h.adjoint
  rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_adjoint] at h2

/-- The product bound for right composition. -/
theorem hilbertSchmidtNormSq_comp_right_le {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {ι κ : Type*} {T : E →L[ℂ] F}
    (hT : IsHilbertSchmidt T) (S : G →L[ℂ] E) (b : HilbertBasis ι ℂ G)
    (c : HilbertBasis κ ℂ E) :
    hilbertSchmidtNormSq (T ∘L S) b ≤ ‖S‖ ^ 2 * hilbertSchmidtNormSq T c := by
  have hTS : IsHilbertSchmidt (T ∘L S) := hT.comp_right S
  obtain ⟨w, d, -⟩ := exists_hilbertBasis ℂ F
  calc hilbertSchmidtNormSq (T ∘L S) b
      = hilbertSchmidtNormSq (ContinuousLinearMap.adjoint (T ∘L S)) d :=
        (hilbertSchmidtNormSq_adjoint hTS b d).symm
    _ = hilbertSchmidtNormSq
          ((ContinuousLinearMap.adjoint S) ∘L (ContinuousLinearMap.adjoint T)) d := by
        rw [ContinuousLinearMap.adjoint_comp]
    _ ≤ ‖ContinuousLinearMap.adjoint S‖ ^ 2
          * hilbertSchmidtNormSq (ContinuousLinearMap.adjoint T) d :=
        hilbertSchmidtNormSq_comp_left_le hT.adjoint _ d
    _ = ‖S‖ ^ 2 * hilbertSchmidtNormSq T c := by
        have hnormS : ‖ContinuousLinearMap.adjoint S‖ = ‖S‖ :=
          LinearIsometryEquiv.norm_map _ _
        rw [hnormS, hilbertSchmidtNormSq_adjoint hT c d]

end ThetLogos
