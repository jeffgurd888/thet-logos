import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import ThetLogos.FlowKernel

open Matrix Finset
open scoped Kronecker

namespace ThetLogos

/-!
# Decoherence toy: partial trace + dephasing channel (T1, TOY)

Scoped by the parked-fleet gauntlet
(`whitepaper/gauntlet-parked-fleet-2026-10-17.md` §9), re-deriving the
Schrödinger gauntlet §4c. Two pieces, both priced S:

* **PT-1 — partial trace at the matrix level.** For matrices on a
  product index `Fin m × Fin n` (written here over general finite
  types `m × n`), `partialTraceB` is the block trace over the second
  factor. This object existed nowhere before this module: the gauntlet
  re-grepped the corpus and the pinned Mathlib (0 hits for any partial
  trace), and this build re-verified that absence. Here it is defined
  and its basic package is proved: trace preservation, linearity,
  star/`conjTranspose` compatibility, Hermitian and positivity
  preservation (positivity in the corpus's own `IsDensityMatrix`
  form, FlowKernel), the product rule `Tr_B(A ⊗ₖ B) = Tr(B) • A`, the
  trace-duality characterization
  `Tr(Tr_B(A) * X) = Tr(A * (X ⊗ₖ 1))`, and the corollary that the
  reduced state of a density matrix is a density matrix.

* **PT-2 — the toy.** The dephasing channel as diagonal pinching in a
  product basis: `pinch A` keeps only the diagonal of `A`.
  Populations (diagonal entries) and the trace are invariant;
  off-diagonals are killed in ONE application, so iteration is
  constant from the first step (`pinch^[k] = pinch` for `k ≥ 1` —
  the geometric decay degenerates to a single step for this
  channel); purity `Tr ρ²` is non-increasing, with equality iff the
  state was already diagonal. Glue with PT-1: pinching commutes with
  the partial trace, so the reduced state of a jointly pinched state
  has all off-diagonals exactly zero; the reduced diagonal is the
  system populations.

**TOY — read this header before citing anything below.**
Finite-dimensional throughout; a single channel (pinching in one
fixed product basis); no environment dynamics, no rates, no times,
no continuum. The named coherence quantity is `offDiagMass`
(the ℓ¹ mass of the off-diagonal entries). Nothing here is a claim
about physical decoherence in any system; the measurement problem
is not touched (it remains T5 by type, per the gauntlet §4b).
-/

-- ============================================================================
-- PT-1: partial trace over the second factor
-- ============================================================================

section PartialTrace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The partial trace over the second factor, at the matrix level:
the `(i, i')` entry is the trace of the `(i, i')` block,
`∑ j, A (i, j) (i', j)`. Definition by block trace (gauntlet §9, PT-1). -/
def partialTraceB (A : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  of fun i i' => ∑ j, A (i, j) (i', j)

theorem partialTraceB_apply (A : Matrix (m × n) (m × n) ℂ) (i i' : m) :
    partialTraceB A i i' = ∑ j, A (i, j) (i', j) := rfl

/-- The reduced diagonal is the system populations: the diagonal of
the reduced state at `i` is the joint diagonal summed over the
environment index. -/
theorem partialTraceB_diag (A : Matrix (m × n) (m × n) ℂ) (i : m) :
    partialTraceB A i i = ∑ j, A (i, j) (i, j) := rfl

theorem partialTraceB_zero : partialTraceB (0 : Matrix (m × n) (m × n) ℂ) = 0 := by
  ext i i'
  simp [partialTraceB_apply]

theorem partialTraceB_add (A B : Matrix (m × n) (m × n) ℂ) :
    partialTraceB (A + B) = partialTraceB A + partialTraceB B := by
  ext i i'
  simp [partialTraceB_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem partialTraceB_smul (c : ℂ) (A : Matrix (m × n) (m × n) ℂ) :
    partialTraceB (c • A) = c • partialTraceB A := by
  ext i i'
  simp [partialTraceB_apply, Matrix.smul_apply, Finset.mul_sum]

/-- Trace preservation: `Tr (Tr_B A) = Tr A`. -/
theorem trace_partialTraceB (A : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace (partialTraceB A) = Matrix.trace A := by
  have hA : Matrix.trace A = ∑ i, ∑ j, A (i, j) (i, j) := by
    rw [show Matrix.trace A = ∑ p : m × n, A p p from rfl, Fintype.sum_prod_type]
  have hP : Matrix.trace (partialTraceB A) = ∑ i, ∑ j, A (i, j) (i, j) := by
    rw [show Matrix.trace (partialTraceB A) = ∑ i, partialTraceB A i i from rfl]
    exact Finset.sum_congr rfl fun i _ => partialTraceB_diag A i
  rw [hP, hA]

/-- Star compatibility: `conjTranspose` commutes with the partial trace. -/
theorem conjTranspose_partialTraceB (A : Matrix (m × n) (m × n) ℂ) :
    (partialTraceB A)ᴴ = partialTraceB Aᴴ := by
  ext i i'
  rw [Matrix.conjTranspose_apply]
  simp only [partialTraceB_apply, star_sum]
  exact Finset.sum_congr rfl fun j _ =>
    (Matrix.conjTranspose_apply A (i', j) (i, j)).symm

theorem isHermitian_partialTraceB {A : Matrix (m × n) (m × n) ℂ} (hA : A.IsHermitian) :
    (partialTraceB A).IsHermitian := by
  have hAe : Aᴴ = A := hA
  show (partialTraceB A)ᴴ = partialTraceB A
  rw [conjTranspose_partialTraceB, hAe]

end PartialTrace

-- ============================================================================
-- PT-1 continued: positivity via the embedding (quadratic-form) identity
-- ============================================================================

section PartialTracePositivity

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The embedding of a system vector `v` into the `j`-th environment
slice of the joint space. The partial trace's quadratic form is the
sum of the joint quadratic form over these embeddings — this is the
content of positivity preservation. -/
def embedB (v : m → ℂ) (j : n) : m × n → ℂ := fun p => if p.2 = j then v p.1 else 0

theorem star_embedB (v : m → ℂ) (j : n) (p : m × n) :
    (star (embedB v j)) p = if p.2 = j then star (v p.1) else 0 := by
  by_cases h : p.2 = j <;> simp [embedB, h]

theorem mulVec_embedB (A : Matrix (m × n) (m × n) ℂ) (v : m → ℂ) (j : n) (p : m × n) :
    (A *ᵥ (embedB v j)) p = ∑ i', A p (i', j) * v i' := by
  rw [mulVec_apply_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i' _
  have : ∀ j'', A p (i', j'') * embedB v j (i', j'')
      = if j'' = j then A p (i', j) * v i' else 0 := by
    intro j''
    by_cases h : j'' = j <;> simp [embedB, h]
  rw [Finset.sum_congr rfl (fun j'' _ => this j''), Finset.sum_ite_eq']
  simp

/-- The quadratic-form identity for the partial trace: the reduced
quadratic form at `v` is the sum, over environment slices `j`, of
the joint quadratic form at the embedded vector `embedB v j`. -/
theorem dotProduct_partialTraceB_mulVec (A : Matrix (m × n) (m × n) ℂ) (v : m → ℂ) :
    (star v) ⬝ᵥ ((partialTraceB A) *ᵥ v)
      = ∑ j, (star (embedB v j)) ⬝ᵥ (A *ᵥ (embedB v j)) := by
  have hdp : ∀ (a b : m → ℂ), a ⬝ᵥ b = ∑ i, a i * b i := fun a b => rfl
  have hdp2 : ∀ (a b : m × n → ℂ), a ⬝ᵥ b = ∑ p, a p * b p := fun a b => rfl
  have expand : ∀ i, star (v i) * ((partialTraceB A) *ᵥ v) i
      = ∑ i', ∑ j, star (v i) * (A (i, j) (i', j) * v i') := by
    intro i
    rw [mulVec_apply_eq_sum]
    simp only [partialTraceB_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  have expandR : ∀ j, (star (embedB v j)) ⬝ᵥ (A *ᵥ (embedB v j))
      = ∑ i, star (v i) * (∑ i', A (i, j) (i', j) * v i') := by
    intro j
    rw [hdp2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    have hs : ∀ j', (star (embedB v j)) (i, j') = if j' = j then star (v i) else 0 :=
      fun j' => star_embedB v j (i, j')
    have hm : ∀ j', (A *ᵥ (embedB v j)) (i, j') = ∑ i', A (i, j') (i', j) * v i' :=
      fun j' => mulVec_embedB A v j (i, j')
    have hterm : ∀ j', (star (embedB v j)) (i, j') * (A *ᵥ (embedB v j)) (i, j')
        = if j' = j then star (v i) * (∑ i', A (i, j) (i', j) * v i') else 0 := by
      intro j'
      rw [hs j', hm j']
      by_cases h : j' = j
      · rw [h]; simp
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl (fun j' _ => hterm j'), Finset.sum_ite_eq']
    simp
  have swap : ∀ i, (∑ i', ∑ j, star (v i) * (A (i, j) (i', j) * v i'))
      = ∑ j, ∑ i', star (v i) * (A (i, j) (i', j) * v i') := fun i => Finset.sum_comm
  simp only [hdp, Pi.star_apply, expand, expandR, Finset.mul_sum, swap]
  exact Finset.sum_comm

/-- Positivity preservation, in the corpus's own form (the positivity
clause of `IsDensityMatrix`, FlowKernel): the reduced quadratic form
is a sum of joint quadratic forms, hence nonnegative if all of those
are. -/
theorem partialTraceB_quadratic_nonneg {A : Matrix (m × n) (m × n) ℂ}
    (hA : ∀ x : m × n → ℂ, 0 ≤ ((star x) ⬝ᵥ (A *ᵥ x)).re) (v : m → ℂ) :
    0 ≤ ((star v) ⬝ᵥ ((partialTraceB A) *ᵥ v)).re := by
  rw [dotProduct_partialTraceB_mulVec, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => hA (embedB v j)

/-- The reduced state of a density matrix is a density matrix
(corpus `IsDensityMatrix`, FlowKernel). -/
theorem IsDensityMatrix.partialTraceB {A : Matrix (m × n) (m × n) ℂ}
    (hA : IsDensityMatrix A) : IsDensityMatrix (partialTraceB A) :=
  ⟨isHermitian_partialTraceB hA.1, partialTraceB_quadratic_nonneg hA.2.1,
    by rw [trace_partialTraceB]; exact hA.2.2⟩

end PartialTracePositivity

-- ============================================================================
-- PT-1 continued: product rule and trace-duality characterization
-- ============================================================================

section PartialTraceProduct

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The product rule: tracing out the second factor of a Kronecker
product leaves the first factor, scaled by the trace of the second:
`Tr_B(A ⊗ₖ B) = Tr(B) • A`. -/
theorem partialTraceB_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    partialTraceB (A ⊗ₖ B) = (Matrix.trace B) • A := by
  ext i i'
  rw [partialTraceB_apply,
    Finset.sum_congr rfl (fun j _ => Matrix.kronecker_apply A B i j i' j),
    ← Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The trace-duality characterization of the partial trace:
`Tr ((Tr_B A) * X) = Tr (A * (X ⊗ₖ 1))` for every system operator
`X`. This is the basis-independent content of the definition: it
pins `partialTraceB` uniquely among linear maps (any two linear
maps satisfying it agree under the nondegenerate trace pairing). -/
theorem trace_partialTraceB_mul (A : Matrix (m × n) (m × n) ℂ) (X : Matrix m m ℂ) :
    Matrix.trace (partialTraceB A * X)
      = Matrix.trace (A * (X ⊗ₖ (1 : Matrix n n ℂ))) := by
  have lhs : Matrix.trace (partialTraceB A * X)
      = ∑ i, ∑ i', ∑ j, A (i, j) (i', j) * X i' i := by
    rw [show Matrix.trace (partialTraceB A * X) = ∑ i, (partialTraceB A * X) i i from rfl]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i' _
    rw [partialTraceB_apply, Finset.sum_mul]
  have rhs : Matrix.trace (A * (X ⊗ₖ (1 : Matrix n n ℂ)))
      = ∑ i, ∑ i', ∑ j, A (i, j) (i', j) * X i' i := by
    rw [show Matrix.trace (A * (X ⊗ₖ (1 : Matrix n n ℂ)))
          = ∑ p : m × n, (A * (X ⊗ₖ (1 : Matrix n n ℂ))) p p from rfl,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    have hpt : ∀ j, (A * (X ⊗ₖ (1 : Matrix n n ℂ))) (i, j) (i, j)
        = ∑ i', A (i, j) (i', j) * X i' i := by
      intro j
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i' _
      have hsumm : ∀ j', A (i, j) (i', j') * (X ⊗ₖ (1 : Matrix n n ℂ)) (i', j') (i, j)
          = if j' = j then A (i, j) (i', j) * X i' i else 0 := by
        intro j'
        by_cases h : j' = j
        · subst h; simp [Matrix.one_apply]
        · simp [Matrix.kronecker_apply, Matrix.one_apply, h]
      rw [Finset.sum_congr rfl (fun j' _ => hsumm j'), Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    exact Finset.sum_comm
  rw [lhs, rhs]

end PartialTraceProduct

-- ============================================================================
-- PT-2: the dephasing channel as diagonal pinching
-- ============================================================================

section Pinch

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dephasing channel: diagonal pinching. `pinch A` is the
diagonal matrix built from the diagonal of `A` — every off-diagonal
entry is set to zero, in the fixed basis of the index type. (TOY:
one channel, one basis, finite-dimensional.) -/
def pinch (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.diagonal fun i => A i i

theorem pinch_apply (A : Matrix ι ι ℂ) (i j : ι) :
    pinch A i j = if i = j then A i i else 0 := Matrix.diagonal_apply _ i j

/-- Populations are invariant under pinching: the diagonal of
`pinch A` is the diagonal of `A`. -/
theorem pinch_diag (A : Matrix ι ι ℂ) (i : ι) : pinch A i i = A i i :=
  Matrix.diagonal_apply_eq _ i

/-- Off-diagonals are killed: for `i ≠ j`, `(pinch A) i j = 0`. -/
theorem pinch_apply_ne (A : Matrix ι ι ℂ) {i j : ι} (h : i ≠ j) : pinch A i j = 0 :=
  Matrix.diagonal_apply_ne _ h

theorem trace_pinch (A : Matrix ι ι ℂ) : Matrix.trace (pinch A) = Matrix.trace A := by
  rw [pinch, Matrix.trace_diagonal]
  rfl

theorem pinch_idem (A : Matrix ι ι ℂ) : pinch (pinch A) = pinch A := by
  ext i j
  by_cases h : i = j
  · subst h; rw [pinch_diag]
  · rw [pinch_apply_ne _ h, pinch_apply_ne _ h]

/-- Iteration: pinching is constant from the first application —
`pinch^[k] = pinch` for every `k ≥ 1`. (For this channel the
"geometric decay under iteration" of the gauntlet degenerates to a
single step: the off-diagonals do not decay gradually, they are
gone at `k = 1` and stay gone.) -/
theorem pinch_iterate (A : Matrix ι ι ℂ) : ∀ k : ℕ, 1 ≤ k → pinch^[k] A = pinch A := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    cases k with
    | zero => intro _; rfl
    | succ k =>
      intro _
      rw [Function.iterate_succ_apply', ih (by omega), pinch_idem]

theorem conjTranspose_pinch (A : Matrix ι ι ℂ) : (pinch A)ᴴ = pinch Aᴴ := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.conjTranspose_apply, pinch_diag, pinch_diag, Matrix.conjTranspose_apply]
  · rw [Matrix.conjTranspose_apply, pinch_apply_ne _ (Ne.symm h), star_zero,
      pinch_apply_ne _ h]

theorem isHermitian_pinch {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (pinch A).IsHermitian := by
  have hAe : Aᴴ = A := hA
  show (pinch A)ᴴ = pinch A
  rw [conjTranspose_pinch, hAe]

/-- The `i`-th basis vector of `ι → ℂ`, as an explicit if-then-else
(avoiding the dependent-family elaboration of `Pi.single`). -/
def basisVec (i : ι) : ι → ℂ := fun k => if k = i then 1 else 0

theorem star_basisVec (i k : ι) :
    (star (basisVec i)) k = if k = i then 1 else 0 := by
  rw [Pi.star_apply]
  by_cases h : k = i <;> simp [basisVec, h]

theorem mulVec_basisVec (A : Matrix ι ι ℂ) (i k : ι) :
    (A *ᵥ (basisVec i)) k = A k i := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single i]
  · simp [basisVec]
  · intro j _ hji
    simp [basisVec, hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The dephased state of a density matrix is a density matrix
(corpus `IsDensityMatrix`, FlowKernel). The content beyond the
preservation lemmas above: a diagonal entry of a density matrix is
real and nonnegative (the quadratic form at a basis vector), so the
pinched quadratic form `∑ i, ρ i i • ‖x i‖²` is nonnegative. -/
theorem isDensityMatrix_pinch {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (pinch ρ) := by
  have hAe : ρᴴ = ρ := hρ.1
  have him : ∀ i, (ρ i i).im = 0 := by
    intro i
    have h1 : ρᴴ i i = star (ρ i i) := Matrix.conjTranspose_apply ρ i i
    rw [hAe] at h1
    have h2 : (ρ i i).im = (star (ρ i i)).im := congrArg Complex.im h1
    rw [← starRingEnd_apply, Complex.conj_im] at h2
    linarith
  have hquad : ∀ i, (star (basisVec i)) ⬝ᵥ (ρ *ᵥ (basisVec i)) = ρ i i := by
    intro i
    have hdp : ∀ (a b : ι → ℂ), a ⬝ᵥ b = ∑ k, a k * b k := fun a b => rfl
    rw [hdp, Finset.sum_eq_single i]
    · rw [star_basisVec, mulVec_basisVec]
      simp
    · intro k _ hki
      rw [star_basisVec, if_neg hki, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hnn : ∀ i, 0 ≤ (ρ i i).re := by
    intro i
    have h := hρ.2.1 (basisVec i)
    rwa [hquad i] at h
  refine ⟨isHermitian_pinch hρ.1, ?_, by rw [trace_pinch]; exact hρ.2.2⟩
  intro x
  have hmv : ∀ i, ((pinch ρ) *ᵥ x) i = ρ i i * x i := by
    intro i
    rw [mulVec_apply_eq_sum, Finset.sum_eq_single i]
    · rw [pinch_diag]
    · intro j _ hji
      rw [pinch_apply_ne _ (Ne.symm hji), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hdp : ∀ (a b : ι → ℂ), a ⬝ᵥ b = ∑ i, a i * b i := fun a b => rfl
  have hterm : ∀ i, (star x) i * ((pinch ρ) *ᵥ x) i
      = (((ρ i i).re * Complex.normSq (x i) : ℝ) : ℂ) := by
    intro i
    have hre : ρ i i = ((ρ i i).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him i]
    have e2 : star (x i) * x i = ((Complex.normSq (x i) : ℝ) : ℂ) := by
      have e := Complex.mul_conj (x i)
      rw [starRingEnd_apply, mul_comm] at e
      exact e
    rw [hmv i, Pi.star_apply, hre]
    calc star (x i) * (((ρ i i).re : ℂ) * x i)
        = ((ρ i i).re : ℂ) * (star (x i) * x i) := by ring
      _ = ((ρ i i).re : ℂ) * ((Complex.normSq (x i) : ℝ) : ℂ) := by rw [e2]
      _ = (((ρ i i).re * Complex.normSq (x i) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul]
  rw [hdp, Finset.sum_congr rfl (fun i _ => hterm i), Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hnn i) (Complex.normSq_nonneg _)

theorem pinch_eq_self_iff (A : Matrix ι ι ℂ) :
    pinch A = A ↔ ∀ i j, i ≠ j → A i j = 0 := by
  constructor
  · intro h i j hij
    have h2 : pinch A i j = A i j := by rw [h]
    rw [pinch_apply_ne _ hij] at h2
    exact h2.symm
  · intro h
    ext i j
    by_cases hij : i = j
    · subst hij; exact pinch_diag A i
    · rw [pinch_apply_ne _ hij, h i j hij]

/-- The named coherence quantity: the ℓ¹ mass of the off-diagonal
entries. (TOY bookkeeping: a norm of the coherence, not a rate.) -/
noncomputable def offDiagMass (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, if i = j then 0 else ‖A i j‖

/-- After one pinching, the coherence quantity is exactly zero. -/
theorem offDiagMass_pinch (A : Matrix ι ι ℂ) : offDiagMass (pinch A) = 0 := by
  unfold offDiagMass
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : i = j
  · rw [if_pos h]
  · rw [if_neg h, pinch_apply_ne _ h, norm_zero]

/-- …and it stays zero under iteration, for every `k ≥ 1`. -/
theorem offDiagMass_pinch_iterate (A : Matrix ι ι ℂ) {k : ℕ} (hk : 1 ≤ k) :
    offDiagMass (pinch^[k] A) = 0 := by
  rw [pinch_iterate A k hk]
  exact offDiagMass_pinch A

-- Purity -----------------------------------------------------------------

/-- The squared Frobenius mass `∑ i j, ‖A i j‖²`. For Hermitian `A`
this is `Tr (A * A)` (proved below), i.e. the purity `Tr ρ²` for a
density matrix `ρ`. -/
noncomputable def frobeniusSq (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem frobeniusSq_pinch (A : Matrix ι ι ℂ) :
    frobeniusSq (pinch A) = ∑ i, ‖A i i‖ ^ 2 := by
  unfold frobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [pinch_diag]
  · intro j _ hji
    rw [pinch_apply_ne _ (Ne.symm hji)]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem diag_frobeniusSq_le (A : Matrix ι ι ℂ) :
    (∑ i, ‖A i i‖ ^ 2) ≤ frobeniusSq A := by
  unfold frobeniusSq
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖A i j‖) (Finset.mem_univ i)

theorem trace_mul_self_eq_frobeniusSq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    Matrix.trace (A * A) = (frobeniusSq A : ℂ) := by
  have hAe : Aᴴ = A := hA
  have step : ∀ i j, A i j * A j i = ((‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i j
    have hji : A j i = star (A i j) := by
      have h1 : Aᴴ i j = star (A j i) := Matrix.conjTranspose_apply A j i
      rw [hAe] at h1
      have h2 := congrArg star h1
      rw [star_star] at h2
      exact h2.symm
    rw [hji]
    have e := Complex.mul_conj (A i j)
    rw [starRingEnd_apply] at e
    rw [e, Complex.normSq_eq_norm_sq]
  rw [show Matrix.trace (A * A) = ∑ i, (A * A) i i from rfl]
  simp only [Matrix.mul_apply]
  unfold frobeniusSq
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => step i j

/-- Purity is non-increasing under pinching: for Hermitian `ρ`,
`Tr ((pinch ρ)²) ≤ Tr (ρ²)` (as real numbers — both traces are
real, by the Frobenius identity above). -/
theorem trace_sq_pinch_le {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    (Matrix.trace ((pinch ρ) * (pinch ρ))).re ≤ (Matrix.trace (ρ * ρ)).re := by
  rw [trace_mul_self_eq_frobeniusSq (isHermitian_pinch hρ),
    trace_mul_self_eq_frobeniusSq hρ, Complex.ofReal_re, frobeniusSq_pinch]
  exact diag_frobeniusSq_le ρ

/-- Equality in the purity bound holds iff the state was already
diagonal: `Tr ((pinch ρ)²) = Tr (ρ²) ↔ pinch ρ = ρ`. -/
theorem trace_sq_pinch_eq_iff {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    Matrix.trace ((pinch ρ) * (pinch ρ)) = Matrix.trace (ρ * ρ) ↔ pinch ρ = ρ := by
  rw [trace_mul_self_eq_frobeniusSq (isHermitian_pinch hρ),
    trace_mul_self_eq_frobeniusSq hρ]
  constructor
  · intro h
    have hf : frobeniusSq (pinch ρ) = frobeniusSq ρ := by exact_mod_cast h
    rw [frobeniusSq_pinch] at hf
    have hsplit : ∀ i, (∑ j, ‖ρ i j‖ ^ 2)
        = ‖ρ i i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖ρ i j‖ ^ 2 :=
      fun i => (Finset.add_sum_erase Finset.univ (fun j => ‖ρ i j‖ ^ 2)
        (Finset.mem_univ i)).symm
    have hsplit2 : frobeniusSq ρ
        = (∑ i, ‖ρ i i‖ ^ 2) + ∑ i, ∑ j ∈ Finset.univ.erase i, ‖ρ i j‖ ^ 2 := by
      unfold frobeniusSq
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hsplit i
    have hoff : ∑ i, ∑ j ∈ Finset.univ.erase i, ‖ρ i j‖ ^ 2 = 0 := by
      have hnn : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ‖ρ i j‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hzero : ∀ i j, j ≠ i → ‖ρ i j‖ ^ 2 = 0 := by
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖ρ i j‖))).mp hoff
      intro i j hji
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ‖ρ i j‖)).mp (h1 i (Finset.mem_univ i))
      exact h2 j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    rw [pinch_eq_self_iff]
    intro i j hij
    have h3 := hzero i j (Ne.symm hij)
    have h4 : ‖ρ i j‖ = 0 := (pow_eq_zero_iff (two_ne_zero)).mp h3
    exact norm_eq_zero.mp h4
  · intro h
    rw [h]

end Pinch

-- ============================================================================
-- Glue: pinching commutes with the partial trace
-- ============================================================================

section Glue

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Pinching the joint state in the product basis and then reducing
is the same as reducing and then pinching: the channel and the
partial trace commute. -/
theorem partialTraceB_pinch (A : Matrix (m × n) (m × n) ℂ) :
    partialTraceB (pinch A) = pinch (partialTraceB A) := by
  ext i i'
  by_cases h : i = i'
  · subst h
    rw [pinch_diag, partialTraceB_apply, partialTraceB_apply]
    exact Finset.sum_congr rfl fun j _ => pinch_diag A (i, j)
  · rw [pinch_apply_ne _ h, partialTraceB_apply]
    apply Finset.sum_eq_zero
    intro j _
    exact pinch_apply_ne _ (fun hh => h (congrArg Prod.fst hh))

/-- Headline: after one joint pinching, EVERY off-diagonal of the
reduced state is exactly zero — the reduced coherence vanishes. -/
theorem partialTraceB_pinch_apply_ne (A : Matrix (m × n) (m × n) ℂ)
    {i i' : m} (h : i ≠ i') : partialTraceB (pinch A) i i' = 0 := by
  rw [partialTraceB_pinch, pinch_apply_ne _ h]

/-- The reduced coherence quantity after one joint pinching is
exactly zero. -/
theorem offDiagMass_partialTraceB_pinch (A : Matrix (m × n) (m × n) ℂ) :
    offDiagMass (partialTraceB (pinch A)) = 0 := by
  rw [partialTraceB_pinch]
  exact offDiagMass_pinch _

end Glue
