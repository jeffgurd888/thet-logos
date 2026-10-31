import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix Finset
open scoped Kronecker

namespace ThetLogos

/-!
# Partial trace (finite-dimensional) + purity vocabulary — SHELF-4

General-API stock, built under Jeff's "fill the shelf" commission
(2026-10-30). This module retires the absence fenced in
`whitepaper/gauntlet-schrodinger-2026-10-16.md`: "What does not
exist: **partial trace** — zero hits in Mathlib, zero in the
corpus — and no channel/purity vocabulary anywhere." The pin
re-check at dispatch (2026-10-30) re-grepped the vendored
Mathlib v4.35.0-rc3 tree for `partialTrace`, `traceLeft`,
`traceRight` and tensor-trace APIs: zero hits — the pin does
not own a partial trace, so the fill is built here from
scratch, as explicit entry sums over product index types.

(The corpus's toy module `DecoherenceToy` carries a
seat-specific one-direction block trace, `partialTraceB`,
proved for its dephasing toy. This module is the general
stock: both directions, over general finite index types,
plus the purity vocabulary. It imports no corpus module.)

Finite-dimensional throughout: states and operators are
matrices over a product index type `ι × κ` with entries in
`ℂ`. Purity is stocked as its own vocabulary item — the
complex trace `tr (ρ * ρ)`, with its reality under
Hermiticity — and is not identified with any other quantity.

NO CLAIM; dials 0/4. General-API stock only: nothing here is
a claim about any corpus line's results.
-/

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

-- ===========================================================================
-- The two partial traces, as explicit entry sums
-- ===========================================================================

/-- The partial trace over the **second** factor: for a matrix
`M` on the product index type `ι × κ`, `partialTraceRight M`
is the matrix on `ι` whose `(i, i')` entry traces out the
second index, `∑ j, M (i, j) (i', j)`. -/
def partialTraceRight (M : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  of fun i i' => ∑ j, M (i, j) (i', j)

/-- The partial trace over the **first** factor: for a matrix
`M` on the product index type `ι × κ`, `partialTraceLeft M`
is the matrix on `κ` whose `(j, j')` entry traces out the
first index, `∑ i, M (i, j) (i, j')`. -/
def partialTraceLeft (M : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ :=
  of fun j j' => ∑ i, M (i, j) (i, j')

theorem partialTraceRight_apply (M : Matrix (ι × κ) (ι × κ) ℂ) (i i' : ι) :
    partialTraceRight M i i' = ∑ j, M (i, j) (i', j) := rfl

theorem partialTraceLeft_apply (M : Matrix (ι × κ) (ι × κ) ℂ) (j j' : κ) :
    partialTraceLeft M j j' = ∑ i, M (i, j) (i, j') := rfl

-- ===========================================================================
-- Linearity
-- ===========================================================================

theorem partialTraceRight_zero :
    partialTraceRight (0 : Matrix (ι × κ) (ι × κ) ℂ) = 0 := by
  ext i i'
  simp [partialTraceRight_apply]

theorem partialTraceLeft_zero :
    partialTraceLeft (0 : Matrix (ι × κ) (ι × κ) ℂ) = 0 := by
  ext j j'
  simp [partialTraceLeft_apply]

theorem partialTraceRight_add (M N : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceRight (M + N) = partialTraceRight M + partialTraceRight N := by
  ext i i'
  simp [partialTraceRight_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem partialTraceLeft_add (M N : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft (M + N) = partialTraceLeft M + partialTraceLeft N := by
  ext j j'
  simp [partialTraceLeft_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem partialTraceRight_smul (c : ℂ) (M : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceRight (c • M) = c • partialTraceRight M := by
  ext i i'
  simp [partialTraceRight_apply, Matrix.smul_apply, Finset.mul_sum]

theorem partialTraceLeft_smul (c : ℂ) (M : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft (c • M) = c • partialTraceLeft M := by
  ext j j'
  simp [partialTraceLeft_apply, Matrix.smul_apply, Finset.mul_sum]

-- ===========================================================================
-- Trace preservation (headline)
-- ===========================================================================

/-- Trace preservation, right form: the partial trace over the
second factor preserves the total trace. -/
theorem trace_partialTraceRight (M : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (partialTraceRight M) = Matrix.trace M := by
  have hP : Matrix.trace (partialTraceRight M) = ∑ i, ∑ j, M (i, j) (i, j) := by
    rw [show Matrix.trace (partialTraceRight M) = ∑ i, partialTraceRight M i i from rfl]
    exact Finset.sum_congr rfl fun i _ => partialTraceRight_apply M i i
  have hM : Matrix.trace M = ∑ i, ∑ j, M (i, j) (i, j) := by
    rw [show Matrix.trace M = ∑ p : ι × κ, M p p from rfl, Fintype.sum_prod_type]
  rw [hP, hM]

/-- Trace preservation, left form: the partial trace over the
first factor preserves the total trace. -/
theorem trace_partialTraceLeft (M : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix.trace (partialTraceLeft M) = Matrix.trace M := by
  have hP : Matrix.trace (partialTraceLeft M) = ∑ j, ∑ i, M (i, j) (i, j) := by
    rw [show Matrix.trace (partialTraceLeft M) = ∑ j, partialTraceLeft M j j from rfl]
    exact Finset.sum_congr rfl fun j _ => partialTraceLeft_apply M j j
  have hM : Matrix.trace M = ∑ j, ∑ i, M (i, j) (i, j) := by
    rw [show Matrix.trace M = ∑ p : ι × κ, M p p from rfl, Fintype.sum_prod_type,
      Finset.sum_comm]
  rw [hP, hM]

-- ===========================================================================
-- Adjoint compatibility
-- ===========================================================================

/-- The partial trace commutes with the conjugate transpose,
right form. -/
theorem conjTranspose_partialTraceRight (M : Matrix (ι × κ) (ι × κ) ℂ) :
    (partialTraceRight M)ᴴ = partialTraceRight Mᴴ := by
  ext i i'
  simp only [Matrix.conjTranspose_apply, partialTraceRight_apply, star_sum]

/-- The partial trace commutes with the conjugate transpose,
left form. -/
theorem conjTranspose_partialTraceLeft (M : Matrix (ι × κ) (ι × κ) ℂ) :
    (partialTraceLeft M)ᴴ = partialTraceLeft Mᴴ := by
  ext j j'
  simp only [Matrix.conjTranspose_apply, partialTraceLeft_apply, star_sum]

/-- Hermiticity is preserved by the right partial trace. -/
theorem isHermitian_partialTraceRight {M : Matrix (ι × κ) (ι × κ) ℂ}
    (hM : M.IsHermitian) : (partialTraceRight M).IsHermitian := by
  show (partialTraceRight M)ᴴ = partialTraceRight M
  rw [conjTranspose_partialTraceRight, hM.eq]

/-- Hermiticity is preserved by the left partial trace. -/
theorem isHermitian_partialTraceLeft {M : Matrix (ι × κ) (ι × κ) ℂ}
    (hM : M.IsHermitian) : (partialTraceLeft M).IsHermitian := by
  show (partialTraceLeft M)ᴴ = partialTraceLeft M
  rw [conjTranspose_partialTraceLeft, hM.eq]

-- ===========================================================================
-- Product states (headline): the partial trace of a Kronecker product
-- ===========================================================================

/-- Product rule, right form: tracing out the second factor of
a Kronecker product leaves the first factor, scaled by the
trace of the second: `Tr_κ (A ⊗ₖ B) = (tr B) • A`. -/
theorem partialTraceRight_kronecker (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    partialTraceRight (A ⊗ₖ B) = (Matrix.trace B) • A := by
  ext i i'
  rw [partialTraceRight_apply,
    Finset.sum_congr rfl (fun j _ => Matrix.kronecker_apply A B i j i' j),
    ← Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Product rule, left form: tracing out the first factor of a
Kronecker product leaves the second factor, scaled by the
trace of the first: `Tr_ι (A ⊗ₖ B) = (tr A) • B`. -/
theorem partialTraceLeft_kronecker (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    partialTraceLeft (A ⊗ₖ B) = (Matrix.trace A) • B := by
  ext j j'
  rw [partialTraceLeft_apply,
    Finset.sum_congr rfl (fun i _ => Matrix.kronecker_apply A B i j i j'),
    ← Finset.sum_mul, Matrix.smul_apply, smul_eq_mul,
    show Matrix.trace A = ∑ i, A i i from rfl]

/-- The reduced state of a product state is the first factor
itself, when the traced-out factor has trace one (right form). -/
theorem partialTraceRight_kronecker_of_trace_eq_one (A : Matrix ι ι ℂ)
    (B : Matrix κ κ ℂ) (hB : Matrix.trace B = 1) :
    partialTraceRight (A ⊗ₖ B) = A := by
  rw [partialTraceRight_kronecker, hB, one_smul]

/-- The reduced state of a product state is the second factor
itself, when the traced-out factor has trace one (left form). -/
theorem partialTraceLeft_kronecker_of_trace_eq_one (A : Matrix ι ι ℂ)
    (B : Matrix κ κ ℂ) (hA : Matrix.trace A = 1) :
    partialTraceLeft (A ⊗ₖ B) = B := by
  rw [partialTraceLeft_kronecker, hA, one_smul]

-- ===========================================================================
-- Purity vocabulary
-- ===========================================================================

/-- The purity of a finite-dimensional operator, named plainly
as the complex trace of its square: `purity ρ = tr (ρ * ρ)`.
For a Hermitian `ρ` this complex number is real
(`purity_star_eq_of_isHermitian` below). Purity is stocked
here as its own vocabulary item and is not identified with
any other quantity. -/
def purity (ρ : Matrix ι ι ℂ) : ℂ := Matrix.trace (ρ * ρ)

/-- Purity of a Kronecker product is the product of the
purities of the factors. -/
theorem purity_kronecker (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    purity (A ⊗ₖ B) = purity A * purity B := by
  simp only [purity, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- Purity under the conjugate transpose is the complex
conjugate of the purity. -/
theorem purity_conjTranspose (ρ : Matrix ι ι ℂ) :
    purity ρᴴ = star (purity ρ) := by
  show Matrix.trace (ρᴴ * ρᴴ) = star (Matrix.trace (ρ * ρ))
  rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose]

/-- For a Hermitian operator the purity is real: it equals
its own complex conjugate. -/
theorem purity_star_eq_of_isHermitian {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    star (purity ρ) = purity ρ := by
  rw [← purity_conjTranspose, hρ.eq]

/-- A pure state, as a predicate: a Hermitian, trace-one
operator whose purity is one. This is a Prop-level vocabulary
item only; no further structure is asserted. -/
def IsPureState (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.IsHermitian ∧ Matrix.trace ρ = 1 ∧ purity ρ = 1

/-- Hermiticity of a Kronecker product of Hermitian factors. -/
theorem isHermitian_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  show (A ⊗ₖ B)ᴴ = A ⊗ₖ B
  rw [Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- A Kronecker product of pure states is a pure state. -/
theorem isPureState_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : IsPureState A) (hB : IsPureState B) : IsPureState (A ⊗ₖ B) := by
  refine ⟨isHermitian_kronecker hA.1 hB.1, ?_, ?_⟩
  · rw [Matrix.trace_kronecker, hA.2.1, hB.2.1, mul_one]
  · rw [purity_kronecker, hA.2.2, hB.2.2, mul_one]

/-- The Schrödinger-gauntlet use, at finite level: the reduced
state of a product state whose factors are pure is the first
factor itself — in particular it is pure. Tracing out a pure
factor costs the remaining factor nothing. -/
theorem isPureState_partialTraceRight_kronecker {A : Matrix ι ι ℂ}
    {B : Matrix κ κ ℂ} (hA : IsPureState A) (hB : IsPureState B) :
    IsPureState (partialTraceRight (A ⊗ₖ B)) := by
  rw [partialTraceRight_kronecker_of_trace_eq_one A B hB.2.1]
  exact hA

end ThetLogos
