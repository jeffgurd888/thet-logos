/-
# Word/tensor bookkeeping (Route B, step T3)

Companion brick to the Gram-clause campaign (Pitch 4, Stage 1b-B).
Charter: `whitepaper/gram-clause-scoping-2026-10-23.md`, §4 Route B,
step **T3** — word/tensor bookkeeping. Steps T2 (the averaging
projection, `ThetLogos.AveragingProjection`) and T1 (the integrated
Gram criterion, `ThetLogos.LatticeGramSeries`) are landed; step T4
(assembly and the β ≥ 0 discharge) consumes this module.

## Content

The crossing action `S₀` is a sum over crossing plaquettes of
densities `1 − (1/d) Re tr ρ(w)`, where the plaquette word `w`, read
in split variables against Stage 1b-A's `splitEquiv`, is an ordered
product of link factors, each either a stratum link or its inverse,
sandwiched between factors that do not depend on the stratum
variables. The standard proof expands the Boltzmann factor
`exp((β/d) Re tr ρ(w))` in matrix coefficients of tensor powers of
`ρ` and integrates the stratum (plane) variables. Two pieces of
bookkeeping make that integration available to T2's averaging
operator, and they are this module's whole content:

* **Words are tensor-representation matrix coefficients.** For a
  finite slot type `ι` (the stratum link positions of *both*
  halves, jointly) the slot tensor matrix
  `tensorMat M a b = ∏ i, M i (a i) (b i)` is multiplicative, so
  finite products of single-link matrix coefficients are matrix
  coefficients of one finite-dimensional tensor representation
  `occRep` of the stratum product group `ι → G`
  (`occMat_mul`, `occRep`). Inverse word factors are coefficients
  of the conjugate representation `conjRep`, with indices swapped
  (`repMatrix_inv_entry`). A word in `Fin n` signed slot factors
  therefore expands as a finite sum, over index paths, of matrix
  coefficients of the single joint occurrence representation
  (`word_entry`) — the rectangular pairing of the 1b-B dossier's
  counterexample 2 is absorbed by tensoring both stratum factors
  into this one representation, not by treating the two sides'
  plaquettes separately. Traces multiply over slots
  (`tensorMat_trace`), so products and powers of plaquette traces
  are traces of tensor powers (`tensorMat_trace_prod`,
  `tensorMat_trace_pow`).

* **The joint stratum integral is `A` applied.** The stratum
  product group carries the product Haar probability measure
  `Measure.pi (fun _ => μG)`, which is left- and inversion-
  invariant (`Measure.pi` instances below). For the occurrence
  representation's continuous linear form `occRepCLM`, every
  matrix coefficient integrates against this measure to the
  corresponding coefficient of T2's averaging operator
  (`integral_occMat_eq_averaging`), and the same holds for word
  entries (`integral_word_entry`).

## Formulation choices (disclosed)

* The slot type `ι`, the occurrence type, the word length and the
  sign pattern are abstract finite data. Which lattice links are
  the stratum slots, and the identification of the corpus's
  crossing words with `wordGroup` below, are T4's instantiation
  work; nothing of the lattice appears here.
* `ρ` is the corpus's own representation (`repMatrix` of
  `ThetLogos.LatticeGauge`), unitary-valued by construction, so
  unitarity of every tensor representation built here is
  definitional, per the charter's fence. Continuity of
  `repMatrix ρ` is passed explicitly, as in the corpus.
* The occurrence continuous linear map is built as a finite sum of
  rank-one maps over `EuclideanSpace.basisFun`, so its matrix
  coefficients are the occurrence matrices by construction.

## Fences

Bookkeeping only: no `β`, no Boltzmann factor, no series, no OS
form, no positivity statement. The β ≥ 0 discharge and the
assembly through T1's integrated criterion are T4. **NO CLAIM** —
parts of any official Clay statement closed by this module: 0.
-/

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import ThetLogos.LatticeGauge
import ThetLogos.AveragingProjection

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace Matrix

namespace ThetLogos

namespace GramWordTensor

/-! ## §1. The slot tensor matrix

For matrices `M i` indexed by a finite slot type `ι`, `tensorMat M`
is the matrix of the tensor product representation on multi-indices
`ι → Fin d`: its `(a, b)` entry is the product over slots of the
single-slot entries. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The slot tensor matrix: `(tensorMat M) a b = ∏ i, M i (a i) (b i)`.
This is the matrix of the tensor product of the slot operators with
respect to the product basis. -/
def tensorMat (M : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  fun a b => ∏ i, M i (a i) (b i)

@[simp]
theorem tensorMat_apply (M : ι → Matrix (Fin d) (Fin d) ℂ)
    (a b : ι → Fin d) :
    tensorMat M a b = ∏ i, M i (a i) (b i) := rfl

/-- The tensor matrix of the identity family is the identity. -/
theorem tensorMat_one :
    tensorMat (fun _ : ι => (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  ext a b
  simp only [tensorMat_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · have ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    have h1 : (∏ i, (if a i = b i then (1 : ℂ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    have h2 : (if a = b then (1 : ℂ) else 0) = 0 := by simp [h]
    rw [h1, h2]

/-- **Multiplicativity.** The tensor matrix of a pointwise product
of matrix families is the product of the tensor matrices: expanding
the product over slots of sums over intermediate indices, and
interchanging the product with the sum over multi-indices. -/
theorem tensorMat_mul (M N : ι → Matrix (Fin d) (Fin d) ℂ) :
    tensorMat (fun i => M i * N i) = tensorMat M * tensorMat N := by
  classical
  ext a b
  simp only [tensorMat_apply, Matrix.mul_apply, Fintype.prod_sum,
    Finset.prod_mul_distrib]

/-- The star of a tensor matrix is the tensor matrix of the stars. -/
theorem tensorMat_star (M : ι → Matrix (Fin d) (Fin d) ℂ) :
    star (tensorMat M) = tensorMat (fun i => star (M i)) := by
  ext a b
  simp only [Matrix.star_apply, tensorMat_apply, star_prod]

/-- A tensor matrix of unitary matrices is unitary. -/
theorem tensorMat_mem_unitaryGroup (M : ι → Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ i, M i ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    tensorMat M ∈ Matrix.unitaryGroup (ι → Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, tensorMat_star, ← tensorMat_mul]
  have : (fun i => M i * star (M i)) = fun _ => (1 : Matrix (Fin d) (Fin d) ℂ) := by
    funext i
    rw [← Matrix.mem_unitaryGroup_iff]
    exact hM i
  rw [this, tensorMat_one]

/-- Entries factor over a sum of slot types: tensoring is joint
over both factors at once. -/
theorem tensorMat_apply_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    (M : (ι₁ ⊕ ι₂) → Matrix (Fin d) (Fin d) ℂ)
    (a b : ι₁ ⊕ ι₂ → Fin d) :
    tensorMat M a b
      = (∏ i₁, M (Sum.inl i₁) (a (Sum.inl i₁)) (b (Sum.inl i₁)))
        * ∏ i₂, M (Sum.inr i₂) (a (Sum.inr i₂)) (b (Sum.inr i₂)) := by
  rw [tensorMat_apply, Fintype.prod_sum_type]

/-- **Traces multiply over slots.** The trace of a tensor matrix is
the product of the slot traces: sum over multi-indices of the
diagonal product, interchanged. -/
theorem tensorMat_trace (M : ι → Matrix (Fin d) (Fin d) ℂ) :
    (tensorMat M).trace = ∏ i, (M i).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, tensorMat_apply, Fintype.prod_sum]

/-! ## §2. The conjugate representation and occurrence representations

Inverse word factors contribute entries of `repMatrix ρ g⁻¹`, which
is the star of `repMatrix ρ g`: an inverse factor at positions
`(x, y)` is the `(y, x)` entry of the conjugate representation.
Tensoring occurrences of `ρ` and of `conjRep ρ` over a joint slot
type gives one representation of the stratum product group. -/

section TensorRep

variable {G : Type*} [Group G] (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The entrywise conjugate of a matrix (for `ℂ`, entrywise
`star`). The conjugate representation's matrix. -/
def conjMat (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => star (M i j)

@[simp]
theorem conjMat_apply (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    conjMat M i j = star (M i j) := rfl

theorem conjMat_one : conjMat (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext i j
  simp [conjMat, Matrix.one_apply]

theorem conjMat_mul (M N : Matrix (Fin d) (Fin d) ℂ) :
    conjMat (M * N) = conjMat M * conjMat N := by
  ext i j
  simp only [conjMat_apply, Matrix.mul_apply, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul, mul_comm]

theorem conjMat_mem_unitaryGroup {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    conjMat M ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  have hstar : star (conjMat M) = Matrix.transpose M := by
    ext i j
    simp [Matrix.star_apply, conjMat, Matrix.transpose_apply]
  rw [hstar]
  ext i j
  have key : ∀ i j : Fin d,
      (∑ k, star (M i k) * M j k) = star ((M * star M) i j) := by
    intro i j
    rw [Matrix.mul_apply, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.star_apply, star_mul, star_star, mul_comm]
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, conjMat_apply]
  rw [key, hM, Matrix.one_apply]
  split_ifs with h
  · simp [h]
  · simp

/-- **The conjugate representation**: `g ↦ conjMat (repMatrix ρ g)`,
a genuine homomorphism into the unitary group (entrywise
conjugation preserves products). Word factors `g⁻¹` are its matrix
coefficients with indices swapped. -/
def conjRep : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ) where
  toFun g := ⟨conjMat (repMatrix ρ g), conjMat_mem_unitaryGroup (repMatrix_mem ρ g)⟩
  map_one' := by
    apply Subtype.ext
    show conjMat (repMatrix ρ 1) = 1
    rw [repMatrix_one, conjMat_one]
  map_mul' a b := by
    apply Subtype.ext
    show conjMat (repMatrix ρ (a * b))
      = conjMat (repMatrix ρ a) * conjMat (repMatrix ρ b)
    rw [repMatrix_mul, conjMat_mul]

@[simp]
theorem repMatrix_conjRep (g : G) :
    repMatrix (conjRep ρ) g = conjMat (repMatrix ρ g) := rfl

/-- An inverse factor's entry is a conjugate-representation
coefficient with the indices swapped. -/
theorem repMatrix_inv_entry (g : G) (x y : Fin d) :
    (repMatrix ρ g⁻¹) x y = repMatrix (conjRep ρ) g y x := by
  rw [repMatrix_inv, Matrix.star_apply]
  rfl

/-- The trace of the conjugate representation is the conjugate of
the trace. -/
theorem trace_conjRep (g : G) :
    (repMatrix (conjRep ρ) g).trace = star ((repMatrix ρ g).trace) := by
  simp [Matrix.trace, Matrix.diag, star_sum]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The occurrence matrix over a joint slot type: the slot tensor
matrix of the per-occurrence representation matrices, occurrence
`occ` reading the group element at slot `slot occ`. -/
def occMat (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s : ι → G) :
    Matrix (κ → Fin d) (κ → Fin d) ℂ :=
  tensorMat (fun occ => repMatrix (Ψ occ) (s (slot occ)))

@[simp]
theorem occMat_apply (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (s : ι → G) (A B : κ → Fin d) :
    occMat slot Ψ s A B = ∏ occ, repMatrix (Ψ occ) (s (slot occ)) (A occ) (B occ) :=
  rfl

theorem occMat_one (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) :
    occMat slot Ψ (1 : ι → G) = 1 := by
  have hfam : (fun occ => repMatrix (Ψ occ) ((1 : ι → G) (slot occ)))
      = fun _ => (1 : Matrix (Fin d) (Fin d) ℂ) := by
    funext occ
    simp
  show tensorMat (fun occ => repMatrix (Ψ occ) ((1 : ι → G) (slot occ))) = 1
  rw [hfam, tensorMat_one]

theorem occMat_mul (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (s t : ι → G) :
    occMat slot Ψ (s * t) = occMat slot Ψ s * occMat slot Ψ t := by
  show tensorMat (fun occ => repMatrix (Ψ occ) ((s * t) (slot occ)))
    = tensorMat (fun occ => repMatrix (Ψ occ) (s (slot occ)))
      * tensorMat (fun occ => repMatrix (Ψ occ) (t (slot occ)))
  rw [← tensorMat_mul]
  congr 1
  funext occ
  rw [Pi.mul_apply, repMatrix_mul]

theorem occMat_mem_unitaryGroup
    (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s : ι → G) :
    occMat slot Ψ s ∈ Matrix.unitaryGroup (κ → Fin d) ℂ :=
  tensorMat_mem_unitaryGroup _ fun occ => repMatrix_mem _ _

/-- **The occurrence representation** of the stratum product group
`ι → G`: one finite-dimensional unitary representation whose
matrix coefficients are the joint products of per-occurrence
coefficients — both stratum factors tensored together. -/
def occRep (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) :
    (ι → G) →* ↥(Matrix.unitaryGroup (κ → Fin d) ℂ) where
  toFun s := ⟨occMat slot Ψ s, occMat_mem_unitaryGroup slot Ψ s⟩
  map_one' := Subtype.ext (occMat_one slot Ψ)
  map_mul' s t := Subtype.ext (occMat_mul slot Ψ s t)

@[simp]
theorem occRep_apply (slot : κ → ι) (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (s : ι → G) :
    ((occRep slot Ψ) s).1 = occMat slot Ψ s := rfl

/-- A product of single-link traces is one trace of the slot tensor
matrix. -/
theorem tensorMat_trace_prod (s : ι → G) :
    (tensorMat (fun i => repMatrix ρ (s i))).trace
      = ∏ i, (repMatrix ρ (s i)).trace :=
  tensorMat_trace _

/-- **Tensor powers.** The `k`-th power of a product of traces is
one trace of the tensor power over the product slot type
`Fin k × ι` with the configuration repeated along `Fin k`. -/
theorem tensorMat_trace_pow {k : ℕ} (s : ι → G) :
    (tensorMat (fun x : Fin k × ι => repMatrix ρ (s x.2))).trace
      = (∏ i, (repMatrix ρ (s i)).trace) ^ k := by
  rw [tensorMat_trace, Fintype.prod_prod_type]
  simp

end TensorRep

/-! ## §3. Words as tensor-representation matrix coefficients

A word is an ordered product of signed slot factors. Its
representation matrix expands over index paths, and each path
product is one matrix coefficient of the joint occurrence
representation of §2 — direct factors through `ρ`, inverse factors
through `conjRep` with the path indices swapped. -/

section Words

variable {G : Type*} [Group G] (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The recursive path sum: `pathSum [M₁, …, Mᵣ] a b` is the
`(a, b)` entry of the product `M₁ * ⋯ * Mᵣ`, computed by summing
over intermediate indices one factor at a time. -/
def pathSum : List (Matrix (Fin d) (Fin d) ℂ) → Fin d → Fin d → ℂ
  | [], a, b => if a = b then 1 else 0
  | (M :: Ms), a, b => ∑ c, M a c * pathSum Ms c b

theorem list_prod_entry (Ms : List (Matrix (Fin d) (Fin d) ℂ)) (a b : Fin d) :
    Ms.prod a b = pathSum Ms a b := by
  induction Ms generalizing a b with
  | nil => simp [pathSum, Matrix.one_apply]
  | cons M Ms ih =>
    rw [List.prod_cons, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih]

/-- `repMatrix ρ` of a product of group elements is the product of
the matrices. -/
theorem repMatrix_list_prod (l : List G) :
    repMatrix ρ l.prod = (l.map (repMatrix ρ)).prod := by
  induction l with
  | nil => simp
  | cons g l ih => rw [List.prod_cons, List.map_cons, List.prod_cons,
      repMatrix_mul, ih]

/-- **The path formula.** The path sum over a list of matrices is
the sum over all index paths from `a` to `b` of the product of the
factor entries along the path. -/
theorem pathSum_eq_sum_paths (Ms : List (Matrix (Fin d) (Fin d) ℂ)) (a b : Fin d) :
    pathSum Ms a b
      = ∑ p : Fin (Ms.length + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last Ms.length) = b then
            ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩) (p j.castSucc) (p j.succ)
          else 0) := by
  induction Ms generalizing a b with
  | nil =>
    simp only [List.length_nil]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => Fin d)), Fintype.sum_prod_type]
    have hq : ∀ x : Fin d, (∑ q : Fin 0 → Fin d,
        (if (Fin.consEquiv (fun _ => Fin d)) (x, q) 0 = a
            ∧ (Fin.consEquiv (fun _ => Fin d)) (x, q) (Fin.last 0) = b
          then ∏ j : Fin 0, (([] : List (Matrix (Fin d) (Fin d) ℂ)).get ⟨j.val, j.isLt⟩)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.castSucc)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.succ)
          else 0))
        = (if x = a ∧ x = b then (1 : ℂ) else 0) := by
      intro x
      rw [Fintype.sum_unique]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.last_zero,
        Fin.prod_univ_zero]
    rw [Finset.sum_congr rfl (fun x _ => hq x)]
    have hx : ∀ x : Fin d, (if x = a ∧ x = b then (1 : ℂ) else 0)
        = (if x = a then (if a = b then (1 : ℂ) else 0) else 0) := by
      intro x
      by_cases h : x = a
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq']
    simp [pathSum]
  | cons M Ms ih =>
    have hprod : ∀ (x : Fin d) (q : Fin (Ms.length + 1) → Fin d),
        (∏ j : Fin (Ms.length + 1), ((M :: Ms).get ⟨j.val, j.isLt⟩)
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.castSucc)
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.succ))
          = M x (q 0) * ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ) := by
      intro x q
      have hcons : (Fin.consEquiv (fun _ => Fin d)) (x, q) = Fin.cons x q := rfl
      have h0 : ((M :: Ms).get ⟨(0 : Fin (Ms.length + 1)).val,
            (0 : Fin (Ms.length + 1)).isLt⟩)
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.castSucc 0))
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.succ 0))
          = M x (q 0) := by
        rw [hcons]
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        rfl
      have htail : (∏ j : Fin Ms.length,
            ((M :: Ms).get ⟨(Fin.succ j).val, (Fin.succ j).isLt⟩)
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.succ j).castSucc)
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.succ j).succ))
          = ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [hcons, Fin.val_succ, List.get_cons_succ, Fin.castSucc_succ,
          Fin.cons_succ]
      rw [Fin.prod_univ_succ, h0, htail]
    have hsummand : ∀ (x : Fin d) (q : Fin (Ms.length + 1) → Fin d),
        (if (Fin.consEquiv (fun _ => Fin d)) (x, q) 0 = a
            ∧ (Fin.consEquiv (fun _ => Fin d)) (x, q) (Fin.last (Ms.length + 1)) = b
          then ∏ j : Fin (Ms.length + 1), ((M :: Ms).get ⟨j.val, j.isLt⟩)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.castSucc)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.succ)
          else 0)
        = (if x = a then (if q (Fin.last Ms.length) = b
              then M a (q 0) * ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
                (q j.castSucc) (q j.succ)
              else 0) else 0) := by
      intro x q
      have h0 : (Fin.consEquiv (fun _ => Fin d)) (x, q) 0 = x := by
        have hcons : (Fin.consEquiv (fun _ => Fin d)) (x, q) = Fin.cons x q := rfl
        rw [hcons, Fin.cons_zero]
      have hl : (Fin.consEquiv (fun _ => Fin d)) (x, q) (Fin.last (Ms.length + 1))
          = q (Fin.last Ms.length) := by
        have hcons : (Fin.consEquiv (fun _ => Fin d)) (x, q) = Fin.cons x q := rfl
        rw [hcons, ← Fin.succ_last, Fin.cons_succ]
      rw [h0, hl, hprod x q]
      by_cases hx : x = a
      · subst hx; simp
      · simp [hx]
    have hinner : ∀ (q : Fin (Ms.length + 1) → Fin d),
        (∑ c, M a c * (if q 0 = c ∧ q (Fin.last Ms.length) = b
            then ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ)
            else 0))
        = (if q (Fin.last Ms.length) = b
            then M a (q 0) * ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ)
            else 0) := by
      intro q
      have hterm : ∀ c : Fin d, M a c * (if q 0 = c ∧ q (Fin.last Ms.length) = b
            then ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ)
            else 0)
          = (if c = q 0 then M a c * (if q (Fin.last Ms.length) = b
              then ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
                (q j.castSucc) (q j.succ)
              else 0) else 0) := by
        intro c
        by_cases hc : c = q 0
        · subst hc; simp
        · have h1 : ¬ (q 0 = c) := fun h => hc h.symm
          simp [h1, hc]
      rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_ite_eq']
      simp [mul_ite]
    have hLHS : pathSum (M :: Ms) a b
        = ∑ c, M a c * (∑ q : Fin (Ms.length + 1) → Fin d,
            (if q 0 = c ∧ q (Fin.last Ms.length) = b
              then ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
                (q j.castSucc) (q j.succ)
              else 0)) := by
      show (∑ c, M a c * pathSum Ms c b) = _
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ih]
    rw [hLHS]
    simp only [List.length_cons]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => Fin d)), Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun q _ => hsummand x q))]
    rw [Finset.sum_comm]
    have hcollapse : ∀ (q : Fin (Ms.length + 1) → Fin d),
        (∑ x : Fin d, (if x = a then (if q (Fin.last Ms.length) = b
            then M a (q 0) * ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ)
            else 0) else 0))
        = (if q (Fin.last Ms.length) = b
            then M a (q 0) * ∏ j : Fin Ms.length, (Ms.get ⟨j.val, j.isLt⟩)
              (q j.castSucc) (q j.succ)
            else 0) := by
      intro q
      rw [Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl (fun q _ => hcollapse q)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => hinner q

/-- The path formula for a `Fin n`-indexed factor family, proved by
induction on `n` (the list form `pathSum_eq_sum_paths` does not
transport along `List.length_ofFn` by rewriting, since the length
occurs in the path types themselves). -/
theorem pathSum_ofFn_eq_sum_paths {n : ℕ} (F : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin d) :
    pathSum (List.ofFn F) a b
      = ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = b then
            ∏ j : Fin n, (F j) (p j.castSucc) (p j.succ)
          else 0) := by
  induction n generalizing a b with
  | zero =>
    have hstep : ∀ p : Fin 1 → Fin d,
        (if p 0 = a ∧ p (Fin.last 0) = b then
          ∏ j : Fin 0, (F j) (p j.castSucc) (p j.succ) else 0)
        = (if p 0 = a ∧ p 0 = b then (1 : ℂ) else 0) := by
      intro p
      rw [Fin.prod_univ_zero, Fin.last_zero]
    have hbij : Function.Bijective (fun p : Fin 1 → Fin d => p 0) := by
      refine ⟨fun p q hpq => ?_, fun x => ⟨fun _ => x, rfl⟩⟩
      funext i
      rw [Fin.eq_zero i]
      exact hpq
    calc pathSum (List.ofFn F) a b = if a = b then (1 : ℂ) else 0 := by
          simp only [List.ofFn_zero, pathSum]
      _ = ∑ x : Fin d, (if x = a ∧ x = b then (1 : ℂ) else 0) := by
          rw [Finset.sum_eq_single b (fun x _ hx => if_neg (fun h => hx h.2))
            (fun h => (h (Finset.mem_univ b)).elim)]
          by_cases h : a = b
          · rw [if_pos h, if_pos ⟨h.symm, rfl⟩]
          · rw [if_neg h, if_neg (fun hh => h hh.1.symm)]
      _ = ∑ p : Fin 1 → Fin d, (if p 0 = a ∧ p 0 = b then (1 : ℂ) else 0) :=
          (Fintype.sum_bijective (fun p : Fin 1 → Fin d => p 0) hbij _ _
            (fun _ => rfl)).symm
      _ = ∑ p : Fin 1 → Fin d,
            (if p 0 = a ∧ p (Fin.last 0) = b then
              ∏ j : Fin 0, (F j) (p j.castSucc) (p j.succ) else 0) :=
          Finset.sum_congr rfl fun p _ => (hstep p).symm
  | succ n ih =>
    classical
    have hprod : ∀ (x : Fin d) (q : Fin (n + 1) → Fin d),
        (∏ j : Fin (n + 1), (F j) (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.castSucc)
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.succ))
          = (F 0) x (q 0) * ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ) := by
      intro x q
      have hcons : (Fin.consEquiv (fun _ => Fin d)) (x, q) = Fin.cons x q := rfl
      have hhead : (F 0) (((Fin.consEquiv (fun _ => Fin d)) (x, q))
              (Fin.castSucc (0 : Fin (n + 1))))
            (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.succ (0 : Fin (n + 1))))
          = (F 0) x (q 0) := by
        rw [hcons]
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
      have htail : (∏ j : Fin n, (F j.succ)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.castSucc (Fin.succ j)))
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) (Fin.succ (Fin.succ j))))
          = ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hcons, Fin.castSucc_succ, Fin.cons_succ, Fin.cons_succ]
      rw [Fin.prod_univ_succ, hhead, htail]
    have hsummand : ∀ (x : Fin d) (q : Fin (n + 1) → Fin d),
        (if (Fin.consEquiv (fun _ => Fin d)) (x, q) 0 = a
            ∧ (Fin.consEquiv (fun _ => Fin d)) (x, q) (Fin.last (n + 1)) = b
          then ∏ j : Fin (n + 1), (F j)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.castSucc)
              (((Fin.consEquiv (fun _ => Fin d)) (x, q)) j.succ)
          else 0)
        = (if x = a then (if q (Fin.last n) = b
              then (F 0) a (q 0) * ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
              else 0) else 0) := by
      intro x q
      have h0 : (Fin.consEquiv (fun _ => Fin d)) (x, q) 0 = x := by
        have hcons : (Fin.consEquiv (fun _ => Fin d)) (x, q) = Fin.cons x q := rfl
        rw [hcons, Fin.cons_zero]
      have hl : (Fin.consEquiv (fun _ => Fin d)) (x, q) (Fin.last (n + 1))
          = q (Fin.last n) := by
        have hcons : (Fin.consEquiv (fun _ => Fin d)) (x, q) = Fin.cons x q := rfl
        rw [hcons, ← Fin.succ_last, Fin.cons_succ]
      rw [h0, hl, hprod x q]
      by_cases hx : x = a
      · subst hx; simp
      · simp [hx]
    have hinner : ∀ (q : Fin (n + 1) → Fin d),
        (∑ c, (F 0) a c * (if q 0 = c ∧ q (Fin.last n) = b
            then ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
            else 0))
        = (if q (Fin.last n) = b
            then (F 0) a (q 0) * ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
            else 0) := by
      intro q
      have hterm : ∀ c : Fin d, (F 0) a c * (if q 0 = c ∧ q (Fin.last n) = b
              then ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
              else 0)
            = (if c = q 0 then (F 0) a c * (if q (Fin.last n) = b
                then ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
                else 0) else 0) := by
        intro c
        by_cases hc : c = q 0
        · subst hc; simp
        · have h1 : ¬ (q 0 = c) := fun h => hc h.symm
          simp [h1, hc]
      rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_ite_eq']
      simp [mul_ite]
    have hLHS : pathSum (List.ofFn F) a b
        = ∑ c, (F 0) a c * (∑ q : Fin (n + 1) → Fin d,
            (if q 0 = c ∧ q (Fin.last n) = b
              then ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
              else 0)) := by
      rw [List.ofFn_succ]
      show (∑ c, (F 0) a c * pathSum (List.ofFn (fun j => F j.succ)) c b) = _
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ih]
    rw [hLHS, ← Equiv.sum_comp (Fin.consEquiv (fun _ => Fin d)),
      Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun q _ => hsummand x q))]
    rw [Finset.sum_comm]
    have hcollapse : ∀ (q : Fin (n + 1) → Fin d),
        (∑ x : Fin d, (if x = a then (if q (Fin.last n) = b
            then (F 0) a (q 0) * ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
            else 0) else 0))
        = (if q (Fin.last n) = b
            then (F 0) a (q 0) * ∏ j : Fin n, (F j.succ) (q j.castSucc) (q j.succ)
            else 0) := by
      intro q
      rw [Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl (fun q _ => hcollapse q)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => hinner q

/-- A word: the ordered product of a `Fin n`-indexed family of
group factors. -/
def wordGroup {n : ℕ} (factor : Fin n → G) : G := (List.ofFn factor).prod

theorem repMatrix_wordGroup {n : ℕ} (factor : Fin n → G) :
    repMatrix ρ (wordGroup factor)
      = (List.ofFn fun j => repMatrix ρ (factor j)).prod := by
  show repMatrix ρ (List.ofFn factor).prod = _
  rw [repMatrix_list_prod, List.map_ofFn]
  simp only [Function.comp_def]

/-- **Word entries as path sums of factor coefficients.** -/
theorem word_entry_factor {n : ℕ} (factor : Fin n → G) (a b : Fin d) :
    (repMatrix ρ (wordGroup factor)) a b
      = ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = b then
            ∏ j : Fin n, (repMatrix ρ (factor j)) (p j.castSucc) (p j.succ)
          else 0) := by
  rw [repMatrix_wordGroup, list_prod_entry]
  exact pathSum_ofFn_eq_sum_paths (fun j => repMatrix ρ (factor j)) a b

/-- The trace of a word matrix is the sum over closed paths. -/
theorem word_trace {n : ℕ} (factor : Fin n → G) :
    (repMatrix ρ (wordGroup factor)).trace
      = ∑ a, ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = a then
            ∏ j : Fin n, (repMatrix ρ (factor j)) (p j.castSucc) (p j.succ)
          else 0) := by
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.sum_congr rfl fun a _ => word_entry_factor ρ factor a a

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The flavor of a word factor: `ρ` for a direct factor, the
conjugate representation for an inverse factor. -/
def flavRep (flag : Bool) : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  if flag then ρ else conjRep ρ

/-- The first path index of a word factor in the occurrence
coefficient: direct factors read the path forward, inverse factors
read it backward (the swap of `repMatrix_inv_entry`). -/
def pathA {n : ℕ} (flag : Fin n → Bool) (p : Fin (n + 1) → Fin d) (j : Fin n) :
    Fin d :=
  if flag j then p j.castSucc else p j.succ

/-- The second path index of a word factor. -/
def pathB {n : ℕ} (flag : Fin n → Bool) (p : Fin (n + 1) → Fin d) (j : Fin n) :
    Fin d :=
  if flag j then p j.succ else p j.castSucc

/-- **Word entries are joint occurrence coefficients.** For a word
in signed slot factors over a joint slot type `ι`, every path
product is one matrix coefficient of the single occurrence
representation `occRep slot (fun j => flavRep ρ (flag j))` of the
stratum product group: both stratum factors are tensored together,
and the rectangular pairing is absorbed. -/
theorem word_entry {n : ℕ} (slot : Fin n → ι) (flag : Fin n → Bool)
    (s : ι → G) (a b : Fin d) :
    (repMatrix ρ (wordGroup (fun j => if flag j then s (slot j)
        else (s (slot j))⁻¹))) a b
      = ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = b then
            occMat slot (fun j => flavRep ρ (flag j)) s (pathA flag p) (pathB flag p)
          else 0) := by
  rw [word_entry_factor]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p 0 = a ∧ p (Fin.last n) = b
  · rw [if_pos h, if_pos h]
    rw [occMat_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hf : flag j
    · simp [hf, flavRep, pathA, pathB]
    · simp [hf, flavRep, pathA, pathB, repMatrix_inv_entry]
  · rw [if_neg h, if_neg h]

end Words

/-! ## §4. The joint stratum integral is the averaging operator applied

The occurrence representation of §2, realized as a continuous linear
map on the Euclidean space over the joint index set `κ → Fin d`. The
stratum product group `ι → G` carries the product Haar probability
measure; §4's two headline theorems identify the joint stratum
integral of an occurrence coefficient — and, through §3, of a word
entry — with T2's averaging operator applied to the corresponding
basis vector. -/

section StratumIntegral

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
  [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsInvInvariant]
variable (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The joint basis of the Euclidean space over `κ → Fin d` is
orthonormal, in if-and-only-if form. -/
lemma basis_inner (A B : κ → Fin d) :
    ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A,
      (EuclideanSpace.basisFun (κ → Fin d) ℂ) B⟫_ℂ
      = if A = B then (1 : ℂ) else 0 :=
  (orthonormal_iff_ite.mp (EuclideanSpace.basisFun (κ → Fin d) ℂ).orthonormal) A B

/-- **The occurrence representation as a continuous linear map**:
the finite sum of rank-one maps with the `occMat` coefficients,
on the Euclidean space over the joint index set. -/
noncomputable def occRepCLM (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s : ι → G) :
    (EuclideanSpace ℂ (κ → Fin d)) →L[ℂ] (EuclideanSpace ℂ (κ → Fin d)) :=
  ∑ A : κ → Fin d, ∑ B : κ → Fin d,
    (occMat slot Ψ s A B) • InnerProductSpace.rankOne ℂ
      ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A)
      ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)

/-- The occurrence CLM applied to a basis vector is the corresponding
column of the occurrence matrix, expanded in the basis. -/
theorem occRepCLM_apply_basis (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s : ι → G) (B : κ → Fin d) :
    occRepCLM slot Ψ s ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)
      = ∑ A, (occMat slot Ψ s A B) •
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A) := by
  classical
  simp only [occRepCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  refine (Finset.sum_eq_single B (fun C _ hCB => ?_)
    (fun h => (h (Finset.mem_univ B)).elim)).trans ?_
  · rw [show ((occMat slot Ψ s A C) • InnerProductSpace.rankOne ℂ
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A)
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) C))
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)
        = (occMat slot Ψ s A C) • (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) C,
            (EuclideanSpace.basisFun (κ → Fin d) ℂ) B⟫_ℂ •
            ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A)) from rfl,
      basis_inner, if_neg hCB, zero_smul, smul_zero]
  · rw [show ((occMat slot Ψ s A B) • InnerProductSpace.rankOne ℂ
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A)
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B))
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)
        = (occMat slot Ψ s A B) • (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B,
            (EuclideanSpace.basisFun (κ → Fin d) ℂ) B⟫_ℂ •
            ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A)) from rfl,
      basis_inner, if_pos rfl, one_smul]

/-- **Coefficient identity.** The `(A, B)` matrix coefficient of the
occurrence CLM is the occurrence matrix entry. -/
theorem occRepCLM_inner_basis (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s : ι → G)
    (A B : κ → Fin d) :
    ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A,
      occRepCLM slot Ψ s ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)⟫_ℂ
      = occMat slot Ψ s A B := by
  classical
  rw [occRepCLM_apply_basis, inner_sum]
  refine (Finset.sum_eq_single A (fun A' _ hA' => ?_)
    (fun h => (h (Finset.mem_univ A)).elim)).trans ?_
  · rw [inner_smul_right, basis_inner, if_neg (fun h => hA' h.symm), mul_zero]
  · rw [inner_smul_right, basis_inner, if_pos rfl, mul_one]

/-- **Coefficient formula for a general vector.** The `A`-th basis
coefficient of the image of `v` under the occurrence CLM is the
matrix product of the occurrence row with the coefficients of `v`. -/
theorem occRepCLM_inner_basis_apply (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s : ι → G)
    (v : EuclideanSpace ℂ (κ → Fin d)) (A : κ → Fin d) :
    ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, occRepCLM slot Ψ s v⟫_ℂ
      = ∑ B, (occMat slot Ψ s A B) *
          ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ := by
  classical
  conv_lhs => rw [← (EuclideanSpace.basisFun (κ → Fin d) ℂ).sum_repr' v]
  rw [_root_.map_sum, inner_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [map_smul, inner_smul_right, occRepCLM_inner_basis, mul_comm]


/-- Occurrence matrix entries are continuous in the stratum
configuration, entry by entry from the per-occurrence continuity. -/
lemma occMat_entry_continuous (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g)
    (A B : κ → Fin d) :
    Continuous fun s : ι → G => occMat slot Ψ s A B := by
  simp only [occMat_apply]
  refine continuous_finset_prod _ fun occ _ => ?_
  exact (continuous_apply (B occ)).comp ((continuous_apply (A occ)).comp
    ((hΨcont occ).comp (continuous_apply (slot occ))))

/-- The occurrence CLM depends continuously on the stratum
configuration: a finite sum of rank-one maps with continuous
coefficients. This is the continuity hypothesis T2's averaging
operator consumes. -/
theorem occRepCLM_continuous (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g) :
    Continuous (occRepCLM slot Ψ) := by
  classical
  show Continuous fun s => occRepCLM slot Ψ s
  simp only [occRepCLM]
  refine continuous_finset_sum _ fun A _ => ?_
  refine continuous_finset_sum _ fun B _ => ?_
  exact Continuous.smul (occMat_entry_continuous slot Ψ hΨcont A B)
    continuous_const

/-- Two vectors with the same basis coefficients are equal. -/
lemma ext_of_inner_basis {x y : EuclideanSpace ℂ (κ → Fin d)}
    (h : ∀ A, ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, x⟫_ℂ
      = ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, y⟫_ℂ) : x = y := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (κ → Fin d) ℂ).sum_repr' x]
  conv_rhs => rw [← (EuclideanSpace.basisFun (κ → Fin d) ℂ).sum_repr' y]
  exact Finset.sum_congr rfl fun A _ => by rw [h A]

/-- Parseval's identity in the joint basis. -/
lemma inner_eq_sum (x y : EuclideanSpace ℂ (κ → Fin d)) :
    ⟪x, y⟫_ℂ = ∑ A, star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, x⟫_ℂ)
      * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, y⟫_ℂ := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (κ → Fin d) ℂ).sum_repr' x]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [inner_smul_left]
  simp only [← RCLike.star_def]

/-- **Unitarity of the occurrence CLM.** Each `occRepCLM s` preserves
the inner product: its matrix is unitary (`occMat_mem_unitaryGroup`),
and Parseval transports the matrix identity to the Euclidean space.
This is the unitarity hypothesis T2's averaging operator consumes. -/
theorem occRepCLM_unitary (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) :
    ∀ (s : ι → G) (v w : EuclideanSpace ℂ (κ → Fin d)),
      ⟪occRepCLM slot Ψ s v, occRepCLM slot Ψ s w⟫_ℂ = ⟪v, w⟫_ℂ := by
  classical
  intro s v w
  have hδ : ∀ B C : κ → Fin d,
      ∑ A, star (occMat slot Ψ s A B) * occMat slot Ψ s A C
        = if B = C then (1 : ℂ) else 0 := by
    intro B C
    have h1 : star (occMat slot Ψ s) * occMat slot Ψ s = 1 :=
      mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp
        (occMat_mem_unitaryGroup slot Ψ s))
    have h2 := congrArg (fun N : Matrix (κ → Fin d) (κ → Fin d) ℂ => N B C) h1
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    simpa only [Matrix.star_apply] using h2
  have hmain : (∑ A, star (∑ B, occMat slot Ψ s A B *
        ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ)
        * (∑ C, occMat slot Ψ s A C *
        ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) C, w⟫_ℂ))
      = ∑ A, star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, v⟫_ℂ)
        * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, w⟫_ℂ := by
    calc (∑ A, star (∑ B, occMat slot Ψ s A B *
            ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ)
          * (∑ C, occMat slot Ψ s A C *
            ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) C, w⟫_ℂ))
        = ∑ A, ∑ B, ∑ C, (star (occMat slot Ψ s A B) * occMat slot Ψ s A C)
            * (star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) C, w⟫_ℂ) := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun B _ =>
            Finset.sum_congr rfl fun C _ => ?_
          simp only [star_mul]
          ring
      _ = ∑ B, ∑ C, ∑ A, (star (occMat slot Ψ s A B) * occMat slot Ψ s A C)
            * (star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) C, w⟫_ℂ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ B, ∑ C, (∑ A, star (occMat slot Ψ s A B) * occMat slot Ψ s A C)
            * (star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) C, w⟫_ℂ) := by
          refine Finset.sum_congr rfl fun B _ =>
            Finset.sum_congr rfl fun C _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ B, star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) B, w⟫_ℂ := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [Finset.sum_eq_single B]
          · rw [hδ B B, if_pos rfl, one_mul]
          · intro C _ hCB
            rw [hδ B C, if_neg (Ne.symm hCB), zero_mul]
          · exact fun h => (h (Finset.mem_univ B)).elim
      _ = ∑ A, star (⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, v⟫_ℂ)
            * ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A, w⟫_ℂ := rfl
  rw [inner_eq_sum, inner_eq_sum]
  simp only [occRepCLM_inner_basis_apply]
  exact hmain

/-- The occurrence CLM at the identity configuration is the
identity. -/
theorem occRepCLM_one (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) :
    occRepCLM slot Ψ 1 = 1 := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply ext_of_inner_basis
  intro A
  rw [occRepCLM_inner_basis_apply, ContinuousLinearMap.one_apply]
  have hM : ∀ B : κ → Fin d, occMat slot Ψ (1 : ι → G) A B
      = if A = B then (1 : ℂ) else 0 := by
    intro B
    rw [occMat_one, Matrix.one_apply]
  rw [Finset.sum_eq_single A]
  · rw [hM A, if_pos rfl, one_mul]
  · intro B _ hBA
    rw [hM B, if_neg (fun h => hBA h.symm), zero_mul]
  · exact fun h => (h (Finset.mem_univ A)).elim

/-- The occurrence CLM is multiplicative in the stratum
configuration: it is a representation of the stratum product group
by continuous linear maps. -/
theorem occRepCLM_mul (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (s t : ι → G) :
    occRepCLM slot Ψ (s * t) = occRepCLM slot Ψ s * occRepCLM slot Ψ t := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply ext_of_inner_basis
  intro A
  rw [ContinuousLinearMap.mul_apply]
  simp only [occRepCLM_inner_basis_apply]
  rw [occMat_mul]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun B _ => ?_
  ring


/-- Per-factor continuity for the flavored representations of §3:
direct factors by hypothesis, inverse factors through the conjugate
representation, whose matrix is the entrywise conjugate. -/
lemma flavRep_continuous {n : ℕ} (flag : Fin n → Bool)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (j : Fin n) :
    Continuous fun g : G => repMatrix (flavRep ρ (flag j)) g := by
  by_cases hf : flag j
  · have h1 : flavRep ρ (flag j) = ρ := by simp [flavRep, hf]
    rw [h1]
    exact hρcont
  · have h1 : flavRep ρ (flag j) = conjRep ρ := by simp [flavRep, hf]
    rw [h1]
    simp only [repMatrix_conjRep]
    refine continuous_pi_iff.mpr fun i => continuous_pi_iff.mpr fun j => ?_
    show Continuous fun a => star (repMatrix ρ a i j)
    exact continuous_star.comp ((continuous_apply j).comp
      ((continuous_apply i).comp hρcont))

/-- **Headline 1: the joint stratum integral is `A` applied.** The
integral of an occurrence coefficient over the stratum product group,
against the product Haar probability measure, is the corresponding
matrix coefficient of T2's averaging operator for the occurrence
representation: integrate the coefficient identity
`occRepCLM_inner_basis` against `averagingOperator_apply`, pulling
the integral out of the inner product by `innerSL`. -/
theorem integral_occMat_eq_averaging (slot : κ → ι)
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g)
    (A B : κ → Fin d) :
    (∫ s, occMat slot Ψ s A B ∂(Measure.pi fun _ : ι => μG))
      = ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A,
          AveragingProjection.averagingOperator (Measure.pi fun _ : ι => μG)
            (occRepCLM slot Ψ) (occRepCLM_continuous slot Ψ hΨcont)
            (occRepCLM_unitary slot Ψ)
            ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)⟫_ℂ := by
  haveI : CompleteSpace (EuclideanSpace ℂ (κ → Fin d)) :=
    FiniteDimensional.complete ℂ _
  rw [AveragingProjection.averagingOperator_apply]
  show (∫ s, occMat slot Ψ s A B ∂(Measure.pi fun _ : ι => μG))
      = (innerSL ℂ ((EuclideanSpace.basisFun (κ → Fin d) ℂ) A))
          (∫ s, occRepCLM slot Ψ s
            ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)
            ∂(Measure.pi fun _ : ι => μG))
  rw [← ContinuousLinearMap.integral_comp_comm _
    (AveragingProjection.integrable_apply _ _
      (occRepCLM_continuous slot Ψ hΨcont)
      ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
    (occRepCLM_inner_basis slot Ψ s A B).symm)

/-- **Headline 2: word entries integrate to `A`-coefficients.** The
stratum integral of a word entry is the finite path sum of the
averaging operator's matrix coefficients at the path endpoints —
§3's `word_entry` writes the word entry as a path sum of joint
occurrence coefficients, headline 1 integrates each coefficient, and
the rectangular pairing stays absorbed in the single joint
occurrence representation throughout. -/
theorem integral_word_entry {n : ℕ} (slot : Fin n → ι) (flag : Fin n → Bool)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (a b : Fin d) :
    (∫ s, (repMatrix ρ (wordGroup (fun j => if flag j then s (slot j)
        else (s (slot j))⁻¹))) a b ∂(Measure.pi fun _ : ι => μG))
      = ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = b then
            ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ) (pathA flag p),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ι => μG)
                (occRepCLM slot (fun j => flavRep ρ (flag j)))
                (occRepCLM_continuous slot _
                  (fun j => flavRep_continuous ρ flag hρcont j))
                (occRepCLM_unitary slot _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ) (pathB flag p))⟫_ℂ
          else 0) := by
  classical
  have hpt : ∀ s : ι → G, (repMatrix ρ (wordGroup (fun j => if flag j then
        s (slot j) else (s (slot j))⁻¹))) a b
      = ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = b then
            occMat slot (fun j => flavRep ρ (flag j)) s (pathA flag p)
              (pathB flag p)
          else 0) := fun s => word_entry ρ slot flag s a b
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hc
    · exact integral_occMat_eq_averaging (μG := μG) slot
        (fun j => flavRep ρ (flag j))
        (fun j => flavRep_continuous ρ flag hρcont j)
        (pathA flag p) (pathB flag p)
    · simp
  · intro p _
    split_ifs with hc
    · exact (occMat_entry_continuous slot (fun j => flavRep ρ (flag j))
        (fun j => flavRep_continuous ρ flag hρcont j)
        (pathA flag p) (pathB flag p)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · exact integrable_zero _ _ _

end StratumIntegral

end GramWordTensor

end ThetLogos
