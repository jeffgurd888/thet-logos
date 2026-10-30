/-
# ThetLogos.PlaquetteFactorPD — Brick A2-1a: positive-definite
functions, the class property of `wordDensity`, and the
character kernel's positive-definiteness

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Dials **0/4**.

This is part 1 of brick A2-1 (Route B of the claim-path scoping
of 2026-10-29, §1.4): the single-plaquette factor is
`f_β(g) = Real.exp (−(β · wordDensity ρ g))`. This module proves
**only**:

1. the positive-definite-function predicate `PosDefFun`, in
   kernel (quadratic-form) form — no Mathlib or corpus predicate
   in this form was found, so it is defined here;
2. the class property: `wordDensity` (and hence the factor
   `f_β`, stated here as a bare invariance, with no
   positive-definiteness asserted for it) is constant on
   conjugacy classes;
3. the character kernel's positive-definiteness: the function
   `g ↦ ((tr ρ g).re : ℂ)` is `PosDefFun`, by an explicit Gram
   factorization over the matrix entries of `ρ`.

**No claim that `f_β` is positive-definite is made in this
brick** — the exponential assembly is brick A2-1b. Route B's
telescoping (A2-2) and `𝒜 ⪰ 0` itself are untouched.

Hypotheses discipline: only `G` a group and
`ρ : G →* unitaryGroup (Fin d) ℂ`. No `hd : 0 < d` hypothesis
appears anywhere in this module: `wordDensity` divides by `d`
as a real number, but its conjugation invariance and the
character kernel's positivity close without ever needing the
division to be nonzero.
-/

import ThetLogos.PlaneCrossingColumn
import ThetLogos.RepTensorTwirl
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Analysis.Matrix.Order

namespace ThetLogos

open Finset

section PosDefFunDef

variable {G : Type*} [Group G]

/-- **Positive-definite function** on a group, in kernel form:
for every finite test family `x : Fin n → G` and every
coefficient family `c : Fin n → ℂ`, the quadratic form of the
kernel `(i, j) ↦ f (x i⁻¹ * x j)` has nonnegative real part. -/
def PosDefFun (f : G → ℂ) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → G, ∀ c : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * f ((x i)⁻¹ * x j) * c j).re

end PosDefFunDef

section ClassProperty

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **The class property of `wordDensity`**: the word density is
invariant under conjugation, `wordDensity ρ (h * g * h⁻¹) =
wordDensity ρ g` — trace cyclicity through `repMatrix`, via the
landed `trace_repMatrix_conj`. No hypothesis on `d` is needed:
the division by `d` is untouched by the conjugation. -/
theorem wordDensity_conj_invariant (g h : G) :
    wordDensity ρ (h * g * h⁻¹) = wordDensity ρ g := by
  unfold wordDensity
  rw [trace_repMatrix_conj]

/-- **Corollary (the plaquette factor is a class function)**:
the single-plaquette factor `f_β(g) = exp (−(β · wordDensity
ρ g))` is constant on conjugacy classes, for every real `β`.
This is the invariance only; positive-definiteness of `f_β`
is **not** asserted here (that assembly is brick A2-1b). -/
theorem plaquetteFactor_classFn (β : ℝ) (g h : G) :
    (fun g => Real.exp (-(β * wordDensity ρ g))) (h * g * h⁻¹)
      = (fun g => Real.exp (-(β * wordDensity ρ g))) g := by
  show Real.exp (-(β * wordDensity ρ (h * g * h⁻¹)))
      = Real.exp (-(β * wordDensity ρ g))
  rw [wordDensity_conj_invariant]

end ClassProperty

section GramKernel

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **The Gram identity for the character**: for unitary `ρ`,
`tr (ρ (x⁻¹ * y)) = tr ((ρ x)ᴴ * ρ y)`, expanded over matrix
entries: the trace is the sum over all entry positions `(a, b)`
of `conj ((ρ x) a b) * (ρ y) a b`. The entry functions
`F a b g = (ρ g) a b` are finite and explicit; this is the
factorization the quadratic-form computation below consumes. -/
theorem trace_repMatrix_inv_mul_gram (x y : G) :
    Matrix.trace (repMatrix ρ (x⁻¹ * y))
      = ∑ a, ∑ b, (starRingEnd ℂ) ((repMatrix ρ x) a b)
          * (repMatrix ρ y) a b := by
  rw [repMatrix_mul, repMatrix_inv]
  calc Matrix.trace (star (repMatrix ρ x) * repMatrix ρ y)
      = ∑ a, (star (repMatrix ρ x) * repMatrix ρ y) a a := by
          simp only [Matrix.trace, Matrix.diag]
    _ = ∑ a, ∑ b, (starRingEnd ℂ) ((repMatrix ρ x) b a)
          * (repMatrix ρ y) b a :=
        Finset.sum_congr rfl fun a _ => by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => by
            rw [Matrix.star_apply, ← starRingEnd_eq_star]
    _ = ∑ a, ∑ b, (starRingEnd ℂ) ((repMatrix ρ x) a b)
          * (repMatrix ρ y) a b :=
        Finset.sum_comm

/-- The trace of the assembled Gram matrix: with
`W = ∑ j, c j • ρ (y j)`, the trace of `star W * W` is exactly
the quadratic form of the kernel
`(i, j) ↦ tr (star (ρ (y i)) * ρ (y j))`. -/
theorem trace_star_sum_repMatrix_eq_quadForm (n : ℕ) (y : Fin n → G)
    (c : Fin n → ℂ) :
    Matrix.trace (star (∑ j, c j • repMatrix ρ (y j))
        * (∑ j, c j • repMatrix ρ (y j)))
      = ∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * Matrix.trace (star (repMatrix ρ (y i)) * repMatrix ρ (y j))
          * c j := by
  have hstar : star (∑ j, c j • repMatrix ρ (y j))
      = ∑ i, (starRingEnd ℂ) (c i) • star (repMatrix ρ (y i)) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [star_smul, starRingEnd_eq_star]
  calc Matrix.trace (star (∑ j, c j • repMatrix ρ (y j))
        * (∑ j, c j • repMatrix ρ (y j)))
      = Matrix.trace ((∑ i, (starRingEnd ℂ) (c i)
            • star (repMatrix ρ (y i)))
          * (∑ j, c j • repMatrix ρ (y j))) := by rw [hstar]
    _ = Matrix.trace (∑ i, ∑ j,
          ((starRingEnd ℂ) (c i) • star (repMatrix ρ (y i)))
            * (c j • repMatrix ρ (y j))) := by
          rw [Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, Matrix.trace
          (((starRingEnd ℂ) (c i) • star (repMatrix ρ (y i)))
            * (c j • repMatrix ρ (y j))) := by
          simp only [Matrix.trace_sum]
    _ = ∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * Matrix.trace (star (repMatrix ρ (y i)) * repMatrix ρ (y j))
          * c j := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          rw [smul_mul_smul, Matrix.trace_smul, smul_eq_mul]
          ring

/-- Conjugation of a represented trace is the trace at the
inverse: `(starRingEnd ℂ) (tr (ρ g)) = tr (ρ g⁻¹)`. -/
theorem star_trace_repMatrix (g : G) :
    (starRingEnd ℂ) (Matrix.trace (repMatrix ρ g))
      = Matrix.trace (repMatrix ρ g⁻¹) := by
  rw [starRingEnd_eq_star, repMatrix_inv,
    Matrix.star_eq_conjTranspose, ← Matrix.trace_conjTranspose]

/-- The real part of a represented trace, as a complex number,
is the average of the traces at `g` and at `g⁻¹`. -/
theorem reTr_eq (g : G) :
    ((Matrix.trace (repMatrix ρ g)).re : ℂ)
      = (Matrix.trace (repMatrix ρ g) + Matrix.trace (repMatrix ρ g⁻¹)) / 2 := by
  have h := RCLike.re_eq_add_conj (Matrix.trace (repMatrix ρ g))
  rw [star_trace_repMatrix] at h
  exact h

/-- **The character kernel is positive-definite**: the function
`g ↦ ((tr ρ g).re : ℂ)` is `PosDefFun`. Proof: at each test
family the quadratic form is the average of the two Gram forms
`tr (star W * W)` and `tr (star W' * W')`, where
`W = ∑ j, c j • ρ (x j)` and `W' = ∑ j, c j • ρ ((x j)⁻¹)`;
by `trace_star_mul_self` each is the sum of the squared norms
of its entries, a nonnegative real number, so the average's
real part is nonnegative. No hypothesis on `d` is needed. -/
theorem reTr_posDefFun :
    PosDefFun (fun g => ((Matrix.trace (repMatrix ρ g)).re : ℂ)) := by
  intro n x c
  show 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i)
      * ((Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ) * c j).re
  have hχ : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
        * Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j)) * c j)
      = Matrix.trace (star (∑ j, c j • repMatrix ρ (x j))
          * (∑ j, c j • repMatrix ρ (x j))) := by
    have h1 : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * Matrix.trace (star (repMatrix ρ (x i)) * repMatrix ρ (x j)) * c j)
        = Matrix.trace (star (∑ j, c j • repMatrix ρ (x j))
            * (∑ j, c j • repMatrix ρ (x j))) :=
      (trace_star_sum_repMatrix_eq_quadForm ρ n x c).symm
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [← repMatrix_inv, ← repMatrix_mul]
  have hχ' : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
        * Matrix.trace (repMatrix ρ ((x j)⁻¹ * x i)) * c j)
      = Matrix.trace (star (∑ j, c j • repMatrix ρ ((x j)⁻¹))
          * (∑ j, c j • repMatrix ρ ((x j)⁻¹))) := by
    have h1 : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * Matrix.trace (star (repMatrix ρ ((x i)⁻¹))
              * repMatrix ρ ((x j)⁻¹)) * c j)
        = Matrix.trace (star (∑ j, c j • repMatrix ρ ((x j)⁻¹))
            * (∑ j, c j • repMatrix ρ ((x j)⁻¹))) :=
      (trace_star_sum_repMatrix_eq_quadForm ρ n (fun i => (x i)⁻¹) c).symm
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    have hstar : star (repMatrix ρ ((x i)⁻¹)) = repMatrix ρ (x i) := by
      rw [repMatrix_inv, star_star]
    have htr : Matrix.trace (star (repMatrix ρ ((x i)⁻¹))
          * repMatrix ρ ((x j)⁻¹))
        = Matrix.trace (repMatrix ρ ((x j)⁻¹ * x i)) := by
      calc Matrix.trace (star (repMatrix ρ ((x i)⁻¹))
            * repMatrix ρ ((x j)⁻¹))
          = Matrix.trace (repMatrix ρ (x i) * repMatrix ρ ((x j)⁻¹)) := by
              rw [hstar]
        _ = Matrix.trace (repMatrix ρ ((x j)⁻¹) * repMatrix ρ (x i)) :=
              Matrix.trace_mul_comm _ _
        _ = Matrix.trace (repMatrix ρ ((x j)⁻¹ * x i)) := by
              rw [← repMatrix_mul]
    rw [htr]
  have hS : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
        * ((Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ) * c j)
      = (Matrix.trace (star (∑ j, c j • repMatrix ρ (x j))
            * (∑ j, c j • repMatrix ρ (x j)))
          + Matrix.trace (star (∑ j, c j • repMatrix ρ ((x j)⁻¹))
            * (∑ j, c j • repMatrix ρ ((x j)⁻¹)))) / 2 := by
    rw [← hχ, ← hχ']
    have hterm : ∀ i j : Fin n,
        (starRingEnd ℂ) (c i)
          * ((Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ) * c j
        = ((starRingEnd ℂ) (c i)
              * Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j)) * c j
            + (starRingEnd ℂ) (c i)
              * Matrix.trace (repMatrix ρ ((x j)⁻¹ * x i)) * c j) / 2 := by
      intro i j
      have hg : ((x i)⁻¹ * x j)⁻¹ = (x j)⁻¹ * x i := by
        rw [mul_inv_rev, inv_inv]
      rw [reTr_eq, hg]
      ring
    calc (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * ((Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ) * c j)
        = ∑ i, ∑ j, (((starRingEnd ℂ) (c i)
              * Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j)) * c j
            + (starRingEnd ℂ) (c i)
              * Matrix.trace (repMatrix ρ ((x j)⁻¹ * x i)) * c j) / 2) :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => hterm i j
      _ = ((∑ i, ∑ j, (starRingEnd ℂ) (c i)
              * Matrix.trace (repMatrix ρ ((x i)⁻¹ * x j)) * c j)
            + (∑ i, ∑ j, (starRingEnd ℂ) (c i)
              * Matrix.trace (repMatrix ρ ((x j)⁻¹ * x i)) * c j)) / 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hS, trace_star_mul_self, trace_star_mul_self]
  have hcast : (((∑ a, ∑ b, ‖(∑ j, c j • repMatrix ρ (x j)) a b‖ ^ 2 : ℝ) : ℂ)
        + ((∑ a, ∑ b, ‖(∑ j, c j • repMatrix ρ ((x j)⁻¹)) a b‖ ^ 2 : ℝ) : ℂ)) / 2
      = (((∑ a, ∑ b, ‖(∑ j, c j • repMatrix ρ (x j)) a b‖ ^ 2
          + ∑ a, ∑ b, ‖(∑ j, c j • repMatrix ρ ((x j)⁻¹)) a b‖ ^ 2) / 2 : ℝ) : ℂ) := by
    have h2 : ((2 : ℝ) : ℂ) = 2 := by norm_cast
    rw [← h2, ← Complex.ofReal_add, ← Complex.ofReal_div]
  rw [hcast, Complex.ofReal_re]
  refine div_nonneg (add_nonneg ?_ ?_) (by norm_num)
  · exact Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => by positivity
  · exact Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => by positivity

end GramKernel

/-
# Part 2 (Brick A2-1b): closure theory of `PosDefFun` and the
plaquette-factor theorem

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Dials **0/4**.

This part proves the closure theory of `PosDefFun` (sums,
nonnegative real multiples, the constant function `1`,
products, powers, and the exponential series) and assembles
them into the headline: the single-plaquette factor
`f_β(g) = Real.exp (−(β · wordDensity ρ g))` is a
positive-definite class function at general `(G, ρ)`, `β ≥ 0`.
This closes brick A2-1 **only**: it does not assemble Route B,
does not prove `𝒜 ⪰ 0` or clause (a), and moves no dial.
-/

section Closure

variable {G : Type*} [Group G]

/-- **Closure under sums**: sums of positive-definite
functions are positive-definite — the two quadratic forms
add, and the real part of a sum is the sum of the real
parts. -/
theorem PosDefFun.add {f g : G → ℂ} (hf : PosDefFun f)
    (hg : PosDefFun g) : PosDefFun (fun h => f h + g h) := by
  intro n x c
  have hsum : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
        * (f ((x i)⁻¹ * x j) + g ((x i)⁻¹ * x j)) * c j)
      = (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * f ((x i)⁻¹ * x j) * c j)
        + (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * g ((x i)⁻¹ * x j) * c j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  show 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i)
      * (f ((x i)⁻¹ * x j) + g ((x i)⁻¹ * x j)) * c j).re
  rw [hsum, Complex.add_re]
  exact add_nonneg (hf n x c) (hg n x c)

/-- **Closure under nonnegative real multiples**: for
`0 ≤ a`, the function `g ↦ (a : ℂ) * f g` is
positive-definite — its quadratic form is `(a : ℂ)` times
the form of `f`, and the real part scales by `a`. -/
theorem PosDefFun.smul_nonneg {f : G → ℂ} (hf : PosDefFun f)
    {a : ℝ} (ha : 0 ≤ a) :
    PosDefFun (fun h => (a : ℂ) * f h) := by
  intro n x c
  have hsum : (∑ i, ∑ j, (starRingEnd ℂ) (c i)
        * ((a : ℂ) * f ((x i)⁻¹ * x j)) * c j)
      = (a : ℂ) * (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * f ((x i)⁻¹ * x j) * c j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  show 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i)
      * ((a : ℂ) * f ((x i)⁻¹ * x j)) * c j).re
  rw [hsum, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact mul_nonneg ha (hf n x c)

/-- **The constant function `1` is positive-definite**: its
quadratic form is `conj (∑ j, c j) * (∑ j, c j)`, whose real
part is the squared norm of `∑ j, c j`. -/
theorem posDefFun_one : PosDefFun (fun _ : G => (1 : ℂ)) := by
  intro n x c
  have hsum : (∑ i, ∑ j, (starRingEnd ℂ) (c i) * (1 : ℂ) * c j)
      = (starRingEnd ℂ) (∑ i, c i) * (∑ j, c j) := by
    calc (∑ i, ∑ j, (starRingEnd ℂ) (c i) * (1 : ℂ) * c j)
        = ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          rw [mul_one]
      _ = (∑ i, (starRingEnd ℂ) (c i)) * (∑ j, c j) :=
          (Finset.sum_mul_sum ..).symm
      _ = (starRingEnd ℂ) (∑ i, c i) * (∑ j, c j) := by
          rw [map_sum]
  show 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * (1 : ℂ) * c j).re
  rw [hsum, starRingEnd_eq_star, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end Closure

open scoped ComplexOrder

section Product

variable {G : Type*} [Group G]

/-- **The Gram matrix of a Hermitian-kernel positive-definite
function is positive semidefinite.** The Hermitian-kernel
hypothesis `hfH` — `conj (f (g⁻¹)) = f g` — is genuinely
needed here, and this is the exact seam of this brick:
`PosDefFun` as defined in Part 1 controls only the real part
of the quadratic form, while Mathlib's `Matrix.PosSemidef`
(the input of `Matrix.PosSemidef.hadamard`) is by definition
`IsHermitian ∧` the form condition. The bare product
statement for arbitrary `PosDefFun` functions is in fact
false under the real-part-only definition — the constant
function `g ↦ Complex.I` is `PosDefFun` (its form is
`Complex.I * ‖∑ j, c j‖²`, of real part `0`), while its
square, the constant function `-1`, is not — so the product
closure below is carried in Hermitian-kernel form, which is
the form the character kernel of Part 1 satisfies. The
nonnegativity clause: the form of the Gram matrix is
exactly the `PosDefFun` form (real part `≥ 0` by `hf`), and
its imaginary part vanishes because the form equals its
own conjugate, by `hfH` and reindexing `i ↔ j`. -/
theorem PosDefFun.gram_posSemidef {f : G → ℂ} (hf : PosDefFun f)
    (hfH : ∀ g, (starRingEnd ℂ) (f g⁻¹) = f g) (n : ℕ)
    (x : Fin n → G) :
    Matrix.PosSemidef (Matrix.of fun i j => f ((x i)⁻¹ * x j)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    have h : (x j)⁻¹ * x i = ((x i)⁻¹ * x j)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [h, ← starRingEnd_eq_star]
    exact hfH _
  · intro v
    have hS : dotProduct (star v)
          (Matrix.mulVec (Matrix.of fun i j => f ((x i)⁻¹ * x j)) v)
        = ∑ i, ∑ j, (starRingEnd ℂ) (v i)
            * f ((x i)⁻¹ * x j) * v j := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply,
        Finset.mul_sum, starRingEnd_eq_star, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hS]
    refine RCLike.nonneg_iff.mpr ⟨hf n x v, ?_⟩
    show (∑ i, ∑ j, (starRingEnd ℂ) (v i)
        * f ((x i)⁻¹ * x j) * v j).im = 0
    have hterm : ∀ i j : Fin n,
        (starRingEnd ℂ) ((starRingEnd ℂ) (v i)
            * f ((x i)⁻¹ * x j) * v j)
          = (starRingEnd ℂ) (v j) * f ((x j)⁻¹ * x i) * v i := by
      intro i j
      have h1 : (starRingEnd ℂ) ((starRingEnd ℂ) (v i)
            * f ((x i)⁻¹ * x j) * v j)
          = v i * (starRingEnd ℂ) (f ((x i)⁻¹ * x j))
            * (starRingEnd ℂ) (v j) := by
        rw [map_mul, map_mul, starRingEnd_self_apply]
      rw [h1]
      have h2 : (x i)⁻¹ * x j = ((x j)⁻¹ * x i)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
      have h3 : (starRingEnd ℂ) (f ((x i)⁻¹ * x j))
          = f ((x j)⁻¹ * x i) := by
        rw [h2]
        exact hfH _
      rw [h3]
      ring
    have hconj : (starRingEnd ℂ)
          (∑ i, ∑ j, (starRingEnd ℂ) (v i)
            * f ((x i)⁻¹ * x j) * v j)
        = ∑ i, ∑ j, (starRingEnd ℂ) (v i)
            * f ((x i)⁻¹ * x j) * v j := by
      calc (starRingEnd ℂ)
            (∑ i, ∑ j, (starRingEnd ℂ) (v i)
              * f ((x i)⁻¹ * x j) * v j)
          = ∑ i, ∑ j, (starRingEnd ℂ) ((starRingEnd ℂ) (v i)
              * f ((x i)⁻¹ * x j) * v j) := by
            simp only [map_sum]
        _ = ∑ i, ∑ j, (starRingEnd ℂ) (v j)
              * f ((x j)⁻¹ * x i) * v i :=
            Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => hterm i j
        _ = ∑ i, ∑ j, (starRingEnd ℂ) (v i)
              * f ((x i)⁻¹ * x j) * v j := Finset.sum_comm
    have him := congrArg Complex.im hconj
    rw [starRingEnd_eq_star, Complex.star_def, Complex.conj_im]
      at him
    linarith

/-- **Closure under products, Hermitian-kernel form**: the
product of two positive-definite functions whose kernels
are Hermitian (`conj (f (g⁻¹)) = f g`, and likewise for the
second factor) is positive-definite. The Gram matrix of the
product is the Hadamard (entrywise) product of the two Gram
matrices, and Mathlib's Schur product theorem
(`Matrix.PosSemidef.hadamard`, the same step the corpus
walks in `ThermalPreCompensation`) closes it. The bare
statement without the Hermitian-kernel hypotheses is false
under Part 1's real-part-only definition — see
`PosDefFun.gram_posSemidef`. -/
theorem PosDefFun.mul {f g : G → ℂ} (hf : PosDefFun f)
    (hg : PosDefFun g)
    (hfH : ∀ h, (starRingEnd ℂ) (f h⁻¹) = f h)
    (hgH : ∀ h, (starRingEnd ℂ) (g h⁻¹) = g h) :
    PosDefFun (fun h => f h * g h) := by
  intro n x c
  have hH := (hf.gram_posSemidef hfH n x).hadamard
    (hg.gram_posSemidef hgH n x)
  have hnn := hH.re_dotProduct_nonneg c
  have hsum : dotProduct (star c)
        (Matrix.mulVec (Matrix.hadamard (Matrix.of fun i j => f ((x i)⁻¹ * x j))
          (Matrix.of fun i j => g ((x i)⁻¹ * x j))) c)
      = ∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * (f ((x i)⁻¹ * x j) * g ((x i)⁻¹ * x j)) * c j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply,
      Matrix.hadamard_apply, Finset.mul_sum, starRingEnd_eq_star,
      Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  show 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i)
      * (f ((x i)⁻¹ * x j) * g ((x i)⁻¹ * x j)) * c j).re
  rw [← hsum]
  exact hnn

/-- **Closure under powers, Hermitian-kernel form**: every
power of a Hermitian-kernel positive-definite function is
positive-definite, by induction through `PosDefFun.mul`
(the Hermitian-kernel property itself is preserved under
powers, by `map_pow`). The base case is `posDefFun_one`. -/
theorem PosDefFun.pow {f : G → ℂ} (hf : PosDefFun f)
    (hfH : ∀ h, (starRingEnd ℂ) (f h⁻¹) = f h) (k : ℕ) :
    PosDefFun (fun h => f h ^ k) := by
  induction k with
  | zero =>
      simpa using (posDefFun_one : PosDefFun (fun _ : G => (1 : ℂ)))
  | succ k ih =>
      have hpowH : ∀ h, (starRingEnd ℂ) ((f h⁻¹) ^ k)
          = (f h) ^ k := fun h => by rw [map_pow, hfH]
      simpa only [pow_succ] using ih.mul hf hpowH hfH

end Product

open scoped Topology

section ExpSeries

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **The character kernel is Hermitian**: conjugating the
(real) value of `g ↦ ((tr ρ g).re : ℂ)` at `g⁻¹` returns its
value at `g` — the trace at `g⁻¹` is the conjugate of the
trace at `g` (`star_trace_repMatrix`, Part 1), and
conjugation fixes both the real part and real casts. This
is the hypothesis `PosDefFun.mul` / `PosDefFun.pow` consume. -/
theorem reTr_kernel_hermitian :
    ∀ g, (starRingEnd ℂ)
        (((Matrix.trace (repMatrix ρ g⁻¹)).re : ℂ))
      = ((Matrix.trace (repMatrix ρ g)).re : ℂ) := by
  intro g
  have hre : (Matrix.trace (repMatrix ρ g⁻¹)).re
      = (Matrix.trace (repMatrix ρ g)).re := by
    have h1 := congrArg Complex.re (star_trace_repMatrix ρ g)
    rw [starRingEnd_eq_star, Complex.star_def, Complex.conj_re]
      at h1
    exact h1.symm
  rw [hre, starRingEnd_eq_star, Complex.star_def,
    Complex.conj_ofReal]

/-- **Exponential closure for the character kernel**: for
`0 ≤ a`, the function `g ↦ (Real.exp (a * (tr ρ g).re) : ℂ)`
is positive-definite. Proof: the partial sums of the
exponential series are positive-definite (nonnegative real
multiples of powers of the character kernel, by
`PosDefFun.pow` and `PosDefFun.smul_nonneg`, summed by
`PosDefFun.add`), they converge pointwise to the
exponential (the real exponential series, cast to `ℂ`), and
the predicate's inequality passes to the limit because each
test form is a finite sum of values. -/
theorem reTr_exp_posDefFun {a : ℝ} (ha : 0 ≤ a) :
    PosDefFun (fun g =>
      (Real.exp (a * (Matrix.trace (repMatrix ρ g)).re) : ℂ)) := by
  have hpow : ∀ k : ℕ, PosDefFun (fun g =>
      (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
        * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k) := by
    intro k
    have hnn : (0 : ℝ) ≤ a ^ k / (Nat.factorial k : ℝ) :=
      div_nonneg (pow_nonneg ha k) (Nat.cast_nonneg _)
    have hpk : PosDefFun (fun g =>
        (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k) :=
      (reTr_posDefFun ρ).pow (reTr_kernel_hermitian ρ) k
    exact hpk.smul_nonneg hnn
  have hpart : ∀ N : ℕ, PosDefFun (fun g =>
      ∑ k ∈ Finset.range N, (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
        * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k) := by
    intro N
    induction N with
    | zero =>
        intro n x c
        simp
    | succ N ih =>
        have hfun : (fun g => ∑ k ∈ Finset.range (N + 1),
              (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
                * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k)
            = (fun g => (∑ k ∈ Finset.range N,
                  (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
                    * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k)
                + (Complex.ofReal (a ^ N / (Nat.factorial N : ℝ)))
                  * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ N) :=
          funext fun g => Finset.sum_range_succ _ _
        rw [hfun]
        exact ih.add (hpow N)
  have hpoint : ∀ g : G, Filter.Tendsto (fun N =>
        ∑ k ∈ Finset.range N, (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
          * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k)
      Filter.atTop
      (𝓝 (Real.exp (a * (Matrix.trace (repMatrix ρ g)).re) : ℂ)) := by
    intro g
    have hid : ∀ N : ℕ, (∑ k ∈ Finset.range N,
          (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
            * (((Matrix.trace (repMatrix ρ g)).re : ℂ)) ^ k)
        = (Complex.ofReal (∑ k ∈ Finset.range N,
            (a * (Matrix.trace (repMatrix ρ g)).re) ^ k
              / (Nat.factorial k : ℝ))) := by
      intro N
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hreal : (a ^ k / (Nat.factorial k : ℝ))
            * ((Matrix.trace (repMatrix ρ g)).re) ^ k
          = (a * (Matrix.trace (repMatrix ρ g)).re) ^ k
            / (Nat.factorial k : ℝ) := by
        rw [mul_pow, div_mul_eq_mul_div]
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, hreal]
    simp_rw [hid]
    have hR : Filter.Tendsto (fun N =>
          ∑ k ∈ Finset.range N,
            (a * (Matrix.trace (repMatrix ρ g)).re) ^ k
              / (Nat.factorial k : ℝ))
        Filter.atTop
        (𝓝 (Real.exp (a * (Matrix.trace (repMatrix ρ g)).re))) := by
      have hs : HasSum (fun k =>
            (a * (Matrix.trace (repMatrix ρ g)).re) ^ k
              / (Nat.factorial k : ℝ))
          (Real.exp (a * (Matrix.trace (repMatrix ρ g)).re)) := by
        have h := NormedSpace.expSeries_div_hasSum_exp_of_mem_ball
          (𝕂 := ℝ) (a * (Matrix.trace (repMatrix ρ g)).re)
          ((NormedSpace.expSeries_radius_eq_top ℝ ℝ).symm ▸
            edist_lt_top _ _)
        simpa only [Real.exp_eq_exp_ℝ] using h
      exact hs.tendsto_sum_nat
    exact (Complex.continuous_ofReal.tendsto _).comp hR
  intro n x c
  have hge : ∀ N : ℕ, 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i)
        * ((∑ k ∈ Finset.range N, (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
            * (((Matrix.trace
                (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ)) ^ k))
          * c j).re :=
    fun N => hpart N n x c
  have hlim : Filter.Tendsto (fun N =>
        ∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * ((∑ k ∈ Finset.range N, (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
              * (((Matrix.trace
                  (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ)) ^ k))
            * c j)
      Filter.atTop
      (𝓝 (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * ((Real.exp
              (a * (Matrix.trace
                (repMatrix ρ ((x i)⁻¹ * x j))).re) : ℂ))
            * c j)) := by
    refine tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => ?_
    exact ((hpoint ((x i)⁻¹ * x j)).const_mul _).mul_const _
  have hre : Filter.Tendsto (fun N =>
        (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * ((∑ k ∈ Finset.range N, (Complex.ofReal (a ^ k / (Nat.factorial k : ℝ)))
              * (((Matrix.trace
                  (repMatrix ρ ((x i)⁻¹ * x j))).re : ℂ)) ^ k))
            * c j).re)
      Filter.atTop
      (𝓝 (∑ i, ∑ j, (starRingEnd ℂ) (c i)
          * ((Real.exp
              (a * (Matrix.trace
                (repMatrix ρ ((x i)⁻¹ * x j))).re) : ℂ))
            * c j).re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  exact ge_of_tendsto' hre hge

/-- **The headline of brick A2-1 (A2-1b assembly)**: for
`0 ≤ β`, the single-plaquette factor
`f_β(g) = Real.exp (−(β · wordDensity ρ g))`, read in `ℂ`,
is a positive-definite function on `G` at general `(G, ρ)`.
Assembly: `wordDensity ρ g = 1 − (tr ρ g).re / d`, so
`f_β = e^{−β} · exp ((β/d) · (tr ρ ·).re)`; the exponential
factor is positive-definite by `reTr_exp_posDefFun` at the
nonnegative scalar `β/d`, and the constant factor
`e^{−β} > 0` is a nonnegative real multiple. **No hypothesis
on `d` is carried**: the exponent identity
`−(β · (1 − r/d)) = −β + (β/d) · r` is a field identity in
the atoms `β`, `r`, `(d : ℝ)⁻¹` and closes by `ring` at
every `d`, including `d = 0` (where both sides reduce to
`−β`, the division being by the cast of `d` as a real
number, never inverted under a side condition) — exactly
the discipline of Part 1, which needed no `hd` either. -/
theorem plaquetteFactor_posDefFun {β : ℝ} (hβ : 0 ≤ β) :
    PosDefFun (fun g =>
      (Real.exp (-(β * wordDensity ρ g)) : ℂ)) := by
  have hβd : (0 : ℝ) ≤ β / (d : ℝ) :=
    div_nonneg hβ (Nat.cast_nonneg d)
  have hscale := (reTr_exp_posDefFun ρ hβd).smul_nonneg
    (Real.exp_pos (-β)).le
  have hfun : (fun g => (Real.exp (-(β * wordDensity ρ g)) : ℂ))
      = (fun g => ((Real.exp (-β) : ℝ) : ℂ)
          * ((Real.exp ((β / (d : ℝ))
              * (Matrix.trace (repMatrix ρ g)).re) : ℝ) : ℂ)) := by
    funext g
    have hexp_eq : Real.exp (-(β * wordDensity ρ g))
        = Real.exp (-β)
          * Real.exp ((β / (d : ℝ))
              * (Matrix.trace (repMatrix ρ g)).re) := by
      rw [← Real.exp_add]
      congr 1
      unfold wordDensity
      ring
    rw [hexp_eq, Complex.ofReal_mul]
  rw [hfun]
  exact hscale

/-- **Brick A2-1, packaged**: the single-plaquette factor
`f_β` is a positive-definite class function at general
`(G, ρ)`, for every `0 ≤ β` — the conjunction of
`plaquetteFactor_posDefFun` (A2-1b) with
`plaquetteFactor_classFn` (A2-1a). This closes A2-1 only:
no Route B assembly, no `𝒜 ⪰ 0`, no clause (a); dials 0/4. -/
theorem plaquetteFactor_posDef_classFn {β : ℝ} (hβ : 0 ≤ β) :
    PosDefFun (fun g =>
        (Real.exp (-(β * wordDensity ρ g)) : ℂ))
      ∧ ∀ g h : G,
          (Real.exp (-(β * wordDensity ρ (h * g * h⁻¹))) : ℂ)
            = (Real.exp (-(β * wordDensity ρ g)) : ℂ) :=
  ⟨plaquetteFactor_posDefFun ρ hβ,
   fun g h => congrArg (fun r : ℝ => (r : ℂ))
     (plaquetteFactor_classFn ρ β g h)⟩

end ExpSeries

end ThetLogos
