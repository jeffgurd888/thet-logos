import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic

open scoped Matrix

/-!
# ThetLogos.TritGrading — balanced-ternary substrate and ℤ₃-gradings (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 background algebra**: a three-element
  type carrying the `ℤ/3` addition table, submodule-valued `ℤ₃`-gradings
  of matrix algebras, the block-offset example, conjugation covariance of
  the commutator and the adjoint action, and the squared-commutator trace
  bound for Hermitian matrices.
- It is **not** mass-gap content, **not** a Chern character, **not**
  physics. Names are the plain ones: the commutator is `commutator`, the
  adjoint action is `ad`. No curvature / connection / topology language
  appears, because none is proved.
- Provenance: this file replaces, from scratch, a pasted AI-generated
  "Theta Framework" draft that failed the gauntlet of 2026-10-15 (it did
  not compile; its grading was a bare predicate admitting degenerate
  models, so its graded theorems did not follow; it carried three
  `sorry`s and a truncated "complete" version). The salvageable
  statements were identified by the gauntlet and are re-derived here in
  project Mathlib. The assumed-`Δ` energy toy from that draft is
  deliberately excluded: the gap there was an input, not a theorem.
- Zero sorrys, no new axioms.
-/

namespace ThetLogos

/-! ## §1. The trit type and its arithmetic -/

/-- The three-element balanced-ternary type: `-1`, `0`, `+1`. -/
inductive Trit
  | neg : Trit
  | zero : Trit
  | pos : Trit
  deriving DecidableEq, Repr

namespace Trit

instance : Fintype Trit where
  elems := {neg, zero, pos}
  complete := by
    intro x
    cases x <;> simp

/-- The integer reading of a trit: `neg ↦ -1`, `zero ↦ 0`, `pos ↦ 1`. -/
def toInt : Trit → ℤ
  | neg => -1
  | zero => 0
  | pos => 1

/-- Balanced-ternary negation (sign flip). -/
def negate : Trit → Trit
  | neg => pos
  | zero => zero
  | pos => neg

instance : Neg Trit := ⟨negate⟩

/-- Balanced-ternary addition: the `ℤ/3` table under
`neg ↦ -1`, `zero ↦ 0`, `pos ↦ 1`. -/
def add : Trit → Trit → Trit
  | zero, t => t
  | t, zero => t
  | neg, neg => pos
  | neg, pos => zero
  | pos, neg => zero
  | pos, pos => neg

instance : Add Trit := ⟨add⟩

theorem add_assoc (a b c : Trit) : a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_comm (a b : Trit) : a + b = b + a := by
  cases a <;> cases b <;> rfl

theorem zero_add (a : Trit) : zero + a = a := by
  cases a <;> rfl

theorem add_zero (a : Trit) : a + zero = a := by
  cases a <;> rfl

theorem neg_add_cancel (a : Trit) : -a + a = zero := by
  cases a <;> rfl

theorem add_neg_cancel (a : Trit) : a + -a = zero := by
  cases a <;> rfl

theorem neg_neg (a : Trit) : - -a = a := by
  cases a <;> rfl

theorem toInt_neg (a : Trit) : toInt (-a) = -toInt a := by
  cases a <;> rfl

/-- The reading of a trit in `ZMod 3`: `neg ↦ 2`, `zero ↦ 0`, `pos ↦ 1`.
This agrees with `toInt` read mod 3 (see `toInt_cast_zmod`). -/
def toZMod3 : Trit → ZMod 3
  | neg => 2
  | zero => 0
  | pos => 1

theorem toZMod3_add (a b : Trit) : toZMod3 (a + b) = toZMod3 a + toZMod3 b := by
  cases a <;> cases b <;> decide

theorem toInt_cast_zmod (t : Trit) : (toInt t : ZMod 3) = toZMod3 t := by
  cases t <;> decide

/-- `toInt` respects the addition table modulo 3, in cast form. -/
theorem toInt_add (a b : Trit) :
    ((toInt (a + b) : ℤ) : ZMod 3) = ((toInt a + toInt b : ℤ) : ZMod 3) := by
  rw [toInt_cast_zmod, Int.cast_add, toInt_cast_zmod, toInt_cast_zmod, toZMod3_add]

/-- `toInt` respects the addition table modulo 3. -/
theorem toInt_add_modEq (a b : Trit) :
    toInt (a + b) ≡ toInt a + toInt b [ZMOD 3] :=
  (ZMod.intCast_eq_intCast_iff _ _ _).mp (toInt_add a b)

theorem toZMod3_injective : Function.Injective toZMod3 := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

/-- The inverse reading: `0 ↦ zero`, `1 ↦ pos`, `2 ↦ neg`. -/
def ofZMod3 (x : ZMod 3) : Trit :=
  if x = 0 then zero else if x = 1 then pos else neg

theorem ofZMod3_toZMod3 (t : Trit) : ofZMod3 (toZMod3 t) = t := by
  cases t <;> decide

theorem toZMod3_ofZMod3 (x : ZMod 3) : toZMod3 (ofZMod3 x) = x := by
  have h : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  rcases h x with rfl | rfl | rfl <;> decide

/-- The trit type, with its addition, is additively equivalent to `ZMod 3`.
This is the precise content of "the trit table is `ℤ₃` addition". -/
def addEquivZMod3 : Trit ≃+ ZMod 3 where
  toFun := toZMod3
  invFun := ofZMod3
  left_inv := ofZMod3_toZMod3
  right_inv := toZMod3_ofZMod3
  map_add' := toZMod3_add

end Trit

/-! ## §2. Commutator and adjoint action: covariance -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator of two matrices: `A * B - B * A`. Plain name for a
plain object; it is not a curvature. -/
def commutator (A B : Matrix n n ℂ) : Matrix n n ℂ := A * B - B * A

/-- The adjoint action of `A` on `X`: `A * X - X * A`. Not a covariant
derivative: there is no differential term. -/
def ad (A X : Matrix n n ℂ) : Matrix n n ℂ := A * X - X * A

/-- Conjugation distributes over a product, one inverse at a time. -/
theorem conj_mul_conj (U U_inv A B : Matrix n n ℂ) (h : U_inv * U = 1) :
    (U * A * U_inv) * (U * B * U_inv) = U * A * B * U_inv := by
  calc (U * A * U_inv) * (U * B * U_inv)
      = U * A * (U_inv * U) * B * U_inv := by noncomm_ring
    _ = U * A * B * U_inv := by rw [h]; noncomm_ring

/-- The commutator is conjugation-covariant. -/
theorem commutator_conj (U U_inv A B : Matrix n n ℂ) (h : U_inv * U = 1) :
    commutator (U * A * U_inv) (U * B * U_inv) = U * commutator A B * U_inv := by
  simp only [commutator]
  rw [conj_mul_conj U U_inv A B h, conj_mul_conj U U_inv B A h]
  noncomm_ring

/-- The adjoint action is conjugation-covariant. -/
theorem ad_conj (U U_inv A X : Matrix n n ℂ) (h : U_inv * U = 1) :
    ad (U * A * U_inv) (U * X * U_inv) = U * ad A X * U_inv := by
  simp only [ad]
  rw [conj_mul_conj U U_inv A X h, conj_mul_conj U U_inv X A h]
  noncomm_ring

omit [DecidableEq n] in
theorem commutator_self (A : Matrix n n ℂ) : commutator A A = 0 := by
  simp [commutator]

omit [DecidableEq n] in
theorem commutator_antisymm (A B : Matrix n n ℂ) :
    commutator A B = -commutator B A := by
  simp only [commutator, neg_sub]

omit [DecidableEq n] in
/-- The commutator of two Hermitian matrices is skew-Hermitian. -/
theorem commutator_conjTranspose {A B : Matrix n n ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (commutator A B)ᴴ = -commutator A B := by
  simp only [commutator, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA, hB,
    neg_sub]

/-! ## §3. A real grading structure: submodule-valued

The pasted draft's grading was a bare predicate with only a multiplication
rule; `IsGraded := fun _ _ => True` satisfies it, so its "graded"
theorems did not follow. Here each homogeneous component is a `Submodule`,
which supplies zero, additive, and scalar closure for free, and the
multiplication rule is the only axiom. -/

/-- A `ℤ₃`-grading of the matrix algebra `Matrix ι ι ℂ`: a `ℂ`-submodule
of homogeneous matrices for each trit grade, with multiplication respecting
the trit addition table. -/
structure TritGrading (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The homogeneous component of grade `g`. -/
  component : Trit → Submodule ℂ (Matrix ι ι ℂ)
  /-- Multiplication of homogeneous elements lands in the summed grade. -/
  mul_mem : ∀ (g₁ g₂ : Trit) {A B : Matrix ι ι ℂ},
    A ∈ component g₁ → B ∈ component g₂ → A * B ∈ component (g₁ + g₂)

namespace TritGrading

/-- Subtraction closure within a grade (inherited from the submodule). -/
theorem sub_mem (G : TritGrading n) {g : Trit} {A B : Matrix n n ℂ}
    (hA : A ∈ G.component g) (hB : B ∈ G.component g) : A - B ∈ G.component g :=
  (G.component g).sub_mem hA hB

/-- The commutator of homogeneous elements is homogeneous of the summed
grade. This is one of the statements the pasted draft could not prove;
here it follows from `mul_mem`, commutativity of the trit table, and
submodule subtraction closure. -/
theorem commutator_mem (G : TritGrading n) {g₁ g₂ : Trit} {A B : Matrix n n ℂ}
    (hA : A ∈ G.component g₁) (hB : B ∈ G.component g₂) :
    commutator A B ∈ G.component (g₁ + g₂) := by
  have hAB : A * B ∈ G.component (g₁ + g₂) := G.mul_mem g₁ g₂ hA hB
  have hBA : B * A ∈ G.component (g₁ + g₂) := by
    have h := G.mul_mem g₂ g₁ hB hA
    rwa [Trit.add_comm g₂ g₁] at h
  exact (G.component _).sub_mem hAB hBA

/-- The adjoint action of a grade-`zero` element preserves every grade.
The second statement the pasted draft could not prove; it follows the
same way, using that `zero` is the additive identity of the trit table. -/
theorem ad_mem (G : TritGrading n) {g : Trit} {A X : Matrix n n ℂ}
    (hA : A ∈ G.component Trit.zero) (hX : X ∈ G.component g) :
    ad A X ∈ G.component g := by
  have hAX : A * X ∈ G.component g := by
    have h := G.mul_mem Trit.zero g hA hX
    rwa [Trit.zero_add] at h
  have hXA : X * A ∈ G.component g := by
    have h := G.mul_mem g Trit.zero hX hA
    rwa [Trit.add_zero] at h
  exact (G.component _).sub_mem hAX hXA

end TritGrading

/-! ## §4. The block-offset instance

Matrices indexed by `Trit × n`: the grade-`g` component is the submodule
of block matrices supported where the column block equals the row block
shifted by `g`. -/

/-- The grade-`g` block component: matrices over `Trit × n` vanishing
outside the block diagonal offset by `g`. -/
def blockComponent (g : Trit) : Submodule ℂ (Matrix (Trit × n) (Trit × n) ℂ) where
  carrier := {M | ∀ (i j : Trit) (r k : n), j ≠ i + g → M (i, r) (j, k) = 0}
  zero_mem' := by
    intro i j r k _
    simp
  add_mem' := by
    intro A B hA hB i j r k hij
    simp only [Matrix.add_apply, hA i j r k hij, hB i j r k hij, add_zero]
  smul_mem' := by
    intro c A hA i j r k hij
    simp only [Matrix.smul_apply, hA i j r k hij, smul_eq_mul, mul_zero]

omit [Fintype n] [DecidableEq n] in
theorem mem_blockComponent {g : Trit} {M : Matrix (Trit × n) (Trit × n) ℂ} :
    M ∈ blockComponent g ↔
      ∀ (i j : Trit) (r k : n), j ≠ i + g → M (i, r) (j, k) = 0 :=
  Iff.rfl

/-- The block-offset components assemble into a `TritGrading`. The
multiplication rule is the pasted draft's headline block-grading claim,
proved here against the submodule-valued definition. -/
def blockGrading : TritGrading (Trit × n) where
  component := blockComponent
  mul_mem := by
    intro g₁ g₂ A B hA hB
    rw [mem_blockComponent] at hA hB ⊢
    intro i j r k hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    rintro ⟨m, p⟩ -
    by_cases hm : m = i + g₁
    · have hmj : j ≠ m + g₂ := by
        have hsum : m + g₂ = i + (g₁ + g₂) := by
          rw [hm]
          exact Trit.add_assoc i g₁ g₂
        rw [hsum]
        exact hij
      rw [hB m j p k hmj, mul_zero]
    · rw [hA i m r p hm, zero_mul]

/-! ## §5. The squared-commutator trace bound

For Hermitian `A B`, the commutator `C = [A, B]` is skew-Hermitian, so
`C * C = -(Cᴴ * C)` and `trace (Cᴴ * C)` is the Frobenius norm squared of
`C`, a non-negative real. Hence `(trace (C * C)).re ≤ 0`. This is
elementary linear algebra about `trace (Cᴴ * C)`; the quantity
`trace (commutator A B * commutator A B)` is **not** a Chern character
(no bundle, no cycle, no normalization is involved) and is not named as
one. -/

omit [DecidableEq n] in
/-- `trace (Cᴴ * C)` is the Frobenius norm squared of `C`, as a real
number; in particular its real part is non-negative. -/
theorem trace_conjTranspose_mul_self_re_nonneg (C : Matrix n n ℂ) :
    0 ≤ (Matrix.trace (Cᴴ * C)).re := by
  have hstar : ∀ z : ℂ, star z = starRingEnd ℂ z := fun z => congrFun Complex.star_def z
  have htrace : Matrix.trace (Cᴴ * C)
      = ((∑ i, ∑ j, Complex.normSq (C j i) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [Matrix.trace, Matrix.diag_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.ofReal_sum, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_apply, hstar, mul_comm (starRingEnd ℂ (C j i)) (C j i),
      Complex.mul_conj]
  rw [htrace, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

omit [DecidableEq n] in
/-- The squared commutator of two Hermitian matrices has non-positive
real trace. Honest name: `trace_commutator_sq_nonpos`. -/
theorem trace_commutator_sq_nonpos {A B : Matrix n n ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (Matrix.trace (commutator A B * commutator A B)).re ≤ 0 := by
  have hskew : (commutator A B)ᴴ = -commutator A B := commutator_conjTranspose hA hB
  have hsq : commutator A B * commutator A B
      = -((commutator A B)ᴴ * commutator A B) := by
    rw [hskew, neg_mul, neg_neg]
  rw [hsq, Matrix.trace_neg, Complex.neg_re]
  exact neg_nonpos.mpr (trace_conjTranspose_mul_self_re_nonneg _)

end ThetLogos
