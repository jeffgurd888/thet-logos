/-
# SA-1: Finite heat-trace coefficients

Finite heat-trace coefficients `Tr(D^{2k})` as exact Yukawa polynomials.
Tier T3. Zero new axioms. No manifolds, curvature, or heat kernels appear.

Proved:
- `finite_heat_trace_even`: `Tr(D^{2k}) = Tr((D^2)^k)`.
- `tr_DF_sq_yukawa`: `Tr((smDirac …)^2)` as an explicit Yukawa polynomial (K3).
- `tr_fluctuated_sq`: `Tr((fluctuatedDirac D_F A)^2)`, symbolic in `A`.
- `fluctuatedDirac_zero`, `tr_fluctuated_sq_zero`: K4 (A=0 reduction).
- D²-block q-lemmas (`pow2_buildDirac_blk_00` … `pow2_buildDirac_blk_33`, C=0):
  infrastructure for the fourth power (stretch, not completed).

Open (stretch):
- `tr_DF_fourth_yukawa`: `Tr((smDirac …)^4)` as a Yukawa polynomial.
- `tr_fluctuated_fourth`: `Tr((fluctuatedDirac D_F A)^4)`, symbolic in `A`.
-/
import ThetLogos.InnerFluctuations

namespace ThetLogos

/-! ## Framework: trace-power lemmas -/

/-- Trace of a matrix square as an explicit double sum. -/
theorem trace_sq_double_sum {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℂ) :
    Matrix.trace (D ^ 2) = ∑ i, ∑ k, D i k * D k i := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]

/-- Trace of a matrix product as an explicit double sum. -/
theorem trace_mul_double_sum {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) :
    Matrix.trace (X * Y) = ∑ i, ∑ k, X i k * Y k i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- Even heat-trace powers reduce to powers of the square:
    `Tr(D^{2k}) = Tr((D^2)^k)`. -/
theorem finite_heat_trace_even {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℂ) (k : ℕ) :
    Matrix.trace (D ^ (2 * k)) = Matrix.trace ((D ^ 2) ^ k) := by
  rw [pow_mul]

/-- Trace of a squared sum. -/
theorem trace_add_sq {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) :
    Matrix.trace ((X + Y) ^ 2)
      = Matrix.trace (X ^ 2) + 2 * Matrix.trace (X * Y) + Matrix.trace (Y ^ 2) := by
  have h : (X + Y) ^ 2 = X ^ 2 + X * Y + Y * X + Y ^ 2 := by
    rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add]
    abel
  rw [h, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_mul_comm Y X]
  ring

/-! ## Block infrastructure for `buildDirac` -/

/-- Block index embedding: block `b : Fin 4`, within-block `a : Fin 8`.
    The val is `a.val + b.val * 8` (rather than `b.val * 8 + a.val`) so that
    block 0 is *definitionally* `a.val`, which keeps later steps smooth. -/
def blkIdx (b : Fin 4) (a : Fin 8) : I32 := ⟨a.val + b.val * 8, by
  have hb := b.isLt; have ha := a.isLt; omega⟩

/-- The block-index equivalence. -/
def blkEquiv : Fin 4 × Fin 8 ≃ Fin 32 where
  toFun p := blkIdx p.1 p.2
  invFun i := (⟨i.val / 8, by have h := i.isLt; omega⟩,
              ⟨i.val % 8, by have h := i.isLt; omega⟩)
  left_inv := by
    rintro ⟨b, a⟩
    have ha := a.isLt; have hb := b.isLt
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show (blkIdx b a).val / 8 = b.val
      have hr : (blkIdx b a).val = a.val + b.val * 8 := rfl
      omega
    · show (blkIdx b a).val % 8 = a.val
      have hr : (blkIdx b a).val = a.val + b.val * 8 := rfl
      omega
  right_inv := by
    intro i
    obtain ⟨v, hv⟩ := i
    have hdm := Nat.div_add_mod v 8
    apply Fin.ext
    show (blkIdx ⟨v / 8, by omega⟩ ⟨v % 8, by omega⟩).val = v
    have hr : (blkIdx ⟨v / 8, by omega⟩ ⟨v % 8, by omega⟩).val
        = v % 8 + (v / 8) * 8 := rfl
    omega

/-- Splitting a 32-sum into 4×8 block sums. -/
theorem sum_blkIdx (f : Fin 32 → ℂ) :
    ∑ i, f i = ∑ b : Fin 4, ∑ a : Fin 8, f (blkIdx b a) := by
  have h1 : (∑ i : Fin 32, f i) = ∑ p : Fin 4 × Fin 8, f (blkEquiv p) :=
    (Fintype.sum_bijective blkEquiv blkEquiv.bijective _ f (fun _ => rfl)).symm
  rw [h1, Fintype.sum_prod_type]
  rfl

/-! ## Block entries of `buildDirac`

Sixteen lemmas, one per (block, block) pair, giving the explicit 8×8 entry.
Proved by reducing the `buildDirac` if-tree with arithmetic facts, then `rfl`
(the index projections are definitional). -/

theorem buildDirac_blk_00 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 0 a₁) (blkIdx 0 a₂) = 0 := by
  have h1 : (blkIdx (0 : Fin 4) a₁).val < 8 := a₁.isLt
  have h2 : (blkIdx (0 : Fin 4) a₂).val < 8 := a₂.isLt
  unfold buildDirac; simp only []; simp [h1, h2]

theorem buildDirac_blk_01 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 0 a₁) (blkIdx 1 a₂) = A a₁ a₂ := by
  have h1 : (blkIdx (0 : Fin 4) a₁).val < 8 := a₁.isLt
  have h2 : ¬ (blkIdx (1 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 1 * 8 < 8); omega
  have h3 : (blkIdx (1 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show a₂.val + 1 * 8 < 16; omega
  unfold buildDirac; simp only []; simp [h1, h2, h3]; rfl

theorem buildDirac_blk_02 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 0 a₁) (blkIdx 2 a₂) = C a₁ a₂ := by
  have h1 : (blkIdx (0 : Fin 4) a₁).val < 8 := a₁.isLt
  have h2 : ¬ (blkIdx (2 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 8); omega
  have h3 : ¬ (blkIdx (2 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 16); omega
  have h4 : (blkIdx (2 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show a₂.val + 2 * 8 < 24; omega
  unfold buildDirac; simp only []; simp [h1, h2, h3, h4]; rfl

theorem buildDirac_blk_03 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 0 a₁) (blkIdx 3 a₂) = 0 := by
  have h1 : (blkIdx (0 : Fin 4) a₁).val < 8 := a₁.isLt
  have h2 : ¬ (blkIdx (3 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 8); omega
  have h3 : ¬ (blkIdx (3 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 16); omega
  have h4 : ¬ (blkIdx (3 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 24); omega
  unfold buildDirac; simp only []; simp [h1, h2, h3, h4]

theorem buildDirac_blk_10 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 1 a₁) (blkIdx 0 a₂) = A.conjTranspose a₁ a₂ := by
  have h1 : ¬ (blkIdx (1 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 1 * 8 < 8); omega
  have h1' : (blkIdx (1 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show a₁.val + 1 * 8 < 16; omega
  have h2 : (blkIdx (0 : Fin 4) a₂).val < 8 := a₂.isLt
  unfold buildDirac; simp only []; simp [h1, h1', h2]; rfl

theorem buildDirac_blk_11 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 1 a₁) (blkIdx 1 a₂) = 0 := by
  have h1 : ¬ (blkIdx (1 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 1 * 8 < 8); omega
  have h1' : (blkIdx (1 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show a₁.val + 1 * 8 < 16; omega
  have h2 : ¬ (blkIdx (1 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 1 * 8 < 8); omega
  have h3 : (blkIdx (1 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show a₂.val + 1 * 8 < 16; omega
  unfold buildDirac; simp only []; simp [h1, h1', h2, h3]

theorem buildDirac_blk_12 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 1 a₁) (blkIdx 2 a₂) = 0 := by
  have h1 : ¬ (blkIdx (1 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 1 * 8 < 8); omega
  have h1' : (blkIdx (1 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show a₁.val + 1 * 8 < 16; omega
  have h2 : ¬ (blkIdx (2 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 8); omega
  have h3 : ¬ (blkIdx (2 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 16); omega
  have h4 : (blkIdx (2 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show a₂.val + 2 * 8 < 24; omega
  unfold buildDirac; simp only []; simp [h1, h1', h2, h3, h4]

theorem buildDirac_blk_13 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 1 a₁) (blkIdx 3 a₂) = E.conjTranspose a₁ a₂ := by
  have h1 : ¬ (blkIdx (1 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 1 * 8 < 8); omega
  have h1' : (blkIdx (1 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show a₁.val + 1 * 8 < 16; omega
  have h2 : ¬ (blkIdx (3 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 8); omega
  have h3 : ¬ (blkIdx (3 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 16); omega
  have h4 : ¬ (blkIdx (3 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 24); omega
  unfold buildDirac; simp only []; simp [h1, h1', h2, h3, h4]; rfl

theorem buildDirac_blk_20 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 2 a₁) (blkIdx 0 a₂) = C.conjTranspose a₁ a₂ := by
  have h1 : ¬ (blkIdx (2 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 8); omega
  have h1' : ¬ (blkIdx (2 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 16); omega
  have h1'' : (blkIdx (2 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show a₁.val + 2 * 8 < 24; omega
  have h2 : (blkIdx (0 : Fin 4) a₂).val < 8 := a₂.isLt
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2]; rfl

theorem buildDirac_blk_21 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 2 a₁) (blkIdx 1 a₂) = 0 := by
  have h1 : ¬ (blkIdx (2 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 8); omega
  have h1' : ¬ (blkIdx (2 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 16); omega
  have h1'' : (blkIdx (2 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show a₁.val + 2 * 8 < 24; omega
  have h2 : ¬ (blkIdx (1 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 1 * 8 < 8); omega
  have h3 : (blkIdx (1 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show a₂.val + 1 * 8 < 16; omega
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2, h3]

theorem buildDirac_blk_22 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 2 a₁) (blkIdx 2 a₂) = 0 := by
  have h1 : ¬ (blkIdx (2 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 8); omega
  have h1' : ¬ (blkIdx (2 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 16); omega
  have h1'' : (blkIdx (2 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show a₁.val + 2 * 8 < 24; omega
  have h2 : ¬ (blkIdx (2 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 8); omega
  have h3 : ¬ (blkIdx (2 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 16); omega
  have h4 : (blkIdx (2 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show a₂.val + 2 * 8 < 24; omega
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2, h3, h4]

theorem buildDirac_blk_23 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 2 a₁) (blkIdx 3 a₂) = B a₁ a₂ := by
  have h1 : ¬ (blkIdx (2 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 8); omega
  have h1' : ¬ (blkIdx (2 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 2 * 8 < 16); omega
  have h1'' : (blkIdx (2 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show a₁.val + 2 * 8 < 24; omega
  have h2 : ¬ (blkIdx (3 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 8); omega
  have h3 : ¬ (blkIdx (3 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 16); omega
  have h4 : ¬ (blkIdx (3 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 24); omega
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2, h3, h4]; rfl

theorem buildDirac_blk_30 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 3 a₁) (blkIdx 0 a₂) = 0 := by
  have h1 : ¬ (blkIdx (3 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 8); omega
  have h1' : ¬ (blkIdx (3 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 16); omega
  have h1'' : ¬ (blkIdx (3 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 24); omega
  have h2 : (blkIdx (0 : Fin 4) a₂).val < 8 := a₂.isLt
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2]

theorem buildDirac_blk_31 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 3 a₁) (blkIdx 1 a₂) = E a₁ a₂ := by
  have h1 : ¬ (blkIdx (3 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 8); omega
  have h1' : ¬ (blkIdx (3 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 16); omega
  have h1'' : ¬ (blkIdx (3 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 24); omega
  have h2 : ¬ (blkIdx (1 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 1 * 8 < 8); omega
  have h3 : (blkIdx (1 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show a₂.val + 1 * 8 < 16; omega
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2, h3]; rfl

theorem buildDirac_blk_32 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 3 a₁) (blkIdx 2 a₂) = B.conjTranspose a₁ a₂ := by
  have h1 : ¬ (blkIdx (3 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 8); omega
  have h1' : ¬ (blkIdx (3 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 16); omega
  have h1'' : ¬ (blkIdx (3 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 24); omega
  have h2 : ¬ (blkIdx (2 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 8); omega
  have h3 : ¬ (blkIdx (2 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 2 * 8 < 16); omega
  have h4 : (blkIdx (2 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show a₂.val + 2 * 8 < 24; omega
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2, h3, h4]; rfl

theorem buildDirac_blk_33 (A B C E : Block8) (a₁ a₂ : Fin 8) :
    buildDirac A B C E (blkIdx 3 a₁) (blkIdx 3 a₂) = 0 := by
  have h1 : ¬ (blkIdx (3 : Fin 4) a₁).val < 8 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 8); omega
  have h1' : ¬ (blkIdx (3 : Fin 4) a₁).val < 16 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 16); omega
  have h1'' : ¬ (blkIdx (3 : Fin 4) a₁).val < 24 := by
    have h := a₁.isLt; show ¬ (a₁.val + 3 * 8 < 24); omega
  have h2 : ¬ (blkIdx (3 : Fin 4) a₂).val < 8 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 8); omega
  have h3 : ¬ (blkIdx (3 : Fin 4) a₂).val < 16 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 16); omega
  have h4 : ¬ (blkIdx (3 : Fin 4) a₂).val < 24 := by
    have h := a₂.isLt; show ¬ (a₂.val + 3 * 8 < 24); omega
  unfold buildDirac; simp only []; simp [h1, h1', h1'', h2, h3, h4]

/-! ## Trace of the square of a `buildDirac` matrix -/

/-- `Tr((buildDirac A B C E)^2) = 2·(Tr(AA†) + Tr(CC†) + Tr(E†E) + Tr(BB†))`.
    The factor 2 comes from the (0,1)/(1,0), (0,2)/(2,0), (1,3)/(3,1),
    (2,3)/(3,2) block pairs; the diagonal blocks of D² vanish in trace
    because the diagonal blocks of D itself are zero. -/
theorem trace_buildDirac_sq (A B C E : Block8) :
    Matrix.trace ((buildDirac A B C E) ^ 2)
      = 2 * (Matrix.trace (A * A.conjTranspose) + Matrix.trace (C * C.conjTranspose)
          + Matrix.trace (E.conjTranspose * E) + Matrix.trace (B * B.conjTranspose)) := by
  have t00 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 0 a₁) (blkIdx 0 a₂)
        * buildDirac A B C E (blkIdx 0 a₂) (blkIdx 0 a₁)) = 0 := by
    simp_rw [buildDirac_blk_00]; simp
  have t01 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 0 a₁) (blkIdx 1 a₂)
        * buildDirac A B C E (blkIdx 1 a₂) (blkIdx 0 a₁))
      = Matrix.trace (A * A.conjTranspose) := by
    simp_rw [buildDirac_blk_01, buildDirac_blk_10]
    exact (trace_mul_double_sum A A.conjTranspose).symm
  have t02 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 0 a₁) (blkIdx 2 a₂)
        * buildDirac A B C E (blkIdx 2 a₂) (blkIdx 0 a₁))
      = Matrix.trace (C * C.conjTranspose) := by
    simp_rw [buildDirac_blk_02, buildDirac_blk_20]
    exact (trace_mul_double_sum C C.conjTranspose).symm
  have t03 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 0 a₁) (blkIdx 3 a₂)
        * buildDirac A B C E (blkIdx 3 a₂) (blkIdx 0 a₁)) = 0 := by
    simp_rw [buildDirac_blk_03]; simp
  have t10 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 1 a₁) (blkIdx 0 a₂)
        * buildDirac A B C E (blkIdx 0 a₂) (blkIdx 1 a₁))
      = Matrix.trace (A.conjTranspose * A) := by
    simp_rw [buildDirac_blk_10, buildDirac_blk_01]
    exact (trace_mul_double_sum A.conjTranspose A).symm
  have t11 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 1 a₁) (blkIdx 1 a₂)
        * buildDirac A B C E (blkIdx 1 a₂) (blkIdx 1 a₁)) = 0 := by
    simp_rw [buildDirac_blk_11]; simp
  have t12 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 1 a₁) (blkIdx 2 a₂)
        * buildDirac A B C E (blkIdx 2 a₂) (blkIdx 1 a₁)) = 0 := by
    simp_rw [buildDirac_blk_12]; simp
  have t13 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 1 a₁) (blkIdx 3 a₂)
        * buildDirac A B C E (blkIdx 3 a₂) (blkIdx 1 a₁))
      = Matrix.trace (E.conjTranspose * E) := by
    simp_rw [buildDirac_blk_13, buildDirac_blk_31]
    exact (trace_mul_double_sum E.conjTranspose E).symm
  have t20 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 2 a₁) (blkIdx 0 a₂)
        * buildDirac A B C E (blkIdx 0 a₂) (blkIdx 2 a₁))
      = Matrix.trace (C.conjTranspose * C) := by
    simp_rw [buildDirac_blk_20, buildDirac_blk_02]
    exact (trace_mul_double_sum C.conjTranspose C).symm
  have t21 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 2 a₁) (blkIdx 1 a₂)
        * buildDirac A B C E (blkIdx 1 a₂) (blkIdx 2 a₁)) = 0 := by
    simp_rw [buildDirac_blk_21]; simp
  have t22 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 2 a₁) (blkIdx 2 a₂)
        * buildDirac A B C E (blkIdx 2 a₂) (blkIdx 2 a₁)) = 0 := by
    simp_rw [buildDirac_blk_22]; simp
  have t23 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 2 a₁) (blkIdx 3 a₂)
        * buildDirac A B C E (blkIdx 3 a₂) (blkIdx 2 a₁))
      = Matrix.trace (B * B.conjTranspose) := by
    simp_rw [buildDirac_blk_23, buildDirac_blk_32]
    exact (trace_mul_double_sum B B.conjTranspose).symm
  have t30 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 3 a₁) (blkIdx 0 a₂)
        * buildDirac A B C E (blkIdx 0 a₂) (blkIdx 3 a₁)) = 0 := by
    simp_rw [buildDirac_blk_30]; simp
  have t31 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 3 a₁) (blkIdx 1 a₂)
        * buildDirac A B C E (blkIdx 1 a₂) (blkIdx 3 a₁))
      = Matrix.trace (E * E.conjTranspose) := by
    simp_rw [buildDirac_blk_31, buildDirac_blk_13]
    exact (trace_mul_double_sum E E.conjTranspose).symm
  have t32 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 3 a₁) (blkIdx 2 a₂)
        * buildDirac A B C E (blkIdx 2 a₂) (blkIdx 3 a₁))
      = Matrix.trace (B.conjTranspose * B) := by
    simp_rw [buildDirac_blk_32, buildDirac_blk_23]
    exact (trace_mul_double_sum B.conjTranspose B).symm
  have t33 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx 3 a₁) (blkIdx 3 a₂)
        * buildDirac A B C E (blkIdx 3 a₂) (blkIdx 3 a₁)) = 0 := by
    simp_rw [buildDirac_blk_33]; simp
  rw [trace_sq_double_sum, sum_blkIdx]
  simp_rw [sum_blkIdx]
  -- Swap the middle two sums so the block indices are outermost:
  -- ∑ b₁ ∑ a₁ ∑ b₂ ∑ a₂  →  ∑ b₁ ∑ b₂ ∑ a₁ ∑ a₂.
  have hswap : (∑ b₁ : Fin 4, ∑ a₁ : Fin 8, ∑ b₂ : Fin 4, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx b₁ a₁) (blkIdx b₂ a₂)
        * buildDirac A B C E (blkIdx b₂ a₂) (blkIdx b₁ a₁))
    = ∑ b₁ : Fin 4, ∑ b₂ : Fin 4, ∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      buildDirac A B C E (blkIdx b₁ a₁) (blkIdx b₂ a₂)
        * buildDirac A B C E (blkIdx b₂ a₂) (blkIdx b₁ a₁) := by
    refine Finset.sum_congr rfl (fun b₁ _ => ?_)
    exact Finset.sum_comm
  rw [hswap, Fin.sum_univ_four]
  simp_rw [Fin.sum_univ_four]
  rw [t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33,
    Matrix.trace_mul_comm A.conjTranspose A, Matrix.trace_mul_comm C.conjTranspose C,
    Matrix.trace_mul_comm E E.conjTranspose, Matrix.trace_mul_comm B.conjTranspose B]
  ring

/-! ## Diagonal helpers -/

/-- Conjugate transpose of a diagonal matrix is diagonal of conjugates. -/
theorem conjTranspose_diagonal (d : Fin 8 → ℂ) :
    (Matrix.diagonal d).conjTranspose = Matrix.diagonal (fun i => star (d i)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.conjTranspose]
  · have h' : j ≠ i := Ne.symm h
    simp [Matrix.conjTranspose, h, h']

/-- `z * star z = normSq z` (as a complex number), via `Complex.mul_conj`. -/
theorem mul_star_eq_normSq (z : ℂ) : z * star z = ((Complex.normSq z : ℝ) : ℂ) :=
  Complex.mul_conj z

/-- `star z * z = normSq z` (as a complex number). -/
theorem star_mul_eq_normSq (z : ℂ) : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [mul_comm]; exact Complex.mul_conj z

/-- `normSq` is invariant under conjugation. -/
theorem normSq_starRingEnd (z : ℂ) :
    Complex.normSq ((starRingEnd ℂ) z) = Complex.normSq z := by
  rw [starRingEnd_apply]
  simp [Complex.normSq, Complex.conj_re, Complex.conj_im]

/-- Trace of `diagonal d * (diagonal d)ᴴ` as a sum of `d i * star (d i)`. -/
theorem trace_diag_mul_diag_star (d : Fin 8 → ℂ) :
    Matrix.trace (Matrix.diagonal d * (Matrix.diagonal d).conjTranspose)
      = ∑ i : Fin 8, (d i * star (d i)) := by
  rw [conjTranspose_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- Trace of `(diagonal d)ᴴ * diagonal d` as a sum of `star (d i) * d i`. -/
theorem trace_diag_star_mul_diag (d : Fin 8 → ℂ) :
    Matrix.trace ((Matrix.diagonal d).conjTranspose * Matrix.diagonal d)
      = ∑ i : Fin 8, (star (d i) * d i) := by
  rw [conjTranspose_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-! ## K3: the Yukawa polynomial for `Tr((smDirac …)^2)` -/

/-- Trace of `yukawaBlock * yukawaBlockᴴ`: `|yNu|² + |yE|² + 3|yU|² + 3|yD|²`. -/
theorem trace_yukawaBlock_sq (yNu yE yU yD : ℂ) :
    Matrix.trace (yukawaBlock yNu yE yU yD
      * (yukawaBlock yNu yE yU yD).conjTranspose)
    = ((Complex.normSq yNu + Complex.normSq yE
        + 3 * Complex.normSq yU + 3 * Complex.normSq yD : ℝ) : ℂ) := by
  have hA : yukawaBlock yNu yE yU yD
      = Matrix.diagonal (![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) := rfl
  rw [hA, trace_diag_mul_diag_star, Fin.sum_univ_eight]
  simp_rw [mul_star_eq_normSq]
  push_cast
  ring

/-- Trace of `majoranaBlockᴴ * majoranaBlock`: `|yR|²`. -/
theorem trace_majoranaBlock_sq (yR : ℂ) :
    Matrix.trace ((majoranaBlock yR).conjTranspose * majoranaBlock yR)
    = ((Complex.normSq yR : ℝ) : ℂ) := by
  have hE : majoranaBlock yR
      = Matrix.diagonal (fun k : Fin 8 => if k.val = 0 then yR else 0) := rfl
  rw [hE, trace_diag_star_mul_diag, Fin.sum_univ_eight]
  simp_rw [star_mul_eq_normSq]
  simp

/-- Trace of `B * Bᴴ` where `B = yukawaBlock.map (starRingEnd ℂ)`:
    same as the yukawaBlock (conjugation preserves `normSq`). -/
theorem trace_yukawaBlockConj_sq (yNu yE yU yD : ℂ) :
    Matrix.trace ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)
      * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose)
    = ((Complex.normSq yNu + Complex.normSq yE
        + 3 * Complex.normSq yU + 3 * Complex.normSq yD : ℝ) : ℂ) := by
  have hA : yukawaBlock yNu yE yU yD
      = Matrix.diagonal (![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) := rfl
  have hmap : (Matrix.diagonal (![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ)).map
        (starRingEnd ℂ)
      = Matrix.diagonal (fun i => starRingEnd ℂ (![yNu, yE, yU, yD, yU, yD, yU, yD] i)) := by
    ext i j
    simp [Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  rw [hA, hmap, trace_diag_mul_diag_star, Fin.sum_univ_eight]
  simp_rw [mul_star_eq_normSq, normSq_starRingEnd]
  push_cast
  ring

/-- K3: `Tr((smDirac yNu yE yU yD yR)^2)` is the Yukawa polynomial
    `4·(|yNu|² + |yE|² + 3|yU|² + 3|yD|²) + 2·|yR|²`.
    The 3× multiplicities are the color multiplicities of the u/d quarks
    (yU, yD appear 3 times in the yukawaBlock diagonal); ν/e appear once.
    This is Tier T3 (the smDirac ansatz itself is imposed, not derived). -/
theorem tr_DF_sq_yukawa (yNu yE yU yD yR : ℂ) :
    Matrix.trace ((smDirac yNu yE yU yD yR) ^ 2)
      = ((4 * (Complex.normSq yNu + Complex.normSq yE
            + 3 * Complex.normSq yU + 3 * Complex.normSq yD)
          + 2 * Complex.normSq yR : ℝ) : ℂ) := by
  have hsm : smDirac yNu yE yU yD yR
      = buildDirac (yukawaBlock yNu yE yU yD)
          ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
          0 (majoranaBlock yR) := rfl
  rw [hsm, trace_buildDirac_sq]
  have hC : Matrix.trace ((0 : Block8) * (0 : Block8).conjTranspose) = 0 := by simp
  rw [hC, trace_yukawaBlock_sq, trace_majoranaBlock_sq, trace_yukawaBlockConj_sq]
  push_cast
  ring

/-! ## Fluctuated Dirac traces -/

/-- `Tr((fluctuatedDirac D_F A)^2)`, symbolic in `A`:
    the cross term is `2·Tr(D_F·(A + A°))` and the pure-fluctuation term is
    `Tr((A + A°)^2)`, where `A° = oppositeOneForm A`. -/
theorem tr_fluctuated_sq (D_F A : Matrix I32 I32 ℂ) :
    Matrix.trace ((fluctuatedDirac D_F A) ^ 2)
      = Matrix.trace (D_F ^ 2)
        + 2 * Matrix.trace (D_F * (A + oppositeOneForm A))
        + Matrix.trace ((A + oppositeOneForm A) ^ 2) := by
  have h : fluctuatedDirac D_F A = D_F + (A + oppositeOneForm A) := by
    simp only [fluctuatedDirac, add_assoc]
  rw [h]
  exact trace_add_sq D_F (A + oppositeOneForm A)

/-- K4: at `A = 0`, the fluctuated Dirac is the unfluctuated one. -/
theorem fluctuatedDirac_zero (D_F : Matrix I32 I32 ℂ) :
    fluctuatedDirac D_F 0 = D_F := by
  simp [fluctuatedDirac, oppositeOneForm]

/-- K4 corollary: at `A = 0`, the fluctuated square-trace reduces to the
    unfluctuated one. -/
theorem tr_fluctuated_sq_zero (D_F : Matrix I32 I32 ℂ) :
    Matrix.trace ((fluctuatedDirac D_F 0) ^ 2) = Matrix.trace (D_F ^ 2) := by
  rw [fluctuatedDirac_zero]

/-! ## D² block entries (C = 0 case, for the fourth power) -/

/-- D² block (0,0) = A·Aᴴ (C = 0). -/
theorem pow2_buildDirac_blk_00 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 0 a₂)
      = (A * A.conjTranspose) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_10,
    buildDirac_blk_02, buildDirac_blk_20, buildDirac_blk_03, buildDirac_blk_30]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]
  rw [← Matrix.mul_apply]

/-- D² block (0,3) = A·Eᴴ (C = 0). -/
theorem pow2_buildDirac_blk_03 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 3 a₂)
      = (A * E.conjTranspose) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_00, buildDirac_blk_03, buildDirac_blk_01, buildDirac_blk_13,
    buildDirac_blk_02, buildDirac_blk_23, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]
  rw [← Matrix.mul_apply]

/-- D² block (1,1) = Aᴴ·A + Eᴴ·E (C = 0). -/
theorem pow2_buildDirac_blk_11 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 1 a₂)
      = (A.conjTranspose * A + E.conjTranspose * E) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_10, buildDirac_blk_01, buildDirac_blk_11,
    buildDirac_blk_12, buildDirac_blk_21, buildDirac_blk_13, buildDirac_blk_31]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.add_apply]

/-- D² block (1,2) = Eᴴ·Bᴴ (C = 0). -/
theorem pow2_buildDirac_blk_12 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 2 a₂)
      = (E.conjTranspose * B.conjTranspose) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_10, buildDirac_blk_02, buildDirac_blk_11, buildDirac_blk_12,
    buildDirac_blk_22, buildDirac_blk_13, buildDirac_blk_32]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]
  rw [← Matrix.mul_apply]

/-- D² block (2,1) = B·E (C = 0). -/
theorem pow2_buildDirac_blk_21 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 1 a₂)
      = (B * E) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_20, buildDirac_blk_01, buildDirac_blk_21, buildDirac_blk_11,
    buildDirac_blk_22, buildDirac_blk_23, buildDirac_blk_31]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply, Matrix.conjTranspose_zero, Matrix.zero_mul]
  rw [← Matrix.mul_apply]

/-- D² block (2,2) = B·Bᴴ (C = 0). -/
theorem pow2_buildDirac_blk_22 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 2 a₂)
      = (B * B.conjTranspose) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_20, buildDirac_blk_02, buildDirac_blk_21, buildDirac_blk_12,
    buildDirac_blk_22, buildDirac_blk_23, buildDirac_blk_32]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]
  rw [← Matrix.mul_apply]

/-- D² block (3,0) = E·Aᴴ (C = 0). -/
theorem pow2_buildDirac_blk_30 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 0 a₂)
      = (E * A.conjTranspose) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_30, buildDirac_blk_00, buildDirac_blk_31, buildDirac_blk_10,
    buildDirac_blk_32, buildDirac_blk_20, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply, Matrix.conjTranspose_zero, Matrix.mul_zero]
  rw [← Matrix.mul_apply]

/-- D² block (3,3) = E·Eᴴ + Bᴴ·B (C = 0). -/
theorem pow2_buildDirac_blk_33 (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 3 a₂)
      = (E * E.conjTranspose + B.conjTranspose * B) a₁ a₂ := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_30, buildDirac_blk_03, buildDirac_blk_31, buildDirac_blk_13,
    buildDirac_blk_32, buildDirac_blk_23, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.add_apply]

/-! ## Fourth power trace (stretch) -/

/- The 8 nonzero D²-block q-lemmas above (`pow2_buildDirac_blk_00` through
    `pow2_buildDirac_blk_33`) provide the infrastructure for `Tr(D⁴)`.
    The full `tr_DF_fourth_yukawa` (Yukawa polynomial for the fourth power)
    and `tr_fluctuated_fourth` remain open: they require a
    `trace_buildDirac_fourth` block-expansion lemma (16 terms, 8 nonzero)
    analogous to `trace_buildDirac_sq`, which is mechanical but lengthy.
    Numerical verification (2026-09-30): `Tr(D⁴) = 4(|yNu|⁴+|yE|⁴+3|yU|⁴+3|yD|⁴)
    + 8|yNu|²|yR|² + 2|yR|⁴` (5 random trials, err ≤ 1.2e-13). -/

end ThetLogos

namespace ThetLogos

/-! ## D² zero blocks (C = 0 case, for the fourth power) -/

/-- D² block (0,1) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_01_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 1 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_11,
    buildDirac_blk_02, buildDirac_blk_21, buildDirac_blk_03, buildDirac_blk_31]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]

/-- D² block (0,2) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_02_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 2 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_00, buildDirac_blk_02, buildDirac_blk_01, buildDirac_blk_12,
    buildDirac_blk_22, buildDirac_blk_03, buildDirac_blk_32]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]

/-- D² block (1,0) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_10_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 0 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_10, buildDirac_blk_00, buildDirac_blk_11, buildDirac_blk_12,
    buildDirac_blk_20, buildDirac_blk_13, buildDirac_blk_30]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply, Matrix.conjTranspose_zero]

/-- D² block (1,3) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_13_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 3 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_10, buildDirac_blk_03, buildDirac_blk_11, buildDirac_blk_13,
    buildDirac_blk_12, buildDirac_blk_23, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]

/-- D² block (2,0) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_20_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 0 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_20, buildDirac_blk_00, buildDirac_blk_21, buildDirac_blk_10,
    buildDirac_blk_22, buildDirac_blk_23, buildDirac_blk_30]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply, Matrix.conjTranspose_zero]

/-- D² block (2,3) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_23_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 3 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_20, buildDirac_blk_03, buildDirac_blk_21, buildDirac_blk_13,
    buildDirac_blk_22, buildDirac_blk_23, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply, Matrix.conjTranspose_zero]

/-- D² block (3,1) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_31_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 1 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_30, buildDirac_blk_01, buildDirac_blk_31, buildDirac_blk_11,
    buildDirac_blk_32, buildDirac_blk_21, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]

/-- D² block (3,2) vanishes (C = 0). -/
theorem pow2_buildDirac_blk_32_zero (A B E : Block8) (a₁ a₂ : Fin 8) :
    ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 2 a₂) = 0 := by
  rw [pow_two, Matrix.mul_apply, sum_blkIdx, Fin.sum_univ_four]
  simp_rw [buildDirac_blk_30, buildDirac_blk_02, buildDirac_blk_31, buildDirac_blk_12,
    buildDirac_blk_32, buildDirac_blk_22, buildDirac_blk_33]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    Matrix.zero_apply]

/-! ## Fourth power trace expansion -/

/-- `Tr((buildDirac A B 0 E)^4)` as a sum of 8×8 block traces.
    Only 8 of the 16 block pairs contribute; the rest vanish. -/
theorem trace_buildDirac_fourth (A B E : Block8) :
    Matrix.trace ((buildDirac A B 0 E) ^ 4)
      = Matrix.trace ((A * A.conjTranspose) * (A * A.conjTranspose))
      + Matrix.trace ((A * E.conjTranspose) * (E * A.conjTranspose))
      + Matrix.trace ((A.conjTranspose * A + E.conjTranspose * E)
          * (A.conjTranspose * A + E.conjTranspose * E))
      + Matrix.trace ((E.conjTranspose * B.conjTranspose) * (B * E))
      + Matrix.trace ((B * E) * (E.conjTranspose * B.conjTranspose))
      + Matrix.trace ((B * B.conjTranspose) * (B * B.conjTranspose))
      + Matrix.trace ((E * A.conjTranspose) * (A * E.conjTranspose))
      + Matrix.trace ((E * E.conjTranspose + B.conjTranspose * B)
          * (E * E.conjTranspose + B.conjTranspose * B)) := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  rw [h4, finite_heat_trace_even, trace_sq_double_sum, sum_blkIdx]
  simp_rw [sum_blkIdx]
  have hswap : (∑ b₁ : Fin 4, ∑ a₁ : Fin 8, ∑ b₂ : Fin 4, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx b₁ a₁) (blkIdx b₂ a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx b₂ a₂) (blkIdx b₁ a₁))
    = ∑ b₁ : Fin 4, ∑ b₂ : Fin 4, ∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx b₁ a₁) (blkIdx b₂ a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx b₂ a₂) (blkIdx b₁ a₁) := by
    refine Finset.sum_congr rfl (fun b₁ _ => ?_)
    exact Finset.sum_comm
  rw [hswap, Fin.sum_univ_four]
  simp_rw [Fin.sum_univ_four]
  have p00 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 0 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 0 a₂) (blkIdx 0 a₁))
      = Matrix.trace ((A * A.conjTranspose) * (A * A.conjTranspose)) := by
    simp_rw [pow2_buildDirac_blk_00]
    exact (trace_mul_double_sum _ _).symm
  have p01 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 1 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 1 a₂) (blkIdx 0 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_10_zero]
    simp
  have p02 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 2 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 2 a₂) (blkIdx 0 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_20_zero]
    simp
  have p03 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 0 a₁) (blkIdx 3 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 3 a₂) (blkIdx 0 a₁))
      = Matrix.trace ((A * E.conjTranspose) * (E * A.conjTranspose)) := by
    simp_rw [pow2_buildDirac_blk_03, pow2_buildDirac_blk_30]
    exact (trace_mul_double_sum _ _).symm
  have p10 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 0 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 0 a₂) (blkIdx 1 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_10_zero, pow2_buildDirac_blk_01_zero]
    simp
  have p11 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 1 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 1 a₂) (blkIdx 1 a₁))
      = Matrix.trace ((A.conjTranspose * A + E.conjTranspose * E)
          * (A.conjTranspose * A + E.conjTranspose * E)) := by
    simp_rw [pow2_buildDirac_blk_11]
    exact (trace_mul_double_sum _ _).symm
  have p12 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 2 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 2 a₂) (blkIdx 1 a₁))
      = Matrix.trace ((E.conjTranspose * B.conjTranspose) * (B * E)) := by
    simp_rw [pow2_buildDirac_blk_12, pow2_buildDirac_blk_21]
    exact (trace_mul_double_sum _ _).symm
  have p13 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 1 a₁) (blkIdx 3 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 3 a₂) (blkIdx 1 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_31_zero]
    simp
  have p20 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 0 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 0 a₂) (blkIdx 2 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_02_zero]
    simp
  have p21 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 1 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 1 a₂) (blkIdx 2 a₁))
      = Matrix.trace ((B * E) * (E.conjTranspose * B.conjTranspose)) := by
    simp_rw [pow2_buildDirac_blk_21, pow2_buildDirac_blk_12]
    exact (trace_mul_double_sum _ _).symm
  have p22 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 2 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 2 a₂) (blkIdx 2 a₁))
      = Matrix.trace ((B * B.conjTranspose) * (B * B.conjTranspose)) := by
    simp_rw [pow2_buildDirac_blk_22]
    exact (trace_mul_double_sum _ _).symm
  have p23 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 2 a₁) (blkIdx 3 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 3 a₂) (blkIdx 2 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_23_zero, pow2_buildDirac_blk_32_zero]
    simp
  have p30 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 0 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 0 a₂) (blkIdx 3 a₁))
      = Matrix.trace ((E * A.conjTranspose) * (A * E.conjTranspose)) := by
    simp_rw [pow2_buildDirac_blk_30, pow2_buildDirac_blk_03]
    exact (trace_mul_double_sum _ _).symm
  have p31 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 1 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 1 a₂) (blkIdx 3 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_13_zero]
    simp
  have p32 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 2 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 2 a₂) (blkIdx 3 a₁)) = 0 := by
    simp_rw [pow2_buildDirac_blk_32_zero, pow2_buildDirac_blk_23_zero]
    simp
  have p33 : (∑ a₁ : Fin 8, ∑ a₂ : Fin 8,
      ((buildDirac A B 0 E)^2) (blkIdx 3 a₁) (blkIdx 3 a₂)
        * ((buildDirac A B 0 E)^2) (blkIdx 3 a₂) (blkIdx 3 a₁))
      = Matrix.trace ((E * E.conjTranspose + B.conjTranspose * B)
          * (E * E.conjTranspose + B.conjTranspose * B)) := by
    simp_rw [pow2_buildDirac_blk_33]
    exact (trace_mul_double_sum _ _).symm
  rw [p00, p01, p02, p03, p10, p11, p12, p13, p20, p21, p22, p23, p30, p31, p32, p33]
  ring

end ThetLogos

/-! ## Fourth power Yukawa evaluation -/

namespace ThetLogos

/-- A diagonal times its conjugate-transpose diagonal is diagonal. -/
theorem diag_mul_conjTranspose_diag (d : Fin 8 → ℂ) :
    Matrix.diagonal d * (Matrix.diagonal d).conjTranspose
      = Matrix.diagonal (fun i => d i * star (d i)) := by
  rw [conjTranspose_diagonal, Matrix.diagonal_mul_diagonal]

/-- Sum of two diagonals is diagonal. -/
theorem diagonal_add_eq (d₁ d₂ : Fin 8 → ℂ) :
    Matrix.diagonal d₁ + Matrix.diagonal d₂
      = Matrix.diagonal (fun i => d₁ i + d₂ i) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

end ThetLogos

namespace ThetLogos

/-- K4a: `Tr((smDirac yNu yE yU yD yR)^4)` is the Yukawa polynomial
    `4·(|yNu|⁴ + |yE|⁴ + 3|yU|⁴ + 3|yD|⁴) + 8·|yNu|²·|yR|² + 2·|yR|⁴`.
    The 3× are color multiplicities; the Majorana `|yR|` terms come only from
    the ν_R slot (index 0 of the Majorana diagonal). Tier T3. -/
theorem tr_DF_fourth_yukawa (yNu yE yU yD yR : ℂ) :
    Matrix.trace ((smDirac yNu yE yU yD yR) ^ 4)
      = ((4 * ((Complex.normSq yNu)^2 + (Complex.normSq yE)^2
            + 3 * (Complex.normSq yU)^2 + 3 * (Complex.normSq yD)^2)
          + 8 * Complex.normSq yNu * Complex.normSq yR
          + 2 * (Complex.normSq yR)^2 : ℝ) : ℂ) := by
  have hsm : smDirac yNu yE yU yD yR
      = buildDirac (yukawaBlock yNu yE yU yD)
          ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
          0 (majoranaBlock yR) := rfl
  rw [hsm, trace_buildDirac_fourth]
  have hA : yukawaBlock yNu yE yU yD
      = Matrix.diagonal (![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) := rfl
  have hE : majoranaBlock yR
      = Matrix.diagonal (fun k : Fin 8 => if k.val = 0 then yR else 0) := rfl
  have hmap : (Matrix.diagonal (![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ)).map
        (starRingEnd ℂ)
      = Matrix.diagonal
          (fun i => starRingEnd ℂ (![yNu, yE, yU, yD, yU, yD, yU, yD] i)) := by
    ext i j
    simp [Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  -- Block (0,0): Tr((A·Aᴴ)²)
  have e1 : Matrix.trace
      ((yukawaBlock yNu yE yU yD * (yukawaBlock yNu yE yU yD).conjTranspose)
        * (yukawaBlock yNu yE yU yD * (yukawaBlock yNu yE yU yD).conjTranspose))
      = (((Complex.normSq yNu)^2 + (Complex.normSq yE)^2
          + 3 * (Complex.normSq yU)^2 + 3 * (Complex.normSq yD)^2 : ℝ) : ℂ) := by
    rw [hA, diag_mul_conjTranspose_diag, Matrix.diagonal_mul_diagonal,
      Matrix.trace_diagonal, Fin.sum_univ_eight]
    simp_rw [mul_star_eq_normSq]
    push_cast
    ring
  -- Block (0,3): Tr((A·Eᴴ)·(E·Aᴴ)) = |yNu|²·|yR|² (only the ν_R slot contributes)
  have e2 : Matrix.trace
      ((yukawaBlock yNu yE yU yD * (majoranaBlock yR).conjTranspose)
        * (majoranaBlock yR * (yukawaBlock yNu yE yU yD).conjTranspose))
      = ((Complex.normSq yNu * Complex.normSq yR : ℝ) : ℂ) := by
    rw [hA, hE, conjTranspose_diagonal, Matrix.diagonal_mul_diagonal,
      conjTranspose_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    have hsum : (∑ i : Fin 8,
        ((![yNu, yE, yU, yD, yU, yD, yU, yD] i
            * star (if i.val = 0 then yR else 0))
          * ((if i.val = 0 then yR else 0)
            * star ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) i))))
        = ((![yNu, yE, yU, yD, yU, yD, yU, yD] 0
            * star (if (0 : Fin 8).val = 0 then yR else 0))
          * ((if (0 : Fin 8).val = 0 then yR else 0)
            * star ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) 0))) := by
      refine Fintype.sum_eq_single (0 : Fin 8) ?_
      intro i hi
      have hiv : ¬ (i.val = 0) := by
        intro hcon
        apply hi
        have hiv' : i.val = (0 : Fin 8).val := by rw [hcon]; rfl
        exact Fin.ext hiv'
      simp only [if_neg hiv, star_zero, mul_zero, zero_mul]
    rw [hsum]
    simp only [Fin.val_zero, if_pos, Matrix.cons_val_zero]
    have hrr : (yNu * star yR) * (yR * star yNu)
        = (yNu * star yNu) * (yR * star yR) := by ring
    rw [hrr, mul_star_eq_normSq, mul_star_eq_normSq]
    push_cast
    ring
  -- Block (1,1): Tr((Aᴴ·A + Eᴴ·E)²)
  have e3 : Matrix.trace
      (((yukawaBlock yNu yE yU yD).conjTranspose * yukawaBlock yNu yE yU yD
        + (majoranaBlock yR).conjTranspose * majoranaBlock yR)
      * ((yukawaBlock yNu yE yU yD).conjTranspose * yukawaBlock yNu yE yU yD
        + (majoranaBlock yR).conjTranspose * majoranaBlock yR))
      = (((Complex.normSq yNu)^2 + (Complex.normSq yE)^2
          + 3 * (Complex.normSq yU)^2 + 3 * (Complex.normSq yD)^2
          + 2 * Complex.normSq yNu * Complex.normSq yR
          + (Complex.normSq yR)^2 : ℝ) : ℂ) := by
    simp_rw [hA, hE, conjTranspose_diagonal, Matrix.diagonal_mul_diagonal,
      diagonal_add_eq, Matrix.trace_diagonal, Fin.sum_univ_eight]
    simp_rw [star_mul_eq_normSq, mul_star_eq_normSq]
    simp
    push_cast
    ring
  -- Block (1,2): Tr((Eᴴ·Bᴴ)·(B·E)) = |yNu|²·|yR|²
  have e4 : Matrix.trace
      (((majoranaBlock yR).conjTranspose
        * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose)
      * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ) * majoranaBlock yR))
      = ((Complex.normSq yNu * Complex.normSq yR : ℝ) : ℂ) := by
    rw [hA, hmap, hE]
    simp_rw [conjTranspose_diagonal, starRingEnd_apply, star_star,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    have hsum : (∑ i : Fin 8,
        ((star (if i.val = 0 then yR else 0)
            * ![yNu, yE, yU, yD, yU, yD, yU, yD] i)
          * ((star ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) i))
            * (if i.val = 0 then yR else 0))))
        = ((star (if (0 : Fin 8).val = 0 then yR else 0)
            * ![yNu, yE, yU, yD, yU, yD, yU, yD] 0)
          * ((star ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) 0))
            * (if (0 : Fin 8).val = 0 then yR else 0))) := by
      refine Fintype.sum_eq_single (0 : Fin 8) ?_
      intro i hi
      have hiv : ¬ (i.val = 0) := by
        intro hcon
        apply hi
        have hiv' : i.val = (0 : Fin 8).val := by rw [hcon]; rfl
        exact Fin.ext hiv'
      simp only [if_neg hiv, star_zero, mul_zero, zero_mul]
    rw [hsum]
    simp only [Fin.val_zero, if_pos, Matrix.cons_val_zero]
    have hrr : (star yR * yNu) * (star yNu * yR)
        = (yNu * star yNu) * (yR * star yR) := by ring
    rw [hrr, mul_star_eq_normSq, mul_star_eq_normSq]
    push_cast
    ring
  -- Block (2,1): Tr((B·E)·(Eᴴ·Bᴴ)) = |yNu|²·|yR|²
  have e5 : Matrix.trace
      (((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ) * majoranaBlock yR)
        * ((majoranaBlock yR).conjTranspose
          * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose))
      = ((Complex.normSq yNu * Complex.normSq yR : ℝ) : ℂ) := by
    rw [hA, hmap, hE]
    simp_rw [conjTranspose_diagonal, starRingEnd_apply, star_star,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    have hsum : (∑ i : Fin 8,
        (((starRingEnd ℂ ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) i))
            * (if i.val = 0 then yR else 0))
          * ((star (if i.val = 0 then yR else 0))
            * ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) i))))
        = (((starRingEnd ℂ ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) 0))
            * (if (0 : Fin 8).val = 0 then yR else 0))
          * ((star (if (0 : Fin 8).val = 0 then yR else 0))
            * ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) 0))) := by
      refine Fintype.sum_eq_single (0 : Fin 8) ?_
      intro i hi
      have hiv : ¬ (i.val = 0) := by
        intro hcon
        apply hi
        have hiv' : i.val = (0 : Fin 8).val := by rw [hcon]; rfl
        exact Fin.ext hiv'
      simp only [if_neg hiv, star_zero, mul_zero, zero_mul]
    rw [hsum]
    simp only [Fin.val_zero, if_pos, Matrix.cons_val_zero, starRingEnd_apply]
    have hrr : (star yNu * yR) * (star yR * yNu)
        = (yNu * star yNu) * (yR * star yR) := by ring
    rw [hrr, mul_star_eq_normSq, mul_star_eq_normSq]
    push_cast
    ring
  -- Block (2,2): Tr((B·Bᴴ)²), same as (A·Aᴴ)² since conjugation preserves normSq
  have e6 : Matrix.trace
      (((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)
        * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose)
      * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)
        * ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose))
      = (((Complex.normSq yNu)^2 + (Complex.normSq yE)^2
          + 3 * (Complex.normSq yU)^2 + 3 * (Complex.normSq yD)^2 : ℝ) : ℂ) := by
    rw [hA, hmap]
    simp_rw [conjTranspose_diagonal, starRingEnd_apply, star_star,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_eight]
    simp_rw [starRingEnd_apply, mul_star_eq_normSq, normSq_starRingEnd]
    push_cast
    ring
  -- Block (3,0): Tr((E·Aᴴ)·(A·Eᴴ)) = |yNu|²·|yR|²
  have e7 : Matrix.trace
      ((majoranaBlock yR * (yukawaBlock yNu yE yU yD).conjTranspose)
        * (yukawaBlock yNu yE yU yD * (majoranaBlock yR).conjTranspose))
      = ((Complex.normSq yNu * Complex.normSq yR : ℝ) : ℂ) := by
    rw [hA, hE, conjTranspose_diagonal, Matrix.diagonal_mul_diagonal,
      conjTranspose_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    have hsum : (∑ i : Fin 8,
        (((if i.val = 0 then yR else 0)
            * star ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) i))
          * ((![yNu, yE, yU, yD, yU, yD, yU, yD] i)
            * star (if i.val = 0 then yR else 0))))
        = (((if (0 : Fin 8).val = 0 then yR else 0)
            * star ((![yNu, yE, yU, yD, yU, yD, yU, yD] : Fin 8 → ℂ) 0))
          * ((![yNu, yE, yU, yD, yU, yD, yU, yD] 0)
            * star (if (0 : Fin 8).val = 0 then yR else 0))) := by
      refine Fintype.sum_eq_single (0 : Fin 8) ?_
      intro i hi
      have hiv : ¬ (i.val = 0) := by
        intro hcon
        apply hi
        have hiv' : i.val = (0 : Fin 8).val := by rw [hcon]; rfl
        exact Fin.ext hiv'
      simp only [if_neg hiv, star_zero, mul_zero, zero_mul]
    rw [hsum]
    simp only [Fin.val_zero, if_pos, Matrix.cons_val_zero]
    have hrr : (yR * star yNu) * (yNu * star yR)
        = (yNu * star yNu) * (yR * star yR) := by ring
    rw [hrr, mul_star_eq_normSq, mul_star_eq_normSq]
    push_cast
    ring
  -- Block (3,3): Tr((E·Eᴴ + Bᴴ·B)²)
  have e8 : Matrix.trace
      ((majoranaBlock yR * (majoranaBlock yR).conjTranspose
        + ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose
          * (yukawaBlock yNu yE yU yD).map (starRingEnd ℂ))
      * (majoranaBlock yR * (majoranaBlock yR).conjTranspose
        + ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)).conjTranspose
          * (yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)))
      = (((Complex.normSq yNu)^2 + (Complex.normSq yE)^2
          + 3 * (Complex.normSq yU)^2 + 3 * (Complex.normSq yD)^2
          + 2 * Complex.normSq yNu * Complex.normSq yR
          + (Complex.normSq yR)^2 : ℝ) : ℂ) := by
    rw [hA, hmap, hE]
    simp_rw [conjTranspose_diagonal, starRingEnd_apply, star_star,
      Matrix.diagonal_mul_diagonal, diagonal_add_eq,
      Matrix.trace_diagonal, Fin.sum_univ_eight]
    simp_rw [mul_star_eq_normSq, star_mul_eq_normSq, normSq_starRingEnd]
    simp
    push_cast
    ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  push_cast
  ring
