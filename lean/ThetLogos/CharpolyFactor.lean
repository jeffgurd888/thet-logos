import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import ThetLogos.MartinettiRep

/-!
# Q4 Path B — sectoral factorization of `charpoly(D_F)`

Candidate module for the Q4 Path B ledger entry (amendment of 2026-10-05 in
`ThetLogos/BlockedQuestions.lean`). The amendment's load-bearing lemma: the
characteristic polynomial of the finite Dirac operator `D_F` splits into
sector polynomials of degree ≤ 4 in `λ²`.

Result: the claim is TRUE for the corpus's one-generation ansatz
`ThetLogos.MartinettiRep.smDirac`, in a stronger form. `smDirac` couples only
indices with the same mode `k = i % 8`, so after regrouping by mode it is
block-diagonal with eight 4×4 mode blocks. Each mode block is chiral
(off-diagonal in the γ-even/γ-odd split), hence its characteristic polynomial
is a biquadratic: a polynomial in `λ²` of `λ²`-degree 2 (≤ 4 as claimed).
Explicitly, with `a = ![yNu, yE, yU, yD, yU, yD, yU, yD]` and
`e k = if k = 0 then yR else 0`:

  charpoly (smDirac yNu yE yU yD yR)
    = ∏ k : Fin 8, (X⁴ − (2·aₖ·āₖ + eₖ·ēₖ) X² + (aₖ·āₖ)²)

Tier: T1 — STANDS WHOLE. Landed 2026-10-22: parent-verified on the
exact shipped text (independent recompile green, token scan
sorry/admit/axiom = 0/0/0, headline `#print axioms` = the standard
three only). Dossier: `whitepaper/charpoly-factorization-2026-10-22.md`.
Nothing here touches `blockedQ4_closedFormGap`, which stays `sorry`:
per-sector closed forms do not survive the `min` selection (Obstruction 2
of the amendment stands untouched).
-/

open Matrix Polynomial

namespace ThetLogos
namespace CharpolyFactorization

/-! ## General machinery -/

/-- The charmatrix of a block-diagonal matrix is the block-diagonal of the
    charmatrices. -/
theorem charmatrix_blockDiagonal {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Type*} [Fintype m] [DecidableEq m]
    (M : ι → Matrix m m R) :
    (Matrix.blockDiagonal M).charmatrix
      = Matrix.blockDiagonal (fun i => (M i).charmatrix) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j
  · subst hij
    by_cases hxy : x = y
    · subst hxy
      simp [Matrix.blockDiagonal_apply_eq]
    · have hne : ((x, i) : m × ι) ≠ (y, i) := by
        intro h
        exact hxy (congrArg Prod.fst h)
      simp [hne, hxy, Matrix.blockDiagonal_apply_eq]
  · have hne : ((x, i) : m × ι) ≠ (y, j) := by
      intro h
      exact hij (congrArg Prod.snd h)
    simp [hne, hij, Matrix.blockDiagonal_apply]

/-- Characteristic polynomial of a block-diagonal matrix is the product of
    the blocks' characteristic polynomials. -/
theorem charpoly_blockDiagonal {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Type*} [Fintype m] [DecidableEq m]
    (M : ι → Matrix m m R) :
    (Matrix.blockDiagonal M).charpoly = ∏ i, (M i).charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_blockDiagonal, Matrix.det_blockDiagonal]

/-- The charmatrix of an off-diagonal block matrix, in block form. -/
theorem charmatrix_fromBlocks_zero {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n R) :
    (Matrix.fromBlocks 0 P Q 0).charmatrix
      = Matrix.fromBlocks (Matrix.scalar n (X : R[X])) (-(C.mapMatrix P))
          (-(C.mapMatrix Q)) (Matrix.scalar n (X : R[X])) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.charmatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.scalar_apply, Matrix.diagonal_apply,
      RingHom.mapMatrix_apply]

/-- **Off-diagonal block charpoly.** For square blocks `P Q`, the
    characteristic polynomial of the chiral block matrix `[[0, P], [Q, 0]]`
    is a polynomial in `X²`: it is `charpoly (Q * P)` composed with `X²`.
    (Proof: one block row operation `L = [[1, 0], [Q, X]]` triangularises
    the charmatrix; both sides pick up the same factor `X ^ card n`.) -/
theorem charpoly_fromBlocks_zero {R : Type*} [Field R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n R) :
    (Matrix.fromBlocks 0 P Q 0).charpoly
      = (Q * P).charpoly.comp (X ^ 2) := by
  classical
  -- The triangularising block matrix and its determinant.
  set L : Matrix (n ⊕ n) (n ⊕ n) R[X] :=
    Matrix.fromBlocks 1 0 (C.mapMatrix Q) (Matrix.scalar n (X : R[X])) with hL
  have hdetL : L.det = (X : R[X]) ^ Fintype.card n := by
    rw [hL, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
    show (Matrix.diagonal (fun _ : n => (X : R[X]))).det = _
    rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
  -- `L * charmatrix = upper block triangular`.
  have hmul : L * (Matrix.fromBlocks 0 P Q 0).charmatrix
      = Matrix.fromBlocks (Matrix.scalar n (X : R[X])) (-(C.mapMatrix P)) 0
          (Matrix.scalar n ((X : R[X]) ^ 2) - C.mapMatrix (Q * P)) := by
    rw [charmatrix_fromBlocks_zero, hL, Matrix.fromBlocks_multiply]
    congr 1
    · -- (1,1): 1 * scalar X + 0 * (-(C.mapMatrix Q)) = scalar X
      simp
    · -- (1,2): 1 * (-(C.mapMatrix P)) + 0 * scalar X = -(C.mapMatrix P)
      simp
    · -- (2,1): (C.mapMatrix Q) * scalar X + scalar X * (-(C.mapMatrix Q)) = 0
      have hc : Commute (Matrix.scalar n (X : R[X])) (C.mapMatrix Q) := by
        refine Matrix.scalar_commute _ ?_ _
        intro r'
        show (X : R[X]) * r' = r' * (X : R[X])
        exact mul_comm _ _
      rw [Matrix.mul_neg, hc.eq, add_neg_cancel]
    · -- (2,2): (C.mapMatrix Q) * (-(C.mapMatrix P)) + scalar X * scalar X
      have hss : Matrix.scalar n (X : R[X]) * Matrix.scalar n (X : R[X])
          = Matrix.scalar n ((X : R[X]) ^ 2) := by
        simp only [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal']
        congr 1
        funext i
        simp [pow_two]
      rw [Matrix.mul_neg, ← map_mul, hss, sub_eq_add_neg, add_comm]
  -- Determinants of both sides.
  have hdet : L.det * (Matrix.fromBlocks 0 P Q 0).charpoly
      = (X : R[X]) ^ Fintype.card n
        * ((Q * P).charpoly.comp (X ^ 2)) := by
    have h1 : L.det * (Matrix.fromBlocks 0 P Q 0).charpoly
        = (L * (Matrix.fromBlocks 0 P Q 0).charmatrix).det := by
      rw [Matrix.det_mul]
      rfl
    have h2 : (L * (Matrix.fromBlocks 0 P Q 0).charmatrix).det
        = (X : R[X]) ^ Fintype.card n * (Matrix.scalar n ((X : R[X]) ^ 2)
            - C.mapMatrix (Q * P)).det := by
      rw [hmul, Matrix.det_fromBlocks_zero₂₁]
      show (Matrix.diagonal (fun _ : n => (X : R[X]))).det * _ = _
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
    have h3 : (Matrix.scalar n ((X : R[X]) ^ 2) - C.mapMatrix (Q * P)).det
        = (Q * P).charpoly.comp (X ^ 2) := by
      have hmap : (Matrix.scalar n ((X : R[X]) ^ 2) - C.mapMatrix (Q * P))
          = (Polynomial.compRingHom (X ^ 2)).mapMatrix (Q * P).charmatrix := by
        apply Matrix.ext
        intro i j
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
            Matrix.scalar_apply, Matrix.diagonal_apply_eq,
            Matrix.charmatrix_apply_eq, map_sub,
            Polynomial.coe_compRingHom_apply, Polynomial.X_comp,
            Polynomial.C_comp]
        · simp only [Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
            Matrix.scalar_apply, Matrix.diagonal_apply, if_neg hij,
            Matrix.charmatrix_apply_ne _ _ _ hij, map_neg,
            Polynomial.coe_compRingHom_apply, Polynomial.C_comp, zero_sub]
      rw [hmap, ← RingHom.map_det]
      show (Polynomial.compRingHom (X ^ 2)) ((Q * P).charmatrix.det)
        = ((Q * P).charmatrix.det).comp (X ^ 2)
      exact Polynomial.coe_compRingHom_apply _ _
    rw [h1, h2, h3]
  rw [hdetL] at hdet
  exact mul_left_cancel₀ (pow_ne_zero _ (X_ne_zero : (X : R[X]) ≠ 0)) hdet

/-- Characteristic polynomial of an explicit 2×2 matrix. -/
theorem charpoly_two_by_two (p q r s : ℂ) :
    (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℂ).charpoly
      = X ^ 2 - C (p + s) * X + C (p * s - q * r) := by
  have hchar : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℂ).charmatrix
      = !![X - C p, -C q; -C r, X - C s] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.charmatrix_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold Matrix.charpoly
  rw [hchar, Matrix.det_fin_two_of]
  simp only [map_add, map_sub, map_mul]
  ring


/-! ## The mode regrouping

`smDirac` couples only indices sharing the mode `k = i % 8` (support lemma
`smDirac_supp_aux`). Regroup the 32 basis indices by mode: each mode carries
a 4-dimensional block indexed by `Fin 2 ⊕ Fin 2`, in the γ-even/γ-odd split
`(H_L, H_R^c) ⊕ (H_R, H_L^c)`. -/

/-- Block (sector) number of a within-mode index: `H_L ↦ 0`, `H_R^c ↦ 3`
    (γ-even, first summand), `H_R ↦ 1`, `H_L^c ↦ 2` (γ-odd, second summand). -/
def modeBase : (Fin 2 ⊕ Fin 2) → ℕ
  | Sum.inl b => if b = 0 then 0 else 3
  | Sum.inr b => if b = 0 then 1 else 2

/-- Inverse of `modeBase` on block numbers `0, 1, 2, 3`. -/
def modeSector : ℕ → (Fin 2 ⊕ Fin 2)
  | 0 => Sum.inl 0
  | 3 => Sum.inl 1
  | 1 => Sum.inr 0
  | _ => Sum.inr 1

theorem modeBase_le (s : Fin 2 ⊕ Fin 2) : modeBase s ≤ 3 := by
  rcases s with (b | b) <;> fin_cases b <;> decide

theorem modeBase_sector (s : Fin 2 ⊕ Fin 2) : modeSector (modeBase s) = s := by
  rcases s with (b | b) <;> fin_cases b <;> decide

theorem modeSector_base (b : ℕ) (hb : b ≤ 3) : modeBase (modeSector b) = b := by
  interval_cases b <;> decide

/-- Every within-mode index is one of the four concrete sectors. -/
theorem sum_fin2_cases (s : Fin 2 ⊕ Fin 2) :
    s = Sum.inl 0 ∨ s = Sum.inl 1 ∨ s = Sum.inr 0 ∨ s = Sum.inr 1 := by
  rcases s with (b | b) <;> fin_cases b <;> simp

/-- The regrouping equivalence `(sector, mode) ≃ Fin 32`,
    `(s, k) ↦ modeBase s * 8 + k`. (The index order matches this Mathlib's
    `Matrix.blockDiagonal`, whose indices are `within × block` pairs.) -/
def modeIdx : ((Fin 2 ⊕ Fin 2) × Fin 8) ≃ Fin 32 where
  toFun sk := ⟨modeBase sk.1 * 8 + sk.2.val, by
    have h1 := modeBase_le sk.1
    have h2 := sk.2.isLt
    omega⟩
  invFun i := (modeSector (i.val / 8), ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩)
  left_inv := by
    intro ⟨s, k⟩
    have hk := k.isLt
    have h1 := modeBase_le s
    refine Prod.ext ?_ ?_
    · show modeSector ((modeBase s * 8 + k.val) / 8) = s
      have hdiv : (modeBase s * 8 + k.val) / 8 = modeBase s := by omega
      rw [hdiv]
      exact modeBase_sector s
    · apply Fin.ext
      show (modeBase s * 8 + k.val) % 8 = k.val
      omega
  right_inv := by
    intro i
    apply Fin.ext
    show modeBase (modeSector (i.val / 8)) * 8 + i.val % 8 = i.val
    have hi := i.isLt
    have hbm : modeBase (modeSector (i.val / 8)) = i.val / 8 :=
      modeSector_base _ (by omega)
    rw [hbm]
    omega

theorem modeIdx_val (s : Fin 2 ⊕ Fin 2) (k : Fin 8) :
    (modeIdx (s, k)).val = modeBase s * 8 + k.val := rfl

/-! ## The mode blocks -/

/-- The diagonal Yukawa values, by mode. -/
def modeYukawa (yNu yE yU yD : ℂ) : Fin 8 → ℂ :=
  ![yNu, yE, yU, yD, yU, yD, yU, yD]

/-- The diagonal Majorana values, by mode (only mode 0 is coupled). -/
def modeMajorana (yR : ℂ) : Fin 8 → ℂ :=
  fun k => if k.val = 0 then yR else 0

theorem majoranaBlock_diag (yR : ℂ) (k : Fin 8) :
    majoranaBlock yR k k = modeMajorana yR k := by
  unfold majoranaBlock modeMajorana
  rw [Matrix.diagonal_apply_eq]

/-- The 4×4 mode block for Yukawa value `a` and Majorana value `e`, in the
    γ-even/γ-odd split: `[[0, P], [Q, 0]]` with `P = !![a, 0; e, a]` and
    `Q = !![ā, ē; 0, ā]`. -/
def modeBlock (a e : ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 !![a, 0; e, a] !![star a, star e; 0, star a] 0

/-! ## Entry lemmas for the regions the corpus does not cover

`FiniteSpectralTriple` provides `buildDirac_B_entry`, `buildDirac_Bdag_entry`
and `buildDirac_Edag_entry`; the `A`, `A†` and `E` regions are proved here in
the same style. -/

theorem buildDirac_A_entry (A B C E : Block8) (i j : I32)
    (hi1 : i.val < 8) (hj1 : ¬ j.val < 8) (hj2 : j.val < 16) :
    buildDirac A B C E i j
      = A ⟨i.val, by omega⟩ ⟨j.val - 8, by omega⟩ := by
  unfold buildDirac
  simp only []
  simp [hi1, hj1, hj2]

theorem buildDirac_Adag_entry (A B C E : Block8) (i j : I32)
    (hi1 : ¬ i.val < 8) (hi2 : i.val < 16) (hj1 : j.val < 8) :
    buildDirac A B C E i j
      = (A.conjTranspose) ⟨i.val - 8, by omega⟩ ⟨j.val, by omega⟩ := by
  unfold buildDirac
  simp only []
  simp [hi1, hi2, hj1]

theorem buildDirac_E_entry (A B C E : Block8) (i j : I32)
    (hi1 : ¬ i.val < 8) (hi2 : ¬ i.val < 16) (hi3 : ¬ i.val < 24)
    (hj1 : ¬ j.val < 8) (hj2 : j.val < 16) :
    buildDirac A B C E i j
      = E ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ := by
  unfold buildDirac
  simp only []
  simp [hi1, hi2, hi3, hj1, hj2]

theorem smDirac_A_entry_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (hi1 : i.val < 8) (hj1 : ¬ j.val < 8) (hj2 : j.val < 16) :
    smDirac yNu yE yU yD yR i j
      = (yukawaBlock yNu yE yU yD) ⟨i.val, by omega⟩ ⟨j.val - 8, by omega⟩ := by
  unfold smDirac
  exact buildDirac_A_entry _ _ _ _ i j hi1 hj1 hj2

theorem smDirac_Adag_entry_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (hi1 : ¬ i.val < 8) (hi2 : i.val < 16) (hj1 : j.val < 8) :
    smDirac yNu yE yU yD yR i j
      = (yukawaBlock yNu yE yU yD).conjTranspose
        ⟨i.val - 8, by omega⟩ ⟨j.val, by omega⟩ := by
  unfold smDirac
  exact buildDirac_Adag_entry _ _ _ _ i j hi1 hi2 hj1

theorem smDirac_E_entry_aux (yNu yE yU yD yR : ℂ) (i j : I32)
    (hi1 : ¬ i.val < 8) (hi2 : ¬ i.val < 16) (hi3 : ¬ i.val < 24)
    (hj1 : ¬ j.val < 8) (hj2 : j.val < 16) :
    smDirac yNu yE yU yD yR i j
      = (majoranaBlock yR) ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ := by
  unfold smDirac
  exact buildDirac_E_entry _ _ _ _ i j hi1 hi2 hi3 hj1 hj2

/-! ## The six nonzero mode entries, specialised to a single mode -/

theorem smDirac_A_entry_mode (yNu yE yU yD yR : ℂ) (k : Fin 8) (i j : I32)
    (hi : i.val = k.val) (hj : j.val = k.val + 8) :
    smDirac yNu yE yU yD yR i j = yukawaBlock yNu yE yU yD k k := by
  have hA := smDirac_A_entry_aux yNu yE yU yD yR i j
    (by omega) (by omega) (by omega)
  have ei : (⟨i.val, by omega⟩ : Fin 8) = k := Fin.ext hi
  have ej : (⟨j.val - 8, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show j.val - 8 = k.val; omega)
  rwa [ei, ej] at hA

theorem smDirac_Adag_entry_mode (yNu yE yU yD yR : ℂ) (k : Fin 8) (i j : I32)
    (hi : i.val = k.val + 8) (hj : j.val = k.val) :
    smDirac yNu yE yU yD yR i j = star (yukawaBlock yNu yE yU yD k k) := by
  have hA := smDirac_Adag_entry_aux yNu yE yU yD yR i j
    (by omega) (by omega) (by omega)
  have ei : (⟨i.val - 8, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show i.val - 8 = k.val; omega)
  have ej : (⟨j.val, by omega⟩ : Fin 8) = k := Fin.ext hj
  rwa [ei, ej, Matrix.conjTranspose_apply] at hA

theorem smDirac_Edag_entry_mode (yNu yE yU yD yR : ℂ) (k : Fin 8) (i j : I32)
    (hi : i.val = k.val + 8) (hj : j.val = k.val + 24) :
    smDirac yNu yE yU yD yR i j = star (majoranaBlock yR k k) := by
  have hA := smDirac_Edag_entry_aux yNu yE yU yD yR i j
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have ei : (⟨i.val - 8, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show i.val - 8 = k.val; omega)
  have ej : (⟨j.val - 24, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show j.val - 24 = k.val; omega)
  rwa [ei, ej, Matrix.conjTranspose_apply] at hA

theorem smDirac_B_entry_mode (yNu yE yU yD yR : ℂ) (k : Fin 8) (i j : I32)
    (hi : i.val = k.val + 16) (hj : j.val = k.val + 24) :
    smDirac yNu yE yU yD yR i j = star (yukawaBlock yNu yE yU yD k k) := by
  have hA := smDirac_B_entry_aux yNu yE yU yD yR i j
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ei : (⟨i.val - 16, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show i.val - 16 = k.val; omega)
  have ej : (⟨j.val - 24, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show j.val - 24 = k.val; omega)
  rwa [ei, ej, Matrix.map_apply, starRingEnd_apply] at hA

theorem smDirac_E_entry_mode (yNu yE yU yD yR : ℂ) (k : Fin 8) (i j : I32)
    (hi : i.val = k.val + 24) (hj : j.val = k.val + 8) :
    smDirac yNu yE yU yD yR i j = majoranaBlock yR k k := by
  have hA := smDirac_E_entry_aux yNu yE yU yD yR i j
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have ei : (⟨i.val - 24, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show i.val - 24 = k.val; omega)
  have ej : (⟨j.val - 8, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show j.val - 8 = k.val; omega)
  rwa [ei, ej] at hA

theorem smDirac_Bdag_entry_mode (yNu yE yU yD yR : ℂ) (k : Fin 8) (i j : I32)
    (hi : i.val = k.val + 24) (hj : j.val = k.val + 16) :
    smDirac yNu yE yU yD yR i j = yukawaBlock yNu yE yU yD k k := by
  have hA := smDirac_Bdag_entry_aux yNu yE yU yD yR i j
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ei : (⟨i.val - 24, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show i.val - 24 = k.val; omega)
  have ej : (⟨j.val - 16, by omega⟩ : Fin 8) = k :=
    Fin.ext (by show j.val - 16 = k.val; omega)
  rwa [ei, ej, Matrix.conjTranspose_apply, Matrix.map_apply, starRingEnd_apply,
    star_star] at hA


theorem modeBase_inl0 : modeBase (Sum.inl 0) = 0 := by decide
theorem modeBase_inl1 : modeBase (Sum.inl 1) = 3 := by decide
theorem modeBase_inr0 : modeBase (Sum.inr 0) = 1 := by decide
theorem modeBase_inr1 : modeBase (Sum.inr 1) = 2 := by decide

/-- Entries of `smDirac` inside one mode are exactly the mode block. -/
theorem smDirac_modeBlock_entry (yNu yE yU yD yR : ℂ) (k : Fin 8)
    (s t : Fin 2 ⊕ Fin 2) :
    smDirac yNu yE yU yD yR (modeIdx (s, k)) (modeIdx (t, k))
      = modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k) s t := by
  have hk8 : k.val < 8 := k.isLt
  have hiv : (modeIdx (s, k)).val = modeBase s * 8 + k.val := rfl
  have hjv : (modeIdx (t, k)).val = modeBase t * 8 + k.val := rfl
  rcases sum_fin2_cases s with rfl | rfl | rfl | rfl <;>
    rcases sum_fin2_cases t with rfl | rfl | rfl | rfl <;>
    simp only [modeBase_inl0, modeBase_inl1, modeBase_inr0, modeBase_inr1] at hiv hjv
  · -- (H_L, H_L): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inl 0) (Sum.inl 0) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_L, H_R^c): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inl 0) (Sum.inl 1) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_L, H_R): the Yukawa block A
    rw [smDirac_A_entry_mode yNu yE yU yD yR k _ _ (by omega) (by omega),
      yukawaBlock_diag]
    simp [modeBlock, modeYukawa]
  · -- (H_L, H_L^c): the C block, which is zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inl 0) (Sum.inr 1) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_R^c, H_L): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inl 1) (Sum.inl 0) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_R^c, H_R^c): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inl 1) (Sum.inl 1) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_R^c, H_R): the Majorana block E
    rw [smDirac_E_entry_mode yNu yE yU yD yR k _ _ (by omega) (by omega),
      majoranaBlock_diag]
    simp [modeBlock]
  · -- (H_R^c, H_L^c): the block B†
    rw [smDirac_Bdag_entry_mode yNu yE yU yD yR k _ _ (by omega) (by omega),
      yukawaBlock_diag]
    simp [modeBlock, modeYukawa]
  · -- (H_R, H_L): the block A†
    rw [smDirac_Adag_entry_mode yNu yE yU yD yR k _ _ (by omega) (by omega),
      yukawaBlock_diag]
    simp [modeBlock, modeYukawa]
  · -- (H_R, H_R^c): the block E†
    rw [smDirac_Edag_entry_mode yNu yE yU yD yR k _ _ (by omega) (by omega),
      majoranaBlock_diag]
    simp [modeBlock]
  · -- (H_R, H_R): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inr 0) (Sum.inr 0) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_R, H_L^c): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inr 0) (Sum.inr 1) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_L^c, H_L): the block C†, which is zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inr 1) (Sum.inl 0) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_L^c, H_R^c): the block B
    rw [smDirac_B_entry_mode yNu yE yU yD yR k _ _ (by omega) (by omega),
      yukawaBlock_diag]
    simp [modeBlock, modeYukawa]
  · -- (H_L^c, H_R): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inr 1) (Sum.inr 0) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · -- (H_L^c, H_L^c): zero
    have hz : modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)
        (Sum.inr 1) (Sum.inr 1) = 0 := by simp [modeBlock]
    rw [hz]
    by_contra hne
    have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega

/-- Entries of `smDirac` between different modes vanish: the support lemma
    forces `j ≡ i (mod 8)`. -/
theorem smDirac_modeBlock_entry_ne (yNu yE yU yD yR : ℂ) {k k' : Fin 8}
    (hkk : k ≠ k') (s t : Fin 2 ⊕ Fin 2) :
    smDirac yNu yE yU yD yR (modeIdx (s, k)) (modeIdx (t, k')) = 0 := by
  by_contra hne
  have hiv : (modeIdx (s, k)).val = modeBase s * 8 + k.val := rfl
  have hjv : (modeIdx (t, k')).val = modeBase t * 8 + k'.val := rfl
  have hb1 : modeBase s ≤ 3 := modeBase_le s
  have hb2 : modeBase t ≤ 3 := modeBase_le t
  have hk8 : k.val < 8 := k.isLt
  have hk8' : k'.val < 8 := k'.isLt
  have hsupp := smDirac_supp_aux yNu yE yU yD yR _ _ hne
  have hkk' : k = k' := by
    apply Fin.ext
    rcases hsupp with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  exact hkk hkk'

/-- `smDirac`, regrouped by mode, is block-diagonal with the mode blocks. -/
theorem smDirac_reindex (yNu yE yU yD yR : ℂ) :
    Matrix.reindex modeIdx.symm modeIdx.symm (smDirac yNu yE yU yD yR)
      = Matrix.blockDiagonal
          (fun k => modeBlock (modeYukawa yNu yE yU yD k) (modeMajorana yR k)) := by
  ext ⟨s, k⟩ ⟨t, k'⟩
  by_cases hkk : k = k'
  · subst hkk
    rw [Matrix.blockDiagonal_apply_eq]
    exact smDirac_modeBlock_entry yNu yE yU yD yR k s t
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hkk]
    exact smDirac_modeBlock_entry_ne yNu yE yU yD yR hkk s t

/-! ## The mode factor and the assembly -/

/-- The characteristic polynomial of one mode block:
    `X⁴ − (2·a·ā + e·ē) X² + (a·ā)²`, a biquadratic. -/
noncomputable def modeFactor (a e : ℂ) : ℂ[X] :=
  X ^ 4 - C (2 * (a * star a) + e * star e) * X ^ 2 + C ((a * star a) ^ 2)

theorem modeBlock_charpoly (a e : ℂ) :
    (modeBlock a e).charpoly = modeFactor a e := by
  have hmul : (!![star a, star e; 0, star a] : Matrix (Fin 2) (Fin 2) ℂ)
        * !![a, 0; e, a]
      = !![star a * a + star e * e, star e * a; star a * e, star a * a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have htr : (star a * a + star e * e) + star a * a
      = 2 * (a * star a) + e * star e := by ring
  have hdet : (star a * a + star e * e) * (star a * a)
      - (star e * a) * (star a * e) = (a * star a) ^ 2 := by ring
  unfold modeBlock modeFactor
  rw [charpoly_fromBlocks_zero, hmul, charpoly_two_by_two, htr, hdet]
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sub_comp,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp]
  ring

/-- Each mode factor is a polynomial in `X²` whose `X²`-degree is `≤ 2`
    (hence `≤ 4`, the amendment's bound): it is `charpoly (Q * P)` composed
    with `X²` for the mode block's off-diagonal factors. -/
theorem modeFactor_sq_form (a e : ℂ) :
    ∃ q : ℂ[X], q.natDegree ≤ 2 ∧ modeFactor a e = q.comp (X ^ 2) := by
  refine ⟨(!![star a, star e; 0, star a] * !![a, 0; e, a]).charpoly, ?_, ?_⟩
  · rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  · rw [← modeBlock_charpoly]
    exact charpoly_fromBlocks_zero _ _

/-- **Q4 Path B, settled for the corpus's `D_F`.** The characteristic
    polynomial of `smDirac` splits into eight sector (mode) factors, each a
    biquadratic — a polynomial in `λ²` of `λ²`-degree `≤ 2 ≤ 4`. -/
theorem charpoly_smDirac (yNu yE yU yD yR : ℂ) :
    (smDirac yNu yE yU yD yR).charpoly
      = ∏ k : Fin 8, modeFactor (modeYukawa yNu yE yU yD k)
          (modeMajorana yR k) := by
  rw [← Matrix.charpoly_reindex modeIdx.symm, smDirac_reindex, charpoly_blockDiagonal]
  exact Finset.prod_congr rfl fun k _ => modeBlock_charpoly _ _

/-- The factorisation grouped by flavour: the neutrino sector carries the
    Majorana correction; the electron and the three colours of up- and
    down-quarks are perfect squares `(X² − y·ȳ)²` with multiplicity. -/
theorem charpoly_smDirac_grouped (yNu yE yU yD yR : ℂ) :
    (smDirac yNu yE yU yD yR).charpoly
      = modeFactor yNu yR * (X ^ 2 - C (yE * star yE)) ^ 2
        * ((X ^ 2 - C (yU * star yU)) ^ 2) ^ 3
        * ((X ^ 2 - C (yD * star yD)) ^ 2) ^ 3 := by
  have hfac0 : ∀ a : ℂ, modeFactor a 0 = (X ^ 2 - C (a * star a)) ^ 2 := by
    intro a
    unfold modeFactor
    simp only [map_add, map_mul, map_pow, map_ofNat, zero_mul, add_zero]
    ring
  rw [charpoly_smDirac, Fin.prod_univ_eight]
  simp [modeYukawa, modeMajorana, hfac0]
  ring

end CharpolyFactorization
end ThetLogos
