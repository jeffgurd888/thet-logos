import ThetLogos.Census96EightyEight

/-!
# ThetLogos.Census96PairBound - C96-3b2: the `<= 88` bound for `PairSpace`

Continuation of C96-3b (lane 2 of the Census-96 line; pack
`pack-c96-3b2.md`). C96-3b landed `dir88_independent` and
`finrank_ge_88 : 88 <= Module.finrank R PairSpace`, and named the
stall: the cross-coordinate support-forcing theorem for a general
element of `PairSpace`. This module is exactly that stall:

1. **Reconstruction.** A pair-space element `M` is the folded
   assembly `admBlockMatOf` of its folded cross-block
   `Z = crossCoordOf M` (the landed `AdmBlock` parameterization of
   C96-1), and the self-adjoint partner is the folded transpose:
   `(admBlockMatOf Z).conjTranspose = admBlockMatOf (Z o swap)`.
   Hence both order-one conditions of `mem_pairSpace_iff` are
   conditions on the single folded block `Z`.

2. **Support forcing.** Testing the order-one condition of `M`
   against the generated algebra (C96-1b's bridge `orderOne_adjoin`)
   with the diagonal support projectors `projC`, `projH`, `projM`
   and their opposites kills every folded coordinate outside the
   44 ordered slots of C96-3b (A-slots 8, flip slots 8, both orders
   of the 12 E-pairs 24, `(8,9)`/`(9,8)`, diagonals `(8,8)`/`(9,9)`);
   the remaining off-slot coordinates are killed by the Pauli /
   Gell-Mann generator tests. The capstone is the determination
   theorem `pairSpace_eq_zero_of_repCoord_eq_zero`: a `PairSpace`
   element whose 44 representative folded coordinates all vanish
   is zero.

3. **Injection + equality.** The pivot-evaluation map
   `pairSpacePivotMap` (the 44 folded coordinates, as a real
   linear map into `Fin 44 -> C`) is injective by determination
   (`pairSpacePivotMap_injective`), so
   `finrank_pairSpace_le : finrank R PairSpace <= 88`; with
   C96-3b's `finrank_ge_88`, `finrank_pairSpace_eq :
   finrank R PairSpace = 88`.

## Kills and fences (on the face)

- K-C96-1 (armed): a PROVED 89th independent direction, or any
  proved finrank of `PairSpace` different from 88, kills the T4
  note at full rank. This module proves the registered number 88
  or reports a partial at the named seam; a stall is a stall.
- K-C96-2 (vacuity): the bound is a support theorem about a general
  element, not a slot count.
- Generations IMPOSED; CKM/PMNS input-only; Q3 OPEN; NO CLAIM.
  The old 46 -> 10 gloss is UNSOUND AS STATED and is not cited.
-/

open Matrix

namespace ThetLogos

/-! ## 1. Reconstruction of a pair from its folded cross-block -/

/-- **Reconstruction.** A block-admissible matrix is the folded
    assembly of its own folded cross-block. The four grading cases:
    same-sign entries vanish (grading-oddness), the `(+, -)` entry
    is the folded value at the recovered indices, and the `(-, +)`
    entry is its conjugate by the J-coupling
    `admBlock_entry_star`. -/
theorem admBlock_eq_admBlockMatOf_crossCoordOf {M : Matrix I32 I32 ℂ}
    (hM : IsAdmBlock M) :
    M = admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M p.1 p.2) := by
  ext i j
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have h0 : M i j = 0 :=
      gammaOdd_entry_eq_zero_of_gSign_eq M hM.1 (by rw [hi, hj])
    rw [h0]
    simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, ite_true]
  · have e1 : admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M p.1 p.2) i j
        = crossCoordOf M (acoord i) (acoord j) := by
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    rw [e1]
    unfold crossCoordOf
    rw [plusEmb_acoord_of_gSign_eq_one hi,
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hj]
  · have e1 : admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M p.1 p.2) i j
        = star (crossCoordOf M (acoord i) (acoord j)) := by
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    rw [e1]
    have h2 : crossCoordOf M (acoord i) (acoord j)
        = M (partner i) (partner j) := by
      unfold crossCoordOf
      have e2 : plusEmb (acoord i) = partner i :=
        plusEmb_acoord_eq_partner_of_gSign_eq_neg_one hi
      have e3 : minusEmb (flip8 (acoord j)) = partner j :=
        minusEmb_flip8_acoord_eq_partner_of_gSign_eq_one hj
      rw [e2, e3]
    rw [h2, admBlock_entry_star M hM]
  · have h0 : M i j = 0 :=
      gammaOdd_entry_eq_zero_of_gSign_eq M hM.1 (by rw [hi, hj])
    rw [h0]
    simp only [admBlockMatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]

/-- Reconstruction for a pair-space element. -/
theorem pairSpace_eq_admBlockMatOf_crossCoordOf {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    M = admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M p.1 p.2) :=
  admBlock_eq_admBlockMatOf_crossCoordOf hM.1

/-- **The folded transpose.** Conjugate-transposition of a folded
    assembly swaps the folded coordinates (the two stars of the
    pair parameterization cancel, as in the landed
    `exPairMat_conjTranspose`). -/
theorem admBlockMatOf_conjTranspose (Z : Fin 16 × Fin 16 → ℂ) :
    (admBlockMatOf Z).conjTranspose
      = admBlockMatOf (fun p : Fin 16 × Fin 16 => Z (p.2, p.1)) := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj | hj
  · have e1 : admBlockMatOf Z j i = 0 := by
      simp only [admBlockMatOf_apply, hj, hi, eq_self_iff_true, ite_true]
    have e2 : admBlockMatOf (fun p : Fin 16 × Fin 16 => Z (p.2, p.1)) i j = 0 := by
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true, ite_true]
    rw [e1, e2, star_zero]
  · have e1 : admBlockMatOf Z j i = star (Z (acoord j, acoord i)) := by
      simp only [admBlockMatOf_apply, hj, hi, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    have e2 : admBlockMatOf (fun p : Fin 16 × Fin 16 => Z (p.2, p.1)) i j
        = Z (acoord j, acoord i) := by
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    rw [e1, e2, star_star]
  · have e1 : admBlockMatOf Z j i = Z (acoord j, acoord i) := by
      simp only [admBlockMatOf_apply, hj, hi, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    have e2 : admBlockMatOf (fun p : Fin 16 × Fin 16 => Z (p.2, p.1)) i j
        = star (Z (acoord j, acoord i)) := by
      simp only [admBlockMatOf_apply, hi, hj, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    rw [e1, e2]
  · have e1 : admBlockMatOf Z j i = 0 := by
      simp only [admBlockMatOf_apply, hj, hi, neg_one_ne_one_complex, ite_false]
    have e2 : admBlockMatOf (fun p : Fin 16 × Fin 16 => Z (p.2, p.1)) i j = 0 := by
      simp only [admBlockMatOf_apply, hi, hj, neg_one_ne_one_complex, ite_false]
    rw [e1, e2, star_zero]

end ThetLogos


namespace ThetLogos

/-! ## 2. The diagonal support projectors, entrywise

The bridge (C96-1b) lets the order-one condition of a pair-space
element be tested against every element of the generated algebra
and its opposite. The first tests are the diagonal support
projectors `projC`, `projH`, `projM` and their opposites: at an
entry `(i, j)` the double commutator with diagonal `P`, `Q` is
`M i j * (p j - p i) * (q j - q i)`, so the entry dies whenever
some left projector and some right projector both separate `i`
from `j`. -/

/-- The C-support indicator (the diagonal of `projC`). -/
def indC (i : I32) : ℂ :=
  if (8 ≤ i.val ∧ i.val < 16) ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25
    then 1 else 0

/-- The H-support indicator (the diagonal of `projH`). -/
def indH (i : I32) : ℂ := if i.val < 8 then 1 else 0

/-- The M-support indicator (the diagonal of `projM`). -/
def indM (i : I32) : ℂ :=
  if (18 ≤ i.val ∧ i.val < 24) ∨ (26 ≤ i.val ∧ i.val < 32) then 1 else 0

/-- `projC` is the diagonal C-support projector. -/
theorem projC_eq_diagonal : projC = Matrix.diagonal indC := by
  have hdef : projC = -(genC * genC) := rfl
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hdef, Matrix.diagonal_apply, if_pos rfl, indC]
    exact genC_sq_proj i
  · rw [hdef, Matrix.diagonal_apply, if_neg hij]
    exact genC_sq_proj_offdiag hij

/-- `projH` is the diagonal H-support projector. -/
theorem projH_eq_diagonal : projH = Matrix.diagonal indH := by
  have hdef : projH = genH 0 * genH 0 := rfl
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hdef, Matrix.diagonal_apply, if_pos rfl, indH]
    exact genH_sq_proj 0 i
  · rw [hdef, Matrix.diagonal_apply, if_neg hij]
    exact genH_sq_offdiag 0 hij

/-- `projM` is the diagonal M-support projector. -/
theorem projM_eq_diagonal : projM = Matrix.diagonal indM := by
  have hdef : projM = (3 / 16 : ℂ) • ∑ a : Fin 8, genM a * genM a := rfl
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hdef, Matrix.diagonal_apply, if_pos rfl, indM]
    exact smul_genM_sq_sum_proj i
  · rw [hdef, Matrix.diagonal_apply, if_neg hij, Matrix.smul_apply,
      genM_sq_sum_offdiag hij, smul_zero]

/-- The opposite of a diagonal matrix is diagonal, with the
    partner-pulled-back values. -/
theorem opLin_diagonal (d : I32 → ℂ) :
    opLin (Matrix.diagonal d) = Matrix.diagonal (fun i => d (partner i)) := by
  ext i j
  rw [opLin_apply, UJ_conj_apply, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply, if_pos rfl, if_pos rfl]
  · have hne : partner j ≠ partner i :=
      fun h => hij ((Function.Involutive.injective partner_involutive h).symm)
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply, if_neg hij, if_neg hne]

/-- The opposite C-projector, as a diagonal matrix. -/
theorem opLin_projC_eq_diagonal :
    opLin projC = Matrix.diagonal (fun i => indC (partner i)) := by
  rw [projC_eq_diagonal, opLin_diagonal]

/-- The opposite H-projector, as a diagonal matrix. -/
theorem opLin_projH_eq_diagonal :
    opLin projH = Matrix.diagonal (fun i => indH (partner i)) := by
  rw [projH_eq_diagonal, opLin_diagonal]

/-- The opposite M-projector, as a diagonal matrix. -/
theorem opLin_projM_eq_diagonal :
    opLin projM = Matrix.diagonal (fun i => indM (partner i)) := by
  rw [projM_eq_diagonal, opLin_diagonal]

/-- Entry of a product with a diagonal matrix on the right. -/
theorem mul_diagonal_apply (M : Matrix I32 I32 ℂ) (q : I32 → ℂ) (i j : I32) :
    (M * Matrix.diagonal q) i j = M i j * q j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro k _ hkj
    rw [Matrix.diagonal_apply, if_neg hkj, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

/-- Entry of a product with a diagonal matrix on the left. -/
theorem diagonal_mul_apply (p : I32 → ℂ) (M : Matrix I32 I32 ℂ) (i j : I32) :
    (Matrix.diagonal p * M) i j = p i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro k _ hki
    rw [Matrix.diagonal_apply, if_neg (Ne.symm hki), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-- **The diagonal double-commutator entry.** Against diagonal
    algebra elements the double commutator is entrywise scalar:
    `[[M, P], Q] i j = M i j * (p j - p i) * (q j - q i)`. -/
theorem dcGen_diagonal_apply (M : Matrix I32 I32 ℂ) (p q : I32 → ℂ)
    (i j : I32) :
    dcGen M (Matrix.diagonal p) (Matrix.diagonal q) i j
      = M i j * (p j - p i) * (q j - q i) := by
  have hX : ∀ a b : I32, (M * Matrix.diagonal p - Matrix.diagonal p * M) a b
      = M a b * (p b - p a) := by
    intro a b
    rw [Matrix.sub_apply, mul_diagonal_apply, diagonal_mul_apply]
    ring
  unfold dcGen
  rw [Matrix.sub_apply, mul_diagonal_apply, diagonal_mul_apply, hX i j]
  ring

/-- **Diagonal forcing.** If a left-algebra element and a
    right-algebra element are diagonal with values `p`, `q` both
    separating `i` from `j`, then a pair-space element vanishes
    at `(i, j)`. -/
theorem pairSpace_entry_eq_zero_of_diag_ne {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {X Y : Matrix I32 I32 ℂ} {p q : I32 → ℂ}
    (hX : X = Matrix.diagonal p) (hY : Y = Matrix.diagonal q)
    (hXm : X ∈ smGenAlgebra) (hYm : Y ∈ smGenOpAlgebra)
    {i j : I32} (hp : p j ≠ p i) (hq : q j ≠ q i) : M i j = 0 := by
  have h := orderOne_adjoin M hM.2.2.1 X hXm Y hYm
  have he := congrFun (congrFun h i) j
  rw [hX, hY, dcGen_diagonal_apply, Matrix.zero_apply] at he
  rcases mul_eq_zero.mp he with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.mp h2) hp
  · exact absurd (sub_eq_zero.mp h1) hq

end ThetLogos


namespace ThetLogos

/-! ## 3. Diagonal forcing on folded coordinates

The six diagonal kill regions. With `i = plusEmb u` (a plus index)
and `j = minusEmb (flip8 v)` (a minus index), the folded entry is
`crossCoordOf M u v = M i j`; the diagonal projectors separate
`i` from `j` on both sides exactly in the six regions below, and
the survivors are the six regions R1-R6 of the next section. -/

/-- Value of a plus embedding, small folded coordinate. -/
theorem plusEmb_val_eq_of_lt {u : Fin 16} (h : u.val < 8) :
    (plusEmb u).val = u.val := by
  rw [plusEmb_val, if_pos h]

/-- Value of a plus embedding, large folded coordinate. -/
theorem plusEmb_val_eq_of_ge {u : Fin 16} (h : 8 ≤ u.val) :
    (plusEmb u).val = u.val + 16 := by
  rw [plusEmb_val, if_neg (by omega : ¬ u.val < 8)]

/-- Value of a minus embedding, small folded coordinate. -/
theorem minusEmb_flip8_val_lt {v : Fin 16} (h : v.val < 8) :
    (minusEmb (flip8 v)).val = v.val + 16 := by
  rw [minusEmb_val, flip8_val, if_pos h]

/-- Value of a minus embedding, large folded coordinate. -/
theorem minusEmb_flip8_val_ge {v : Fin 16} (h : 8 ≤ v.val) :
    (minusEmb (flip8 v)).val = v.val := by
  have hv := v.isLt
  rw [minusEmb_val, flip8_val, if_neg (by omega : ¬ v.val < 8)]
  omega

/-- Partner of a plus embedding, small folded coordinate. -/
theorem partner_plusEmb_val_lt {u : Fin 16} (h : u.val < 8) :
    (partner (plusEmb u)).val = u.val + 16 := by
  rw [partner_val_eq, plusEmb_val_eq_of_lt h, if_pos (by omega : u.val < 16)]

/-- Partner of a plus embedding, large folded coordinate. -/
theorem partner_plusEmb_val_ge {u : Fin 16} (h : 8 ≤ u.val) :
    (partner (plusEmb u)).val = u.val := by
  rw [partner_val_eq, plusEmb_val_eq_of_ge h,
    if_neg (by omega : ¬ u.val + 16 < 16)]
  omega

/-- Partner of a minus embedding, small folded coordinate. -/
theorem partner_minusEmb_flip8_val_lt {v : Fin 16} (h : v.val < 8) :
    (partner (minusEmb (flip8 v))).val = v.val := by
  rw [partner_val_eq, minusEmb_flip8_val_lt h,
    if_neg (by omega : ¬ v.val + 16 < 16)]
  omega

/-- Partner of a minus embedding, large folded coordinate. -/
theorem partner_minusEmb_flip8_val_ge {v : Fin 16} (h : 8 ≤ v.val) :
    (partner (minusEmb (flip8 v))).val = v.val + 16 := by
  have hv := v.isLt
  rw [partner_val_eq, minusEmb_flip8_val_ge h, if_pos (by omega : v.val < 16)]

/-- K1: the whole `(u < 8, v < 8)` quadrant dies, via
    `projH` against its opposite. -/
theorem pairSpace_crossCoord_eq_zero_K1 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {u v : Fin 16} (hu : u.val < 8) (hv : v.val < 8) :
    crossCoordOf M u v = 0 := by
  show M (plusEmb u) (minusEmb (flip8 v)) = 0
  apply pairSpace_entry_eq_zero_of_diag_ne hM projH_eq_diagonal
    opLin_projH_eq_diagonal projH_mem_adjoin
    (opLin_mem_adjoinOp projH projH_mem_adjoin)
  · unfold indH
    rw [minusEmb_flip8_val_lt hv, plusEmb_val_eq_of_lt hu,
      if_neg (by omega : ¬ v.val + 16 < 8), if_pos hu]
    exact zero_ne_one
  · unfold indH
    rw [partner_minusEmb_flip8_val_lt hv, partner_plusEmb_val_lt hu,
      if_pos hv, if_neg (by omega : ¬ u.val + 16 < 8)]
    exact one_ne_zero

/-- K2: `(u in {0,1}, v >= 10)` dies, via `projC` against the
    opposite M-projector. -/
theorem pairSpace_crossCoord_eq_zero_K2 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {u v : Fin 16} (hu : u.val = 0 ∨ u.val = 1)
    (hv : 10 ≤ v.val) : crossCoordOf M u v = 0 := by
  show M (plusEmb u) (minusEmb (flip8 v)) = 0
  apply pairSpace_entry_eq_zero_of_diag_ne hM projC_eq_diagonal
    opLin_projM_eq_diagonal projC_mem_adjoin
    (opLin_mem_adjoinOp projM projM_mem_adjoin)
  · unfold indC
    have hvlt := v.isLt
    have hult : u.val < 8 := by rcases hu with h | h <;> omega
    rw [minusEmb_flip8_val_ge (by omega : 8 ≤ v.val),
      plusEmb_val_eq_of_lt hult, if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero
  · unfold indM
    have hvlt := v.isLt
    rw [partner_minusEmb_flip8_val_ge (by omega : 8 ≤ v.val),
      partner_plusEmb_val_lt (by rcases hu with h | h <;> omega),
      if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero

/-- K3: `(u in 2..7, v in {8,9})` dies, via `projC` against its
    opposite. -/
theorem pairSpace_crossCoord_eq_zero_K3 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {u v : Fin 16} (hu : 2 ≤ u.val ∧ u.val < 8)
    (hv : v.val = 8 ∨ v.val = 9) : crossCoordOf M u v = 0 := by
  show M (plusEmb u) (minusEmb (flip8 v)) = 0
  apply pairSpace_entry_eq_zero_of_diag_ne hM projC_eq_diagonal
    opLin_projC_eq_diagonal projC_mem_adjoin
    (opLin_mem_adjoinOp projC projC_mem_adjoin)
  · unfold indC
    have hvlt := v.isLt
    rw [minusEmb_flip8_val_ge (by omega : 8 ≤ v.val),
      plusEmb_val_eq_of_lt hu.2, if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero
  · unfold indC
    rw [partner_minusEmb_flip8_val_ge (by omega : 8 ≤ v.val),
      partner_plusEmb_val_lt hu.2, if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero

/-- K4: `(u in {8,9}, v in 2..7)` dies, via `projM` against the
    opposite C-projector. -/
theorem pairSpace_crossCoord_eq_zero_K4 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 2 ≤ v.val ∧ v.val < 8) : crossCoordOf M u v = 0 := by
  show M (plusEmb u) (minusEmb (flip8 v)) = 0
  apply pairSpace_entry_eq_zero_of_diag_ne hM projM_eq_diagonal
    opLin_projC_eq_diagonal projM_mem_adjoin
    (opLin_mem_adjoinOp projC projC_mem_adjoin)
  · unfold indM
    rw [minusEmb_flip8_val_lt hv.2, plusEmb_val_eq_of_ge (by omega : 8 ≤ u.val),
      if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero
  · unfold indC
    rw [partner_minusEmb_flip8_val_lt hv.2,
      partner_plusEmb_val_ge (by omega : 8 ≤ u.val),
      if_neg (by omega), if_pos (by omega)]
    exact zero_ne_one

/-- K5: `(u in 10..15, v in {0,1})` dies, via `projC` against its
    opposite. -/
theorem pairSpace_crossCoord_eq_zero_K5 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {u v : Fin 16} (hu : 10 ≤ u.val)
    (hv : v.val = 0 ∨ v.val = 1) : crossCoordOf M u v = 0 := by
  show M (plusEmb u) (minusEmb (flip8 v)) = 0
  apply pairSpace_entry_eq_zero_of_diag_ne hM projC_eq_diagonal
    opLin_projC_eq_diagonal projC_mem_adjoin
    (opLin_mem_adjoinOp projC projC_mem_adjoin)
  · unfold indC
    have hult := u.isLt
    rw [minusEmb_flip8_val_lt (by rcases hv with h | h <;> omega),
      plusEmb_val_eq_of_ge (by omega : 8 ≤ u.val),
      if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero
  · unfold indC
    rw [partner_minusEmb_flip8_val_lt (by rcases hv with h | h <;> omega),
      partner_plusEmb_val_ge (by omega : 8 ≤ u.val),
      if_neg (by omega), if_pos (by omega)]
    exact zero_ne_one

/-- K6: `(u in 10..15, v in 10..15)` dies, via `projC` against the
    opposite M-projector. -/
theorem pairSpace_crossCoord_eq_zero_K6 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {u v : Fin 16} (hu : 10 ≤ u.val)
    (hv : 10 ≤ v.val) : crossCoordOf M u v = 0 := by
  show M (plusEmb u) (minusEmb (flip8 v)) = 0
  apply pairSpace_entry_eq_zero_of_diag_ne hM projC_eq_diagonal
    opLin_projM_eq_diagonal projC_mem_adjoin
    (opLin_mem_adjoinOp projM projM_mem_adjoin)
  · unfold indC
    have hvlt := v.isLt
    rw [minusEmb_flip8_val_ge (by omega : 8 ≤ v.val),
      plusEmb_val_eq_of_ge (by omega : 8 ≤ u.val),
      if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero
  · unfold indM
    have hvlt := v.isLt
    rw [partner_minusEmb_flip8_val_ge (by omega : 8 ≤ v.val),
      partner_plusEmb_val_ge (by omega : 8 ≤ u.val),
      if_pos (by omega), if_neg (by omega)]
    exact one_ne_zero

end ThetLogos


namespace ThetLogos

/-! ## 4. The partner side: folded coordinates of `M-dagger`

The Gell-Mann forcing of the next section is proved once, on the
`(10..15, 2..7)` folded region, and transported to the
`(2..7, 10..15)` region through the self-adjoint partner: the
partner's folded block is the transpose of the original folded
block. -/

/-- The double commutator against a diagonal right element is
    entrywise scalar in the inner commutator. -/
theorem dcGen_diagonal_right_apply (M X : Matrix I32 I32 ℂ)
    (q : I32 → ℂ) (i j : I32) :
    dcGen M X (Matrix.diagonal q) i j
      = (M * X - X * M) i j * (q j - q i) := by
  unfold dcGen
  rw [Matrix.sub_apply, mul_diagonal_apply, diagonal_mul_apply]
  ring

/-- The self-adjoint partner of a pair-space element is again in
    the pair space (the four conditions are symmetric in the two
    members). -/
theorem pairSpace_conjTranspose_mem {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) : M.conjTranspose ∈ PairSpace := by
  refine ⟨hM.2.1, ?_, hM.2.2.2, ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]; exact hM.1
  · rw [Matrix.conjTranspose_conjTranspose]; exact hM.2.2.1

/-- Folded coordinates read back an assembled block. -/
theorem crossCoordOf_admBlockMatOf (Z : Fin 16 × Fin 16 → ℂ)
    (u v : Fin 16) : crossCoordOf (admBlockMatOf Z) u v = Z (u, v) := by
  unfold crossCoordOf
  have e1 : admBlockMatOf Z (plusEmb u) (minusEmb (flip8 v))
      = Z (acoord (plusEmb u), acoord (minusEmb (flip8 v))) := by
    simp only [admBlockMatOf_apply, gSign_plusEmb, gSign_minusEmb,
      eq_self_iff_true, neg_one_ne_one_complex, ite_true, ite_false]
  rw [e1, acoord_plusEmb, acoord_minusEmb, flip8_flip8]

/-- **Folded transpose.** The partner's folded block is the
    transpose of the folded block. -/
theorem crossCoordOf_conjTranspose {M : Matrix I32 I32 ℂ}
    (hM : IsAdmBlock M) (u v : Fin 16) :
    crossCoordOf M.conjTranspose u v = crossCoordOf M v u := by
  have h2 : M.conjTranspose
      = admBlockMatOf (fun p : Fin 16 × Fin 16 => crossCoordOf M p.2 p.1) := by
    have h3 := admBlockMatOf_conjTranspose
      (fun p : Fin 16 × Fin 16 => crossCoordOf M p.1 p.2)
    rwa [← admBlock_eq_admBlockMatOf_crossCoordOf hM] at h3
  rw [h2]
  simp only [crossCoordOf_admBlockMatOf]

end ThetLogos


namespace ThetLogos

/-! ## 5. Gell-Mann forcing on the antiparticle region R4

For a pair-space element `M`, the double commutator against
`genM a` (left) and the opposite C-projector (right, diagonal with
factor `-1` on the region) says the commutator `[M, genM a]`
vanishes at every `(tripletIdx t p, tripletIdx t' q)` entry with
`t >= 2`, `t' < 2`. Entrywise this says each folded colour block
`B(p, q) = M (tripletIdx t p) (tripletIdx t' q)` commutes with
every Gell-Mann matrix; commuting with `gellMann 2` (eigenvalues
`1, -1, 0`, all distinct) kills the colour-off-diagonal entries,
and commuting with `gellMann 0` / `gellMann 5` links the three
colour-diagonal values. -/

/-- Value of a triplet index. -/
theorem tripletIdx_val (t : Fin 4) (p : Fin 3) :
    (tripletIdx t p).val
      = (if t.val < 2 then 18 else 26) + 2 * p.val + t.val % 2 := rfl

/-- Partner value of a triplet index in the antiparticle range. -/
theorem partner_tripletIdx_val_ge {t : Fin 4} (ht : 2 ≤ t.val) (p : Fin 3) :
    (partner (tripletIdx t p)).val = 10 + 2 * p.val + t.val % 2 := by
  have hp := p.isLt
  rw [partner_val_eq, tripletIdx_val, if_neg (by omega : ¬ t.val < 2),
    if_neg (by omega : ¬ (26 + 2 * p.val + t.val % 2) < 16)]
  omega

/-- Partner value of a triplet index in the particle range. -/
theorem partner_tripletIdx_val_lt {t : Fin 4} (ht : t.val < 2) (p : Fin 3) :
    (partner (tripletIdx t p)).val = 2 + 2 * p.val + t.val % 2 := by
  have hp := p.isLt
  rw [partner_val_eq, tripletIdx_val, if_pos ht,
    if_neg (by omega : ¬ (18 + 2 * p.val + t.val % 2) < 16)]
  omega

/-- The opposite C-projector is `1` on antiparticle triplets. -/
theorem indC_partner_tripletIdx_ge {t : Fin 4} (ht : 2 ≤ t.val) (p : Fin 3) :
    indC (partner (tripletIdx t p)) = 1 := by
  have hp := p.isLt
  unfold indC
  rw [partner_tripletIdx_val_ge ht p, if_pos (Or.inl ⟨by omega, by omega⟩)]

/-- The opposite C-projector is `0` on particle triplets. -/
theorem indC_partner_tripletIdx_lt {t : Fin 4} (ht : t.val < 2) (p : Fin 3) :
    indC (partner (tripletIdx t p)) = 0 := by
  have hp := p.isLt
  unfold indC
  rw [partner_tripletIdx_val_lt ht p, if_neg (by omega)]

/-- **The commutator entry on the triplet region.** Testing
    order-one against `genM a` and the opposite C-projector kills
    the `(triplet, triplet)` entries of `[M, genM a]`. -/
theorem pairSpace_comm_genM_entry {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace)
    (a : Fin 8) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    (p q : Fin 3) :
    (M * genM a - genM a * M) (tripletIdx t p) (tripletIdx t' q) = 0 := by
  have h := orderOne_adjoin M hM.2.2.1 (genM a) (genM_mem_adjoin a)
    (opLin projC) (opLin_mem_adjoinOp projC projC_mem_adjoin)
  have he := congrFun (congrFun h (tripletIdx t p)) (tripletIdx t' q)
  simp only [opLin_projC_eq_diagonal, dcGen_diagonal_right_apply,
    indC_partner_tripletIdx_ge ht p, indC_partner_tripletIdx_lt ht' q,
    Matrix.zero_apply] at he
  have he2 : (M * genM a - genM a * M) (tripletIdx t p) (tripletIdx t' q)
      * (-1 : ℂ) = 0 := by
    have h01 : (0 : ℂ) - 1 = -1 := by norm_num
    rwa [h01] at he
  rcases mul_eq_zero.mp he2 with hX | hX
  · exact hX
  · norm_num at hX

/-- Entry of `M * genM a` on a triplet block: the sum over the
    intermediate index collapses to the three triplet mates. -/
theorem mul_genM_apply_triplet {M : Matrix I32 I32 ℂ} (a : Fin 8)
    (t t' : Fin 4) (p q : Fin 3) :
    (M * genM a) (tripletIdx t p) (tripletIdx t' q)
      = ∑ p' : Fin 3, M (tripletIdx t p) (tripletIdx t' p')
          * gellMann a p' q := by
  have hvan : ∀ l : I32, l ∉ Finset.image (tripletIdx t') Finset.univ →
      M (tripletIdx t p) l * genM a l (tripletIdx t' q) = 0 := by
    intro l hl
    by_cases g1 : genM a l (tripletIdx t' q) = 0
    · rw [g1, mul_zero]
    · exfalso
      obtain ⟨t1, p1, q1, h1, h2⟩ := genM_supp_triplet a l (tripletIdx t' q) g1
      have htt : t1 = t' := by
        have h := h2.symm.trans (tripletIdx_spec t' q)
        exact congrArg Prod.fst (Option.some_inj.mp h)
      rw [htt] at h1
      exact hl (Finset.mem_image.mpr ⟨p1, Finset.mem_univ p1, (tripletOf_inv l t' p1 h1).symm⟩)
  rw [Matrix.mul_apply, sum_I32_support _ hvan,
    Finset.sum_image (fun x _ y _ hxy => tripletIdx_inj t' x y hxy)]
  apply Finset.sum_congr rfl
  intro p' _
  rw [genM_apply_eq a (tripletIdx t' p') (tripletIdx t' q) t' p' q
    (tripletIdx_spec t' p') (tripletIdx_spec t' q)]

/-- Entry of `genM a * M` on a triplet block. -/
theorem genM_mul_apply_triplet {M : Matrix I32 I32 ℂ} (a : Fin 8)
    (t t' : Fin 4) (p q : Fin 3) :
    (genM a * M) (tripletIdx t p) (tripletIdx t' q)
      = ∑ q' : Fin 3, gellMann a p q'
          * M (tripletIdx t q') (tripletIdx t' q) := by
  have hvan : ∀ l : I32, l ∉ Finset.image (tripletIdx t) Finset.univ →
      genM a (tripletIdx t p) l * M l (tripletIdx t' q) = 0 := by
    intro l hl
    by_cases g1 : genM a (tripletIdx t p) l = 0
    · rw [g1, zero_mul]
    · exfalso
      obtain ⟨t1, p1, q1, h1, h2⟩ := genM_supp_triplet a (tripletIdx t p) l g1
      have htt : t1 = t := by
        have h := h1.symm.trans (tripletIdx_spec t p)
        exact congrArg Prod.fst (Option.some_inj.mp h)
      rw [htt] at h2
      exact hl (Finset.mem_image.mpr ⟨q1, Finset.mem_univ q1, (tripletOf_inv l t q1 h2).symm⟩)
  rw [Matrix.mul_apply, sum_I32_support _ hvan,
    Finset.sum_image (fun x _ y _ hxy => tripletIdx_inj t x y hxy)]
  apply Finset.sum_congr rfl
  intro q' _
  rw [genM_apply_eq a (tripletIdx t p) (tripletIdx t q') t p q'
    (tripletIdx_spec t p) (tripletIdx_spec t q')]

/-- **Block commutation.** On each `(t, t')` colour block, a
    pair-space element's folded block commutes with every
    Gell-Mann matrix, in entry-sum form. -/
theorem pairSpace_genM_block_comm {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace)
    (a : Fin 8) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    (p q : Fin 3) :
    (∑ p' : Fin 3, M (tripletIdx t p) (tripletIdx t' p') * gellMann a p' q)
      = ∑ q' : Fin 3, gellMann a p q'
          * M (tripletIdx t q') (tripletIdx t' q) := by
  have h0 := pairSpace_comm_genM_entry hM a ht ht' p q
  rw [Matrix.sub_apply, sub_eq_zero] at h0
  rwa [mul_genM_apply_triplet, genM_mul_apply_triplet] at h0

/-- `gellMann 2` is the diagonal `![1, -1, 0]`. -/
theorem gellMann_two_eq_diagonal :
    gellMann 2 = Matrix.diagonal ![1, -1, 0] := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [gellMann, Matrix.diagonal_apply]

/-- Entry of a product with a diagonal `Fin 3` matrix on the right. -/
theorem mul_diagonal_apply3 {B : Matrix (Fin 3) (Fin 3) ℂ} (q : Fin 3 → ℂ)
    (p r : Fin 3) :
    (B * Matrix.diagonal q) p r = B p r * q r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro k _ hkr
    rw [Matrix.diagonal_apply, if_neg hkr, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ r) hcon

/-- Entry of a product with a diagonal `Fin 3` matrix on the left. -/
theorem diagonal_mul_apply3 (q : Fin 3 → ℂ) {B : Matrix (Fin 3) (Fin 3) ℂ}
    (p r : Fin 3) :
    (Matrix.diagonal q * B) p r = q p * B p r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro k _ hkp
    rw [Matrix.diagonal_apply, if_neg (Ne.symm hkp), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ p) hcon

/-- The three `gellMann 2` eigenvalues are pairwise distinct. -/
theorem gellMann_two_diag_ne {p q : Fin 3} (hpq : p ≠ q) :
    (![1, -1, 0] : Fin 3 → ℂ) p ≠ ![1, -1, 0] q := by
  fin_cases p <;> fin_cases q <;>
    simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two] <;> norm_num

/-- **Colour-off-diagonal kill.** A `Fin 3` block commuting with
    `gellMann 2` has vanishing off-diagonal entries. -/
theorem block_eq_zero_of_comm_gellMann_two {B : Matrix (Fin 3) (Fin 3) ℂ}
    (h : B * gellMann 2 = gellMann 2 * B) {p q : Fin 3} (hpq : p ≠ q) :
    B p q = 0 := by
  have he := congrFun (congrFun h p) q
  rw [gellMann_two_eq_diagonal, mul_diagonal_apply3, diagonal_mul_apply3]
    at he
  have hne : (![1, -1, 0] : Fin 3 → ℂ) q - ![1, -1, 0] p ≠ 0 :=
    sub_ne_zero.mpr (fun hcon => gellMann_two_diag_ne hpq hcon.symm)
  have h2 : B p q * ((![1, -1, 0] : Fin 3 → ℂ) q - ![1, -1, 0] p) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp h2).resolve_right hne

end ThetLogos


namespace ThetLogos

/-! ## 6. Folded corollaries on the antiparticle region -/

/-- Grading sign of an antiparticle triplet index. -/
theorem gSign_tripletIdx_ge {t : Fin 4} (ht : 2 ≤ t.val) (p : Fin 3) :
    gSign (tripletIdx t p) = 1 := by
  have hp := p.isLt
  rw [gSign_apply, tripletIdx_val, if_neg (by omega : ¬ t.val < 2),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Grading sign of a particle triplet index. -/
theorem gSign_tripletIdx_lt {t : Fin 4} (ht : t.val < 2) (p : Fin 3) :
    gSign (tripletIdx t p) = -1 := by
  have hp := p.isLt
  rw [gSign_apply, tripletIdx_val, if_pos ht,
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- The folded block at triplet indices is the matrix entry. -/
theorem crossCoordOf_tripletIdx {M : Matrix I32 I32 ℂ} {t t' : Fin 4}
    (ht : 2 ≤ t.val) (ht' : t'.val < 2) (p q : Fin 3) :
    crossCoordOf M (acoord (tripletIdx t p)) (acoord (tripletIdx t' q))
      = M (tripletIdx t p) (tripletIdx t' q) := by
  unfold crossCoordOf
  rw [plusEmb_acoord_of_gSign_eq_one (gSign_tripletIdx_ge ht p),
    minusEmb_flip8_acoord_of_gSign_eq_neg_one (gSign_tripletIdx_lt ht' q)]

/-- The colour block of a pair-space element commutes with every
    Gell-Mann matrix, as a matrix equation. -/
theorem pairSpace_genM_block_comm_matrix {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    (a : Fin 8) :
    (Matrix.of fun x y => M (tripletIdx t x) (tripletIdx t' y)) * gellMann a
      = gellMann a
        * (Matrix.of fun x y => M (tripletIdx t x) (tripletIdx t' y)) := by
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  exact pairSpace_genM_block_comm hM a ht ht' p q

/-- **R4 colour-off-diagonal kill**, folded form. -/
theorem pairSpace_crossCoord_R4_eq_zero {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    {p q : Fin 3} (hpq : p ≠ q) :
    crossCoordOf M (acoord (tripletIdx t p)) (acoord (tripletIdx t' q)) = 0 := by
  rw [crossCoordOf_tripletIdx ht ht']
  have h := block_eq_zero_of_comm_gellMann_two
    (pairSpace_genM_block_comm_matrix hM ht ht' 2) hpq
  simpa [Matrix.of_apply] using h

/-- **R4 colour-diagonal link, first step** (`gellMann 0`): the
    colour-0 and colour-1 diagonal values of a folded block agree. -/
theorem pairSpace_crossCoord_R4_link01 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2) :
    crossCoordOf M (acoord (tripletIdx t 0)) (acoord (tripletIdx t' 0))
      = crossCoordOf M (acoord (tripletIdx t 1)) (acoord (tripletIdx t' 1)) := by
  rw [crossCoordOf_tripletIdx ht ht', crossCoordOf_tripletIdx ht ht']
  have h := pairSpace_genM_block_comm hM 0 ht ht' 0 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  simpa [gellMann] using h

/-- **R4 colour-diagonal link, second step** (`gellMann 5`): the
    colour-1 and colour-2 diagonal values of a folded block agree. -/
theorem pairSpace_crossCoord_R4_link12 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2) :
    crossCoordOf M (acoord (tripletIdx t 1)) (acoord (tripletIdx t' 1))
      = crossCoordOf M (acoord (tripletIdx t 2)) (acoord (tripletIdx t' 2)) := by
  rw [crossCoordOf_tripletIdx ht ht', crossCoordOf_tripletIdx ht ht']
  have h := pairSpace_genM_block_comm hM 5 ht ht' 1 2
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  simpa [gellMann] using h

end ThetLogos


namespace ThetLogos

/-! ## 7. The particle region R2, by partner transport

The `(2..7, 10..15)` folded region of `M` is the `(10..15, 2..7)`
region of the partner `M-dagger`, whose folded block is the
transpose; the R4 results transport verbatim. -/

/-- **R2 colour-off-diagonal kill**, folded form. -/
theorem pairSpace_crossCoord_R2_eq_zero {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    {p q : Fin 3} (hpq : p ≠ q) :
    crossCoordOf M (acoord (tripletIdx t' q)) (acoord (tripletIdx t p)) = 0 := by
  have h := pairSpace_crossCoord_R4_eq_zero
    (pairSpace_conjTranspose_mem hM) ht ht' hpq
  rwa [crossCoordOf_conjTranspose hM.1] at h

/-- **R2 colour-diagonal link, first step.** -/
theorem pairSpace_crossCoord_R2_link01 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2) :
    crossCoordOf M (acoord (tripletIdx t' 0)) (acoord (tripletIdx t 0))
      = crossCoordOf M (acoord (tripletIdx t' 1)) (acoord (tripletIdx t 1)) := by
  have h := pairSpace_crossCoord_R4_link01
    (pairSpace_conjTranspose_mem hM) ht ht'
  rwa [crossCoordOf_conjTranspose hM.1, crossCoordOf_conjTranspose hM.1] at h

/-- **R2 colour-diagonal link, second step.** -/
theorem pairSpace_crossCoord_R2_link12 {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2) :
    crossCoordOf M (acoord (tripletIdx t' 1)) (acoord (tripletIdx t 1))
      = crossCoordOf M (acoord (tripletIdx t' 2)) (acoord (tripletIdx t 2)) := by
  have h := pairSpace_crossCoord_R4_link12
    (pairSpace_conjTranspose_mem hM) ht ht'
  rwa [crossCoordOf_conjTranspose hM.1, crossCoordOf_conjTranspose hM.1] at h

end ThetLogos


namespace ThetLogos

/-! ## 8. The 44 pivot representatives and the finite case split

The 44 ordered pivot slots of the probe: entries `0`-`7` are the
channel-diagonal representatives of the four colour-diagonal groups
and their partners, `8`-`15` the channel-flipped partners, `16`-`39`
the generation rows/columns against the colour rows/columns, and
`40`-`43` the four special slots `(8,8), (9,9), (8,9), (9,8)`. -/

/-- The 44 pivot representatives, as folded coordinates. -/
def repCoord : Fin 44 → Fin 16 × Fin 16 := fun r =>
  match r.val with
  | 0 => (0, 8) | 1 => (8, 0) | 2 => (1, 9) | 3 => (9, 1)
  | 4 => (2, 10) | 5 => (10, 2) | 6 => (3, 11) | 7 => (11, 3)
  | 8 => (0, 9) | 9 => (9, 0) | 10 => (1, 8) | 11 => (8, 1)
  | 12 => (2, 11) | 13 => (11, 2) | 14 => (3, 10) | 15 => (10, 3)
  | 16 => (8, 10) | 17 => (10, 8) | 18 => (9, 10) | 19 => (10, 9)
  | 20 => (8, 11) | 21 => (11, 8) | 22 => (9, 11) | 23 => (11, 9)
  | 24 => (8, 12) | 25 => (12, 8) | 26 => (9, 12) | 27 => (12, 9)
  | 28 => (8, 13) | 29 => (13, 8) | 30 => (9, 13) | 31 => (13, 9)
  | 32 => (8, 14) | 33 => (14, 8) | 34 => (9, 14) | 35 => (14, 9)
  | 36 => (8, 15) | 37 => (15, 8) | 38 => (9, 15) | 39 => (15, 9)
  | 40 => (8, 8) | 41 => (9, 9) | 42 => (8, 9) | 43 => (9, 8)
  | _ => (0, 0)

set_option maxRecDepth 16384

/-- The finite case split: every folded coordinate is a pivot
    representative, one of the sixteen colour-linked coordinates, or
    in one of the eight forced regions (K1-K6, R4 colour mismatch,
    R2 colour mismatch).  Pure finite arithmetic. -/
theorem pairCoord_cases : ∀ p : Fin 16 × Fin 16,
    (∃ r : Fin 44, repCoord r = p)
    ∨ p = (4, 12) ∨ p = (6, 14) ∨ p = (5, 13) ∨ p = (7, 15)
    ∨ p = (4, 13) ∨ p = (6, 15) ∨ p = (5, 12) ∨ p = (7, 14)
    ∨ p = (12, 4) ∨ p = (14, 6) ∨ p = (13, 5) ∨ p = (15, 7)
    ∨ p = (12, 5) ∨ p = (14, 7) ∨ p = (13, 4) ∨ p = (15, 6)
    ∨ (p.1.val < 8 ∧ p.2.val < 8)
    ∨ ((p.1.val = 0 ∨ p.1.val = 1) ∧ 10 ≤ p.2.val)
    ∨ (2 ≤ p.1.val ∧ p.1.val < 8 ∧ (p.2.val = 8 ∨ p.2.val = 9))
    ∨ ((p.1.val = 8 ∨ p.1.val = 9) ∧ 2 ≤ p.2.val ∧ p.2.val < 8)
    ∨ (10 ≤ p.1.val ∧ (p.2.val = 0 ∨ p.2.val = 1))
    ∨ (10 ≤ p.1.val ∧ 10 ≤ p.2.val)
    ∨ (10 ≤ p.1.val ∧ 2 ≤ p.2.val ∧ p.2.val < 8
        ∧ (p.1.val - 10) / 2 ≠ (p.2.val - 2) / 2)
    ∨ (2 ≤ p.1.val ∧ p.1.val < 8 ∧ 10 ≤ p.2.val
        ∧ (p.1.val - 2) / 2 ≠ (p.2.val - 10) / 2) := by
  decide

/-- Folded coordinate of a triplet index, as a value formula. -/
theorem acoord_tripletIdx_val (t : Fin 4) (p : Fin 3) :
    (acoord (tripletIdx t p)).val
      = (if t.val < 2 then 2 else 10) + 2 * p.val + t.val % 2 := by
  have hp := p.isLt
  rw [acoord_val, tripletIdx_val]
  by_cases ht : t.val < 2
  · rw [if_pos ht, if_pos ht]; omega
  · rw [if_neg ht, if_neg ht]; omega

end ThetLogos


namespace ThetLogos

/-! ## 9. The eight colour-link groups at literal folded coordinates -/

/-- R4 group `{(10,2), (12,4), (14,6)}`: all values equal the
    representative at `(10,2)`. -/
theorem pairSpace_crossCoord_R4_groupA {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 12 4 = crossCoordOf M 10 2
      ∧ crossCoordOf M 14 6 = crossCoordOf M 10 2 := by
  have h01 := pairSpace_crossCoord_R4_link01 hM (t := 2) (t' := 0)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R4_link12 hM (t := 2) (t' := 0)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 2 0) = (10 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 2 1) = (12 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 2 2) = (14 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 0 0) = (2 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 0 1) = (4 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 0 2) = (6 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R4 group `{(11,3), (13,5), (15,7)}`. -/
theorem pairSpace_crossCoord_R4_groupB {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 13 5 = crossCoordOf M 11 3
      ∧ crossCoordOf M 15 7 = crossCoordOf M 11 3 := by
  have h01 := pairSpace_crossCoord_R4_link01 hM (t := 3) (t' := 1)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R4_link12 hM (t := 3) (t' := 1)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 3 0) = (11 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 3 1) = (13 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 3 2) = (15 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 1 0) = (3 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 1 1) = (5 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 1 2) = (7 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R4 group `{(10,3), (12,5), (14,7)}`. -/
theorem pairSpace_crossCoord_R4_groupC {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 12 5 = crossCoordOf M 10 3
      ∧ crossCoordOf M 14 7 = crossCoordOf M 10 3 := by
  have h01 := pairSpace_crossCoord_R4_link01 hM (t := 2) (t' := 1)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R4_link12 hM (t := 2) (t' := 1)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 2 0) = (10 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 2 1) = (12 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 2 2) = (14 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 1 0) = (3 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 1 1) = (5 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 1 2) = (7 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R4 group `{(11,2), (13,4), (15,6)}`. -/
theorem pairSpace_crossCoord_R4_groupD {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 13 4 = crossCoordOf M 11 2
      ∧ crossCoordOf M 15 6 = crossCoordOf M 11 2 := by
  have h01 := pairSpace_crossCoord_R4_link01 hM (t := 3) (t' := 0)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R4_link12 hM (t := 3) (t' := 0)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 3 0) = (11 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 3 1) = (13 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 3 2) = (15 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 0 0) = (2 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 0 1) = (4 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 0 2) = (6 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R2 group `{(2,10), (4,12), (6,14)}`. -/
theorem pairSpace_crossCoord_R2_groupA {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 4 12 = crossCoordOf M 2 10
      ∧ crossCoordOf M 6 14 = crossCoordOf M 2 10 := by
  have h01 := pairSpace_crossCoord_R2_link01 hM (t := 2) (t' := 0)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R2_link12 hM (t := 2) (t' := 0)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 2 0) = (10 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 2 1) = (12 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 2 2) = (14 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 0 0) = (2 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 0 1) = (4 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 0 2) = (6 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R2 group `{(3,11), (5,13), (7,15)}`. -/
theorem pairSpace_crossCoord_R2_groupB {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 5 13 = crossCoordOf M 3 11
      ∧ crossCoordOf M 7 15 = crossCoordOf M 3 11 := by
  have h01 := pairSpace_crossCoord_R2_link01 hM (t := 3) (t' := 1)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R2_link12 hM (t := 3) (t' := 1)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 3 0) = (11 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 3 1) = (13 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 3 2) = (15 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 1 0) = (3 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 1 1) = (5 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 1 2) = (7 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R2 group `{(3,10), (5,12), (7,14)}`. -/
theorem pairSpace_crossCoord_R2_groupC {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 5 12 = crossCoordOf M 3 10
      ∧ crossCoordOf M 7 14 = crossCoordOf M 3 10 := by
  have h01 := pairSpace_crossCoord_R2_link01 hM (t := 2) (t' := 1)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R2_link12 hM (t := 2) (t' := 1)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 2 0) = (10 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 2 1) = (12 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 2 2) = (14 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 1 0) = (3 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 1 1) = (5 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 1 2) = (7 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- R2 group `{(2,11), (4,13), (6,15)}`. -/
theorem pairSpace_crossCoord_R2_groupD {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) :
    crossCoordOf M 4 13 = crossCoordOf M 2 11
      ∧ crossCoordOf M 6 15 = crossCoordOf M 2 11 := by
  have h01 := pairSpace_crossCoord_R2_link01 hM (t := 3) (t' := 0)
    (by norm_num) (by norm_num)
  have h12 := pairSpace_crossCoord_R2_link12 hM (t := 3) (t' := 0)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 3 0) = (11 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 3 1) = (13 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 3 2) = (15 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 0 0) = (2 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 0 1) = (4 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 0 2) = (6 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

end ThetLogos


namespace ThetLogos

/-! ## 10. Determination: the 44 pivots determine a pair-space element -/

/-- A pair-space element whose 44 pivot coordinates vanish is zero:
    every other folded coordinate is forced to zero (K1-K6 and the
    colour-mismatch kills) or linked to a pivot (the eight colour
    groups). -/
theorem pairSpace_eq_zero_of_repCoord_eq_zero (M : PairSpace)
    (hrep : ∀ r : Fin 44, crossCoordOf M.1 (repCoord r).1 (repCoord r).2 = 0) :
    M = 0 := by
  have hall : ∀ p : Fin 16 × Fin 16, crossCoordOf M.1 p.1 p.2 = 0 := by
    intro p
    rcases pairCoord_cases p with ⟨r, hr⟩ | h | h | h | h | h | h | h | h
      | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [← hr]; exact hrep r
    · subst h; show crossCoordOf M.1 4 12 = 0
      rw [(pairSpace_crossCoord_R2_groupA M.2).1]
      have e : repCoord 4 = ((2 : Fin 16), (10 : Fin 16)) := by decide
      have h4 := hrep 4; rw [e] at h4; exact h4
    · subst h; show crossCoordOf M.1 6 14 = 0
      rw [(pairSpace_crossCoord_R2_groupA M.2).2]
      have e : repCoord 4 = ((2 : Fin 16), (10 : Fin 16)) := by decide
      have h4 := hrep 4; rw [e] at h4; exact h4
    · subst h; show crossCoordOf M.1 5 13 = 0
      rw [(pairSpace_crossCoord_R2_groupB M.2).1]
      have e : repCoord 6 = ((3 : Fin 16), (11 : Fin 16)) := by decide
      have h6 := hrep 6; rw [e] at h6; exact h6
    · subst h; show crossCoordOf M.1 7 15 = 0
      rw [(pairSpace_crossCoord_R2_groupB M.2).2]
      have e : repCoord 6 = ((3 : Fin 16), (11 : Fin 16)) := by decide
      have h6 := hrep 6; rw [e] at h6; exact h6
    · subst h; show crossCoordOf M.1 4 13 = 0
      rw [(pairSpace_crossCoord_R2_groupD M.2).1]
      have e : repCoord 12 = ((2 : Fin 16), (11 : Fin 16)) := by decide
      have h12 := hrep 12; rw [e] at h12; exact h12
    · subst h; show crossCoordOf M.1 6 15 = 0
      rw [(pairSpace_crossCoord_R2_groupD M.2).2]
      have e : repCoord 12 = ((2 : Fin 16), (11 : Fin 16)) := by decide
      have h12 := hrep 12; rw [e] at h12; exact h12
    · subst h; show crossCoordOf M.1 5 12 = 0
      rw [(pairSpace_crossCoord_R2_groupC M.2).1]
      have e : repCoord 14 = ((3 : Fin 16), (10 : Fin 16)) := by decide
      have h14 := hrep 14; rw [e] at h14; exact h14
    · subst h; show crossCoordOf M.1 7 14 = 0
      rw [(pairSpace_crossCoord_R2_groupC M.2).2]
      have e : repCoord 14 = ((3 : Fin 16), (10 : Fin 16)) := by decide
      have h14 := hrep 14; rw [e] at h14; exact h14
    · subst h; show crossCoordOf M.1 12 4 = 0
      rw [(pairSpace_crossCoord_R4_groupA M.2).1]
      have e : repCoord 5 = ((10 : Fin 16), (2 : Fin 16)) := by decide
      have h5 := hrep 5; rw [e] at h5; exact h5
    · subst h; show crossCoordOf M.1 14 6 = 0
      rw [(pairSpace_crossCoord_R4_groupA M.2).2]
      have e : repCoord 5 = ((10 : Fin 16), (2 : Fin 16)) := by decide
      have h5 := hrep 5; rw [e] at h5; exact h5
    · subst h; show crossCoordOf M.1 13 5 = 0
      rw [(pairSpace_crossCoord_R4_groupB M.2).1]
      have e : repCoord 7 = ((11 : Fin 16), (3 : Fin 16)) := by decide
      have h7 := hrep 7; rw [e] at h7; exact h7
    · subst h; show crossCoordOf M.1 15 7 = 0
      rw [(pairSpace_crossCoord_R4_groupB M.2).2]
      have e : repCoord 7 = ((11 : Fin 16), (3 : Fin 16)) := by decide
      have h7 := hrep 7; rw [e] at h7; exact h7
    · subst h; show crossCoordOf M.1 12 5 = 0
      rw [(pairSpace_crossCoord_R4_groupC M.2).1]
      have e : repCoord 15 = ((10 : Fin 16), (3 : Fin 16)) := by decide
      have h15 := hrep 15; rw [e] at h15; exact h15
    · subst h; show crossCoordOf M.1 14 7 = 0
      rw [(pairSpace_crossCoord_R4_groupC M.2).2]
      have e : repCoord 15 = ((10 : Fin 16), (3 : Fin 16)) := by decide
      have h15 := hrep 15; rw [e] at h15; exact h15
    · subst h; show crossCoordOf M.1 13 4 = 0
      rw [(pairSpace_crossCoord_R4_groupD M.2).1]
      have e : repCoord 13 = ((11 : Fin 16), (2 : Fin 16)) := by decide
      have h13 := hrep 13; rw [e] at h13; exact h13
    · subst h; show crossCoordOf M.1 15 6 = 0
      rw [(pairSpace_crossCoord_R4_groupD M.2).2]
      have e : repCoord 13 = ((11 : Fin 16), (2 : Fin 16)) := by decide
      have h13 := hrep 13; rw [e] at h13; exact h13
    · exact pairSpace_crossCoord_eq_zero_K1 M.2 h.1 h.2
    · exact pairSpace_crossCoord_eq_zero_K2 M.2 h.1 h.2
    · exact pairSpace_crossCoord_eq_zero_K3 M.2 ⟨h.1, h.2.1⟩ h.2.2
    · exact pairSpace_crossCoord_eq_zero_K4 M.2 h.1 ⟨h.2.1, h.2.2⟩
    · exact pairSpace_crossCoord_eq_zero_K5 M.2 h.1 h.2
    · exact pairSpace_crossCoord_eq_zero_K6 M.2 h.1 h.2
    · -- R4 colour mismatch
      obtain ⟨hu, hv2, hv8, hne⟩ := h
      have h16 := p.1.isLt
      have h16' := p.2.isLt
      set t : Fin 4 := ⟨2 + (p.1.val - 10) % 2, by omega⟩ with ht
      set t' : Fin 4 := ⟨(p.2.val - 2) % 2, by omega⟩ with ht'
      set pp : Fin 3 := ⟨(p.1.val - 10) / 2, by omega⟩ with hpp
      set qq : Fin 3 := ⟨(p.2.val - 2) / 2, by omega⟩ with hqq
      have htval : t.val = 2 + (p.1.val - 10) % 2 := rfl
      have ht'val : t'.val = (p.2.val - 2) % 2 := rfl
      have hppval : pp.val = (p.1.val - 10) / 2 := rfl
      have hqqval : qq.val = (p.2.val - 2) / 2 := rfl
      have eu : p.1 = acoord (tripletIdx t pp) := by
        apply Fin.ext
        rw [acoord_tripletIdx_val, htval, hppval,
          if_neg (by omega : ¬ (2 + (p.1.val - 10) % 2) < 2)]
        omega
      have ev : p.2 = acoord (tripletIdx t' qq) := by
        apply Fin.ext
        rw [acoord_tripletIdx_val, ht'val, hqqval,
          if_pos (by omega : (p.2.val - 2) % 2 < 2)]
        omega
      have hpq : pp ≠ qq := by
        intro hcon
        have e := congrArg Fin.val hcon
        rw [hppval, hqqval] at e
        exact hne e
      rw [eu, ev]
      exact pairSpace_crossCoord_R4_eq_zero M.2 (t := t) (t' := t')
        (by rw [htval]; omega) (by rw [ht'val]; omega) (p := pp) (q := qq) hpq
    · -- R2 colour mismatch
      obtain ⟨hu2, hu8, hv, hne⟩ := h
      have h16 := p.1.isLt
      have h16' := p.2.isLt
      set t : Fin 4 := ⟨2 + (p.2.val - 10) % 2, by omega⟩ with ht
      set t' : Fin 4 := ⟨(p.1.val - 2) % 2, by omega⟩ with ht'
      set pp : Fin 3 := ⟨(p.2.val - 10) / 2, by omega⟩ with hpp
      set qq : Fin 3 := ⟨(p.1.val - 2) / 2, by omega⟩ with hqq
      have htval : t.val = 2 + (p.2.val - 10) % 2 := rfl
      have ht'val : t'.val = (p.1.val - 2) % 2 := rfl
      have hppval : pp.val = (p.2.val - 10) / 2 := rfl
      have hqqval : qq.val = (p.1.val - 2) / 2 := rfl
      have eu : p.1 = acoord (tripletIdx t' qq) := by
        apply Fin.ext
        rw [acoord_tripletIdx_val, ht'val, hqqval,
          if_pos (by omega : (p.1.val - 2) % 2 < 2)]
        omega
      have ev : p.2 = acoord (tripletIdx t pp) := by
        apply Fin.ext
        rw [acoord_tripletIdx_val, htval, hppval,
          if_neg (by omega : ¬ (2 + (p.2.val - 10) % 2) < 2)]
        omega
      have hpq : pp ≠ qq := by
        intro hcon
        have e := congrArg Fin.val hcon
        rw [hppval, hqqval] at e
        exact hne e.symm
      rw [eu, ev]
      exact pairSpace_crossCoord_R2_eq_zero M.2 (t := t) (t' := t')
        (by rw [htval]; omega) (by rw [ht'val]; omega) (p := pp) (q := qq) hpq
  apply Subtype.ext
  change M.1 = 0
  calc M.1 = admBlockMatOf (fun p => crossCoordOf M.1 p.1 p.2) :=
        pairSpace_eq_admBlockMatOf_crossCoordOf M.2
    _ = admBlockMatOf 0 := by
        congr 1
        funext p
        exact hall p
    _ = 0 := by
        ext i j
        rw [admBlockMatOf_apply]
        split_ifs <;> simp

end ThetLogos


namespace ThetLogos

/-! ## 11. The pivot injection and the finrank equality -/

/-- The pivot-evaluation map: a pair-space element maps to its 44
    folded pivot coordinates. -/
def pairSpacePivotMap : PairSpace →ₗ[ℝ] (Fin 44 → ℂ) where
  toFun := fun M r => crossCoordOf M.1 (repCoord r).1 (repCoord r).2
  map_add' := by
    intro M N
    funext r
    simp [crossCoordOf, Matrix.add_apply]
  map_smul' := by
    intro c M
    funext r
    simp [crossCoordOf, Matrix.smul_apply, Pi.smul_apply]

/-- The pivot map is injective, by determination. -/
theorem pairSpacePivotMap_injective :
    Function.Injective pairSpacePivotMap := by
  intro x y hxy
  have h0 : pairSpacePivotMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hdet := pairSpace_eq_zero_of_repCoord_eq_zero (x - y) (fun r => by
    have hr := congrFun h0 r
    simpa [pairSpacePivotMap] using hr)
  exact sub_eq_zero.mp hdet

/-- **The upper bound**: `finrank ℝ PairSpace ≤ 88`. -/
theorem finrank_pairSpace_le : Module.finrank ℝ PairSpace ≤ 88 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := pairSpacePivotMap) pairSpacePivotMap_injective
  refine h.trans_eq ?_
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- **C96-3b2 headline**: the pair space has real dimension exactly
    `88` - the 44 complex pivot slots, with no 89th direction. -/
theorem finrank_pairSpace_eq : Module.finrank ℝ PairSpace = 88 :=
  le_antisymm finrank_pairSpace_le finrank_ge_88

end ThetLogos

