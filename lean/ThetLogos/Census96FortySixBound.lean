import ThetLogos.Census96FortySixDirections
import ThetLogos.Census96PairBound

/-!
# ThetLogos.Census96FortySixBound - C96-2b: the `<= 46` bound and the 46 theorem

Bound half of the one-generation 46 theorem (scoping memo
`scoping-census96-2026-10-30.md` section 1.A / section 3 row C96-2;
pack `pack-c96-2b.md`). C96-2a landed the 46 directions
(`dir46_independent`); C96-3b2 (`Census96PairBound.lean`) is the
method template - this module is its diagonal-side cousin. Target
headline: `finrank_sol32_eq : Module.finrank R Sol32 = 46`.

## The 23 pivot slots, reconciled (2a matrix entries vs folded slots)

C96-2a's independence proof pivots on 23 complex matrix entries
`(r, c)` of `I32 x I32` (the `hva46_*` / `hvb46_*` lemmas). Folded
through the `adm32MatOf` parameterization (entry `(i, j)` in the
`(+, -)` grading sector is `symMatOf f (acoord i) (acoord j)`, and
the two `(-, +)` pivots are the conjugates of the swapped folded
entries), the 23 pivots are exactly the 23 folded coordinates
`slotCoord 0 .. slotCoord 22` below:

- the eleven dirs22-consumed pivots: `(0,8) -> (0,8)`,
  `(1,9) -> (1,9)`, `(2,10) -> (2,10)`, `(3,11) -> (3,11)`,
  `(24,8) -> (8,8)`, `(0,9) -> (0,9)`, `(1,8) -> (1,8)`,
  `(2,11) -> (2,11)`, `(3,10) -> (3,10)`, `(8,25) -> (8,9)`
  (a `(-, +)` entry: `star` of the folded `(9,8) = (8,9)` entry),
  `(9,25) -> (9,9)` (likewise, `star` of the folded `(9,9)` entry);
- the twelve new Majorana pivots: `(24, v) -> (8, v)` and
  `(25, v) -> (9, v)` for `v = 10..15` - the folded Majorana
  coordinates `(8, v)`, `(9, v)`, `v = 10..15`, of C96-2a section 3.

So the pivot slots, as folded coordinates `(u, v)` with `u <= v`,
are: `(0,8), (1,9), (2,10), (3,11), (8,8), (0,9), (1,8), (2,11),
(3,10), (8,9), (9,9)`, and `(8,v), (9,v)` for `v = 10..15`.

## What is proved here (T1 when the build is green)

1. **Reconstruction.** Every admissible `D` is `adm32MatOf` of its
   own folded coordinate function on `Upper16` (the landed
   parameterization of `Census96Decoupling.lean`), and the folded
   block of an admissible matrix is symmetric
   (`crossCoordOf_symm_of_adm32`, from J-compatibility). Hence
   `OrderOneHolds D` is a condition on the single folded coordinate
   function `crossCoordOf D`.
2. **Support forcing.** For `D` in `Sol32`, every folded coordinate
   outside the 23 pivot slots vanishes or is colour-linked to a
   slot: the diagonal support projectors of C96-3b2 (transported
   through C96-1b's bridge `orderOne_adjoin`) kill the regions
   K1/K2/K3/K6, and the Gell-Mann generator tests kill the colour
   off-diagonal entries of the four triplet blocks and link their
   colour diagonals to the four exotic pivot slots.
3. **Determination + injection + equality.** A `Sol32` element
   whose 23 pivot coordinates all vanish is zero
   (`sol32_eq_zero_of_slotCoord_eq_zero`); the pivot-evaluation map
   `sol32PivotMap : Sol32 -> (Fin 23 -> C)` is therefore injective,
   giving `finrank_sol32_le : finrank R Sol32 <= 46 = 2 * 23`; with
   C96-2a's `dir46_independent` (via `finrank_ge_46`),
   `finrank_sol32_eq : finrank R Sol32 = 46`.

## Kills and fences (on the face)

- K-C96-1 (armed): a PROVED 47th independent direction, or any
  proved finrank of `Sol32` different from 46, kills the T4 note at
  full rank. This module proves the registered number 46.
- K-C96-2 (vacuity): the bound is a support theorem about a general
  element, not a slot count.
- Generations IMPOSED; CKM/PMNS input-only; Q3 OPEN; NO CLAIM.
  The old 46 -> 10 gloss is UNSOUND AS STATED and is not cited.
  `Census96` / `Census96Diag` are NOT discharged here (assembly is
  C96-4).
-/

open Matrix

namespace ThetLogos

/-! ## 1. Reconstruction of an admissible matrix from its folded block -/

/-- **Folded symmetry.** The folded cross-block of an admissible
    matrix is symmetric (J-compatibility, via the landed
    `symMatOf_crossCoordOf`). -/
theorem crossCoordOf_symm_of_adm32 {D : Matrix I32 I32 ℂ}
    (hD : IsAdm32 D) (u v : Fin 16) :
    crossCoordOf D u v = crossCoordOf D v u := by
  have h1 := symMatOf_crossCoordOf D hD.2.2 u v
  have h2 := symMatOf_crossCoordOf D hD.2.2 v u
  rw [← h1, ← h2, symMatOf_symm]

/-- **Reconstruction.** An admissible matrix is the folded assembly
    of its own folded coordinate function. The four grading cases:
    same-sign entries vanish (grading-oddness), the `(+, -)` entry
    is the folded value at the recovered indices, and the `(-, +)`
    entry is its conjugate by self-adjointness. (The same proof
    sits inside the landed `adm32Equiv`; stated here as a theorem
    about `IsAdm32`.) -/
theorem adm32_eq_adm32MatOf_crossCoordOf {D : Matrix I32 I32 ℂ}
    (hD : IsAdm32 D) :
    D = adm32MatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2) := by
  obtain ⟨hsa, hgr, hj⟩ := hD
  ext i j
  rcases gSign_eq_one_or_neg_one i with hi | hi <;>
    rcases gSign_eq_one_or_neg_one j with hj2 | hj2
  · have h0 : D i j = 0 :=
      gammaOdd_entry_eq_zero_of_gSign_eq D hgr (by rw [hi, hj2])
    rw [h0]
    simp only [adm32MatOf_apply, hi, hj2, eq_self_iff_true, ite_true]
  · have e1 : adm32MatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2) i j
        = symMatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2)
            (acoord i) (acoord j) := by
      simp only [adm32MatOf_apply, hi, hj2, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    rw [e1, symMatOf_crossCoordOf D hj]
    unfold crossCoordOf
    rw [plusEmb_acoord_of_gSign_eq_one hi,
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hj2]
  · have e1 : adm32MatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2) i j
        = star (symMatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2)
            (acoord j) (acoord i)) := by
      simp only [adm32MatOf_apply, hi, hj2, eq_self_iff_true,
        neg_one_ne_one_complex, ite_true, ite_false]
    rw [e1, symMatOf_crossCoordOf D hj]
    unfold crossCoordOf
    rw [plusEmb_acoord_of_gSign_eq_one hj2,
      minusEmb_flip8_acoord_of_gSign_eq_neg_one hi]
    exact selfAdjoint_entry D hsa i j
  · have h0 : D i j = 0 :=
      gammaOdd_entry_eq_zero_of_gSign_eq D hgr (by rw [hi, hj2])
    rw [h0]
    simp only [adm32MatOf_apply, hi, hj2, neg_one_ne_one_complex, ite_false]

/-- Reconstruction for a solution-space element. -/
theorem sol32_eq_adm32MatOf_crossCoordOf {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) :
    D = adm32MatOf (fun p : Upper16 => crossCoordOf D p.1.1 p.1.2) :=
  adm32_eq_adm32MatOf_crossCoordOf hD.1

end ThetLogos

namespace ThetLogos

/-! ## 2. The 23 pivot slots and the finite case split -/

/-- The 23 pivot slots, as folded coordinates `(u, v)` with
    `u <= v`, in C96-2a's pivot order (see the header for the
    reconciliation against the 23 matrix pivot entries). -/
def slotCoord : Fin 23 → Fin 16 × Fin 16 := fun r =>
  match r.val with
  | 0 => (0, 8) | 1 => (1, 9) | 2 => (2, 10) | 3 => (3, 11)
  | 4 => (8, 8) | 5 => (0, 9) | 6 => (1, 8) | 7 => (2, 11)
  | 8 => (3, 10) | 9 => (8, 9) | 10 => (9, 9)
  | 11 => (8, 10) | 12 => (8, 11) | 13 => (8, 12) | 14 => (8, 13)
  | 15 => (8, 14) | 16 => (8, 15)
  | 17 => (9, 10) | 18 => (9, 11) | 19 => (9, 12) | 20 => (9, 13)
  | 21 => (9, 14) | 22 => (9, 15)
  | _ => (0, 0)

set_option maxRecDepth 16384

/-- The finite case split: every upper-triangular folded coordinate
    is a pivot slot, one of the eight colour-linked coordinates, or
    in one of the five forced regions (K1, K2, K3, K6, colour
    mismatch). Pure finite arithmetic. -/
theorem solCoord_cases : ∀ p : Fin 16 × Fin 16, p.1 ≤ p.2 →
    (∃ r : Fin 23, slotCoord r = p)
    ∨ p = (4, 12) ∨ p = (6, 14) ∨ p = (5, 13) ∨ p = (7, 15)
    ∨ p = (5, 12) ∨ p = (7, 14) ∨ p = (4, 13) ∨ p = (6, 15)
    ∨ p.2.val < 8
    ∨ ((p.1.val = 0 ∨ p.1.val = 1) ∧ 10 ≤ p.2.val)
    ∨ (2 ≤ p.1.val ∧ p.1.val < 8 ∧ (p.2.val = 8 ∨ p.2.val = 9))
    ∨ (10 ≤ p.1.val)
    ∨ (2 ≤ p.1.val ∧ p.1.val < 8 ∧ 10 ≤ p.2.val
        ∧ (p.1.val - 2) / 2 ≠ (p.2.val - 10) / 2) := by
  decide

end ThetLogos

namespace ThetLogos

/-! ## 3. Diagonal forcing on folded coordinates

The diagonal double-commutator machinery is C96-3b2's (section 2 of
`Census96PairBound.lean`: `dcGen_diagonal_apply`, the projectors
`projC` / `projH` / `projM` as diagonal matrices `indC` / `indH` /
`indM`, and their opposites). Only the order-one source changes:
here it is the `OrderOneHolds` half of `Sol32` membership, fed
through the same bridge `orderOne_adjoin`. -/

/-- **Diagonal forcing, diagonal side.** If a left-algebra element
    and a right-algebra element are diagonal with values `p`, `q`
    both separating `i` from `j`, then a solution-space element
    vanishes at `(i, j)`. -/
theorem sol32_entry_eq_zero_of_diag_ne {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {X Y : Matrix I32 I32 ℂ} {p q : I32 → ℂ}
    (hX : X = Matrix.diagonal p) (hY : Y = Matrix.diagonal q)
    (hXm : X ∈ smGenAlgebra) (hYm : Y ∈ smGenOpAlgebra)
    {i j : I32} (hp : p j ≠ p i) (hq : q j ≠ q i) : D i j = 0 := by
  have h := orderOne_adjoin D hD.2 X hXm Y hYm
  have he := congrFun (congrFun h i) j
  rw [hX, hY, dcGen_diagonal_apply, Matrix.zero_apply] at he
  rcases mul_eq_zero.mp he with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.mp h2) hp
  · exact absurd (sub_eq_zero.mp h1) hq

/-- K1: the whole `(u < 8, v < 8)` quadrant dies, via `projH`
    against its opposite. -/
theorem sol32_crossCoord_eq_zero_K1 {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {u v : Fin 16} (hu : u.val < 8) (hv : v.val < 8) :
    crossCoordOf D u v = 0 := by
  show D (plusEmb u) (minusEmb (flip8 v)) = 0
  apply sol32_entry_eq_zero_of_diag_ne hD projH_eq_diagonal
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
theorem sol32_crossCoord_eq_zero_K2 {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {u v : Fin 16} (hu : u.val = 0 ∨ u.val = 1)
    (hv : 10 ≤ v.val) : crossCoordOf D u v = 0 := by
  show D (plusEmb u) (minusEmb (flip8 v)) = 0
  apply sol32_entry_eq_zero_of_diag_ne hD projC_eq_diagonal
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
    opposite. (On the diagonal side this one region covers both of
    the pair side's K3 and K4, the folded block being symmetric.) -/
theorem sol32_crossCoord_eq_zero_K3 {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {u v : Fin 16} (hu : 2 ≤ u.val ∧ u.val < 8)
    (hv : v.val = 8 ∨ v.val = 9) : crossCoordOf D u v = 0 := by
  show D (plusEmb u) (minusEmb (flip8 v)) = 0
  apply sol32_entry_eq_zero_of_diag_ne hD projC_eq_diagonal
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

/-- K6: `(u >= 10, v >= 10)` dies, via `projC` against the opposite
    M-projector. -/
theorem sol32_crossCoord_eq_zero_K6 {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {u v : Fin 16} (hu : 10 ≤ u.val)
    (hv : 10 ≤ v.val) : crossCoordOf D u v = 0 := by
  show D (plusEmb u) (minusEmb (flip8 v)) = 0
  apply sol32_entry_eq_zero_of_diag_ne hD projC_eq_diagonal
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

/-! ## 4. Gell-Mann forcing on the triplet blocks

Transported from C96-3b2 section 5-6, with the order-one source
again the only change. Testing order-one against `genM a` (left)
and the opposite C-projector (right, diagonal with factor `-1` on
the region) says each folded colour block of a solution-space
element commutes with every Gell-Mann matrix; commuting with
`gellMann 2` (eigenvalues `1, -1, 0`, all distinct) kills the
colour-off-diagonal entries, and commuting with `gellMann 0` /
`gellMann 5` links the three colour-diagonal values. On the
diagonal side the single orientation `(10..15, 2..7)` suffices -
the folded block is symmetric, so the pair side's partner
transport (its section 7) is not needed. -/

/-- **The commutator entry on the triplet region.** Testing
    order-one against `genM a` and the opposite C-projector kills
    the `(triplet, triplet)` entries of `[D, genM a]`. -/
theorem sol32_comm_genM_entry {D : Matrix I32 I32 ℂ} (hD : D ∈ Sol32)
    (a : Fin 8) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    (p q : Fin 3) :
    (D * genM a - genM a * D) (tripletIdx t p) (tripletIdx t' q) = 0 := by
  have h := orderOne_adjoin D hD.2 (genM a) (genM_mem_adjoin a)
    (opLin projC) (opLin_mem_adjoinOp projC projC_mem_adjoin)
  have he := congrFun (congrFun h (tripletIdx t p)) (tripletIdx t' q)
  simp only [opLin_projC_eq_diagonal, dcGen_diagonal_right_apply,
    indC_partner_tripletIdx_ge ht p, indC_partner_tripletIdx_lt ht' q,
    Matrix.zero_apply] at he
  have he2 : (D * genM a - genM a * D) (tripletIdx t p) (tripletIdx t' q)
      * (-1 : ℂ) = 0 := by
    have h01 : (0 : ℂ) - 1 = -1 := by norm_num
    rwa [h01] at he
  rcases mul_eq_zero.mp he2 with hX | hX
  · exact hX
  · norm_num at hX

/-- **Block commutation.** On each `(t, t')` colour block, a
    solution-space element's folded block commutes with every
    Gell-Mann matrix, in entry-sum form. -/
theorem sol32_genM_block_comm {D : Matrix I32 I32 ℂ} (hD : D ∈ Sol32)
    (a : Fin 8) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    (p q : Fin 3) :
    (∑ p' : Fin 3, D (tripletIdx t p) (tripletIdx t' p') * gellMann a p' q)
      = ∑ q' : Fin 3, gellMann a p q'
          * D (tripletIdx t q') (tripletIdx t' q) := by
  have h0 := sol32_comm_genM_entry hD a ht ht' p q
  rw [Matrix.sub_apply, sub_eq_zero] at h0
  rwa [mul_genM_apply_triplet, genM_mul_apply_triplet] at h0

/-- The colour block of a solution-space element commutes with
    every Gell-Mann matrix, as a matrix equation. -/
theorem sol32_genM_block_comm_matrix {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    (a : Fin 8) :
    (Matrix.of fun x y => D (tripletIdx t x) (tripletIdx t' y)) * gellMann a
      = gellMann a
        * (Matrix.of fun x y => D (tripletIdx t x) (tripletIdx t' y)) := by
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  exact sol32_genM_block_comm hD a ht ht' p q

/-- **Colour-off-diagonal kill**, folded form. -/
theorem sol32_crossCoord_R4_eq_zero {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2)
    {p q : Fin 3} (hpq : p ≠ q) :
    crossCoordOf D (acoord (tripletIdx t p)) (acoord (tripletIdx t' q)) = 0 := by
  rw [crossCoordOf_tripletIdx ht ht']
  have h := block_eq_zero_of_comm_gellMann_two
    (sol32_genM_block_comm_matrix hD ht ht' 2) hpq
  simpa [Matrix.of_apply] using h

/-- **Colour-diagonal link, first step** (`gellMann 0`): the
    colour-0 and colour-1 diagonal values of a folded block agree. -/
theorem sol32_crossCoord_R4_link01 {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2) :
    crossCoordOf D (acoord (tripletIdx t 0)) (acoord (tripletIdx t' 0))
      = crossCoordOf D (acoord (tripletIdx t 1)) (acoord (tripletIdx t' 1)) := by
  rw [crossCoordOf_tripletIdx ht ht', crossCoordOf_tripletIdx ht ht']
  have h := sol32_genM_block_comm hD 0 ht ht' 0 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  simpa [gellMann] using h

/-- **Colour-diagonal link, second step** (`gellMann 5`): the
    colour-1 and colour-2 diagonal values of a folded block agree. -/
theorem sol32_crossCoord_R4_link12 {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) {t t' : Fin 4} (ht : 2 ≤ t.val) (ht' : t'.val < 2) :
    crossCoordOf D (acoord (tripletIdx t 1)) (acoord (tripletIdx t' 1))
      = crossCoordOf D (acoord (tripletIdx t 2)) (acoord (tripletIdx t' 2)) := by
  rw [crossCoordOf_tripletIdx ht ht', crossCoordOf_tripletIdx ht ht']
  have h := sol32_genM_block_comm hD 5 ht ht' 1 2
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  simpa [gellMann] using h

end ThetLogos

namespace ThetLogos

/-! ## 5. The four colour-link groups at literal folded coordinates

Each group is stated in the `(10..15, 2..7)` orientation of the
Gell-Mann section; the determination theorem transports through
folded symmetry (`crossCoordOf_symm_of_adm32`) to the
upper-triangular orientation of the case split. -/

/-- Group `{(10,2), (12,4), (14,6)}`: all values equal the
    representative at `(10,2)` - the pivot slot `(2,10)`. -/
theorem sol32_crossCoord_groupA {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) :
    crossCoordOf D 12 4 = crossCoordOf D 10 2
      ∧ crossCoordOf D 14 6 = crossCoordOf D 10 2 := by
  have h01 := sol32_crossCoord_R4_link01 hD (t := 2) (t' := 0)
    (by norm_num) (by norm_num)
  have h12 := sol32_crossCoord_R4_link12 hD (t := 2) (t' := 0)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 2 0) = (10 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 2 1) = (12 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 2 2) = (14 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 0 0) = (2 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 0 1) = (4 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 0 2) = (6 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- Group `{(11,3), (13,5), (15,7)}` - pivot slot `(3,11)`. -/
theorem sol32_crossCoord_groupB {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) :
    crossCoordOf D 13 5 = crossCoordOf D 11 3
      ∧ crossCoordOf D 15 7 = crossCoordOf D 11 3 := by
  have h01 := sol32_crossCoord_R4_link01 hD (t := 3) (t' := 1)
    (by norm_num) (by norm_num)
  have h12 := sol32_crossCoord_R4_link12 hD (t := 3) (t' := 1)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 3 0) = (11 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 3 1) = (13 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 3 2) = (15 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 1 0) = (3 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 1 1) = (5 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 1 2) = (7 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- Group `{(10,3), (12,5), (14,7)}` - pivot slot `(3,10)`. -/
theorem sol32_crossCoord_groupC {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) :
    crossCoordOf D 12 5 = crossCoordOf D 10 3
      ∧ crossCoordOf D 14 7 = crossCoordOf D 10 3 := by
  have h01 := sol32_crossCoord_R4_link01 hD (t := 2) (t' := 1)
    (by norm_num) (by norm_num)
  have h12 := sol32_crossCoord_R4_link12 hD (t := 2) (t' := 1)
    (by norm_num) (by norm_num)
  have c1 : acoord (tripletIdx 2 0) = (10 : Fin 16) := by decide
  have c2 : acoord (tripletIdx 2 1) = (12 : Fin 16) := by decide
  have c3 : acoord (tripletIdx 2 2) = (14 : Fin 16) := by decide
  have d1 : acoord (tripletIdx 1 0) = (3 : Fin 16) := by decide
  have d2 : acoord (tripletIdx 1 1) = (5 : Fin 16) := by decide
  have d3 : acoord (tripletIdx 1 2) = (7 : Fin 16) := by decide
  simp only [c1, c2, c3, d1, d2, d3] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

/-- Group `{(11,2), (13,4), (15,6)}` - pivot slot `(2,11)`. -/
theorem sol32_crossCoord_groupD {D : Matrix I32 I32 ℂ}
    (hD : D ∈ Sol32) :
    crossCoordOf D 13 4 = crossCoordOf D 11 2
      ∧ crossCoordOf D 15 6 = crossCoordOf D 11 2 := by
  have h01 := sol32_crossCoord_R4_link01 hD (t := 3) (t' := 0)
    (by norm_num) (by norm_num)
  have h12 := sol32_crossCoord_R4_link12 hD (t := 3) (t' := 0)
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

/-! ## 6. Determination: the 23 pivot slots determine a solution -/

/-- A solution-space element whose 23 pivot coordinates vanish is
    zero: every other folded coordinate is forced to zero (K1, K2,
    K3, K6 and the colour-mismatch kill) or linked to a pivot slot
    (the four colour groups, transported through folded symmetry). -/
theorem sol32_eq_zero_of_slotCoord_eq_zero (D : Sol32)
    (hslot : ∀ r : Fin 23,
      crossCoordOf D.1 (slotCoord r).1 (slotCoord r).2 = 0) :
    D = 0 := by
  have hall : ∀ p : Upper16, crossCoordOf D.1 p.1.1 p.1.2 = 0 := by
    intro p
    have key : ∀ q : Fin 16 × Fin 16, q.1 ≤ q.2 →
        crossCoordOf D.1 q.1 q.2 = 0 := by
      intro q hq
      rcases solCoord_cases q hq with ⟨r, hr⟩ | h | h | h | h | h | h | h | h
        | h | h | h | h | h
      · have hr0 := hslot r
        rw [hr] at hr0
        exact hr0
      · subst h; show crossCoordOf D.1 4 12 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupA D.2).1,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 2 = ((2 : Fin 16), (10 : Fin 16)) := by decide
        have h2 := hslot 2; rw [e] at h2; exact h2
      · subst h; show crossCoordOf D.1 6 14 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupA D.2).2,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 2 = ((2 : Fin 16), (10 : Fin 16)) := by decide
        have h2 := hslot 2; rw [e] at h2; exact h2
      · subst h; show crossCoordOf D.1 5 13 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupB D.2).1,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 3 = ((3 : Fin 16), (11 : Fin 16)) := by decide
        have h3 := hslot 3; rw [e] at h3; exact h3
      · subst h; show crossCoordOf D.1 7 15 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupB D.2).2,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 3 = ((3 : Fin 16), (11 : Fin 16)) := by decide
        have h3 := hslot 3; rw [e] at h3; exact h3
      · subst h; show crossCoordOf D.1 5 12 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupC D.2).1,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 8 = ((3 : Fin 16), (10 : Fin 16)) := by decide
        have h8 := hslot 8; rw [e] at h8; exact h8
      · subst h; show crossCoordOf D.1 7 14 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupC D.2).2,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 8 = ((3 : Fin 16), (10 : Fin 16)) := by decide
        have h8 := hslot 8; rw [e] at h8; exact h8
      · subst h; show crossCoordOf D.1 4 13 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupD D.2).1,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 7 = ((2 : Fin 16), (11 : Fin 16)) := by decide
        have h7 := hslot 7; rw [e] at h7; exact h7
      · subst h; show crossCoordOf D.1 6 15 = 0
        rw [crossCoordOf_symm_of_adm32 D.2.1, (sol32_crossCoord_groupD D.2).2,
          crossCoordOf_symm_of_adm32 D.2.1]
        have e : slotCoord 7 = ((2 : Fin 16), (11 : Fin 16)) := by decide
        have h7 := hslot 7; rw [e] at h7; exact h7
      · -- K1: both coordinates below 8
        have hle : q.1.val ≤ q.2.val := Fin.le_iff_val_le_val.mp hq
        exact sol32_crossCoord_eq_zero_K1 D.2 (by omega) h
      · -- K2
        exact sol32_crossCoord_eq_zero_K2 D.2 h.1 h.2
      · -- K3
        exact sol32_crossCoord_eq_zero_K3 D.2 ⟨h.1, h.2.1⟩ h.2.2
      · -- K6: the first coordinate is at least 10, hence so is the second
        have hle : q.1.val ≤ q.2.val := Fin.le_iff_val_le_val.mp hq
        exact sol32_crossCoord_eq_zero_K6 D.2 h (by omega)
      · -- Colour mismatch in the triplet blocks
        obtain ⟨hu2, hu8, hv, hne⟩ := h
        have h16 := q.1.isLt
        have h16' := q.2.isLt
        set t : Fin 4 := ⟨2 + (q.2.val - 10) % 2, by omega⟩ with ht
        set t' : Fin 4 := ⟨(q.1.val - 2) % 2, by omega⟩ with ht'
        set pp : Fin 3 := ⟨(q.2.val - 10) / 2, by omega⟩ with hpp
        set qq : Fin 3 := ⟨(q.1.val - 2) / 2, by omega⟩ with hqq
        have htval : t.val = 2 + (q.2.val - 10) % 2 := rfl
        have ht'val : t'.val = (q.1.val - 2) % 2 := rfl
        have hppval : pp.val = (q.2.val - 10) / 2 := rfl
        have hqqval : qq.val = (q.1.val - 2) / 2 := rfl
        have eu : q.2 = acoord (tripletIdx t pp) := by
          apply Fin.ext
          rw [acoord_tripletIdx_val, htval, hppval,
            if_neg (by omega : ¬ (2 + (q.2.val - 10) % 2) < 2)]
          omega
        have ev : q.1 = acoord (tripletIdx t' qq) := by
          apply Fin.ext
          rw [acoord_tripletIdx_val, ht'val, hqqval,
            if_pos (by omega : (q.1.val - 2) % 2 < 2)]
          omega
        have hpq : pp ≠ qq := by
          intro hcon
          have e := congrArg Fin.val hcon
          rw [hppval, hqqval] at e
          exact hne e.symm
        rw [crossCoordOf_symm_of_adm32 D.2.1, eu, ev]
        exact sol32_crossCoord_R4_eq_zero D.2 (t := t) (t' := t')
          (by rw [htval]; omega) (by rw [ht'val]; omega) (p := pp) (q := qq) hpq
    exact key p.1 p.2
  apply Subtype.ext
  change D.1 = 0
  calc D.1 = adm32MatOf (fun p : Upper16 => crossCoordOf D.1 p.1.1 p.1.2) :=
        sol32_eq_adm32MatOf_crossCoordOf D.2
    _ = adm32MatOf 0 := by
        congr 1
        funext p
        exact hall p
    _ = 0 := by
        ext i j
        rw [adm32MatOf_apply]
        split_ifs <;> simp [symMatOf]

end ThetLogos

namespace ThetLogos

/-! ## 7. The pivot injection and the finrank equality -/

/-- The pivot-evaluation map: a solution-space element maps to its
    23 folded pivot coordinates. -/
def sol32PivotMap : Sol32 →ₗ[ℝ] (Fin 23 → ℂ) where
  toFun := fun D r => crossCoordOf D.1 (slotCoord r).1 (slotCoord r).2
  map_add' := by
    intro D E
    funext r
    simp [crossCoordOf, Matrix.add_apply]
  map_smul' := by
    intro c D
    funext r
    simp [crossCoordOf, Matrix.smul_apply, Pi.smul_apply]

/-- The pivot map is injective, by determination. -/
theorem sol32PivotMap_injective :
    Function.Injective sol32PivotMap := by
  intro x y hxy
  have h0 : sol32PivotMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hdet := sol32_eq_zero_of_slotCoord_eq_zero (x - y) (fun r => by
    have hr := congrFun h0 r
    simpa [sol32PivotMap] using hr)
  exact sub_eq_zero.mp hdet

/-- **The upper bound**: `finrank R Sol32 <= 46 = 2 * 23`. -/
theorem finrank_sol32_le : Module.finrank ℝ Sol32 ≤ 46 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := sol32PivotMap) sol32PivotMap_injective
  refine h.trans_eq ?_
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- **The lower bound**, from C96-2a's 46 independent directions. -/
theorem finrank_ge_46 : 46 ≤ Module.finrank ℝ Sol32 := by
  have h := dir46_independent.fintype_card_le_finrank
  simpa using h

/-- **C96-2b headline**: the one-generation order-one solution
    space has real dimension exactly `46` - the 23 complex pivot
    slots of C96-2a, with no 47th direction. -/
theorem finrank_sol32_eq : Module.finrank ℝ Sol32 = 46 :=
  le_antisymm finrank_sol32_le finrank_ge_46

end ThetLogos
