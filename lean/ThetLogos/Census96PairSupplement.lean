import ThetLogos.Census96PairExotic

/-!
# ThetLogos.Census96PairSupplement - C96-3a4: the exotic supplement

Continuation of C96-3a3 (lane 2 of the Census-96 line; pack
`pack-c96-3a4.md`). The frozen interfaces of C96-3a / C96-3a2 /
C96-3a3 (`PairSpace`, `mem_pairSpace_iff`, `pairDirExotic54`,
`exAntiMat`, `exAntiMat_mem`, `exPairMat_orderOne_A`,
`exPairMat_orderOne_B`, `exPairMat_conjTranspose`, and the rest of
the `ex*` engine) are imported and untouched; every name defined
here is new.

## What this module does

It exhibits the 8 antisymmetric folded patterns left unexhibited
by C96-3a3 (the named seam of its dossier): the patterns
`exAntiMat u v z` at the folded coordinate pairs `(8, 9)`,
`(9, 13)`, `(9, 14)`, `(9, 15)`, each with `z` in `{1, Complex.I}`,
as explicit elements of `PairSpace`, assembled as the family
`pairDirExoticSupp8 : Fin 8 -> PairSpace`.

Accounting (for C96-3b's assembly; no finrank is stated or proved
here): with these 8 exhibited, the direction assembly is
SM 18 + flipped 16 + exotic-segment 46 distinct + supplement 8
= 88 distinct directions - the exotic segment of
`pairDirExotic54` contributes 46 distinct E-slot dimensions
because its frozen first-12 segment duplicates the 8 flipped
hermitian directions also used in `pairDirFlip16`.

Six of the eight (the `(9, 13)`, `(9, 14)`, `(9, 15)` patterns)
assemble directly from C96-3a3's landed order-one theorems
`exPairMat_orderOne_A` / `exPairMat_orderOne_B`. The remaining
pair `(8, 9)` (and its transpose `(9, 8)`) is this brick's one
genuine proof obligation, discharged here by a separate small
argument (`exPairMat_orderOne_SS`, both coordinates
lepton-singlets):

* `[M, genC] = 0` outright: at a support entry of
  `M = exPairMat u v z` with `u, v` in `{8, 9}`, both indices are
  lifts of lepton-singlet folded coordinates, so both have
  `genCVal = Complex.I` (the landed table
  `exGenC_table_singlet`) and the diagonal-commutator factor
  vanishes.
* `[M, genM a] = 0` outright: the intermediate index of a
  nonzero product entry would have folded coordinate `8` or `9`,
  hence value in `{8, 9, 24, 25}`, while `genM` support lies in
  `[18, 24) union [26, 32)` (the landed `genM_supp`) - disjoint,
  so both products vanish by `disjoint_mul_zero`. (C96-3a3's
  triplet-mate argument is not needed and not used: it required
  a column `>= 10`.)
* `[M, genH k] = 0` is the landed
  `exPairMat_comm_genH_eq_zero` (both folded coordinates `>= 8`).

With all three commutators zero, every double commutator in
`OrderOneHolds` vanishes.

## Kills and fences (on the face)

- K-C96-1 (armed): a PROVED 89th independent direction, or any
  proved finrank of `PairSpace` different from 88, kills the T4
  note. Nothing here proves any finrank or any independence.
  A stall is a stall, never a kill.
- K-C96-2 (vacuity): every direction named here is an element of
  `PairSpace` with its four coupling conditions proved; no slot
  counting, no zero padding.
- Generations IMPOSED; CKM/PMNS input-only; Q3 OPEN; NO CLAIM.
  The old 46 -> 10 gloss is UNSOUND AS STATED and is not cited.
-/

open Matrix

namespace ThetLogos

/-! ## 1. The both-singlets order-one theorem (the (8, 9) pair) -/

/-- A single-coordinate pair pattern at two lepton-singlet folded
    coordinates commutes with `genC`: at every support entry both
    `genCVal` charges equal `Complex.I`, so the diagonal
    commutator factor vanishes. -/
theorem exPairMat_comm_genC_eq_zero_SS {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : v.val = 8 ∨ v.val = 9)
    (z : ℂ) :
    exPairMat u v z * genC - genC * exPairMat u v z = 0 := by
  ext i j
  have h2 := comm_diag_entry (exPairMat u v z) genCVal genC
    (fun x y => genC_eq_diag x y) i j
  rw [h2]
  by_cases hD : exPairMat u v z i j = 0
  · rw [hD, zero_mul, Matrix.zero_apply]
  · have hcoord := exPairMat_ne_zero hD
    have hCi := (exGenC_table_singlet hu hcoord.1).1
    have hCj := (exGenC_table_singlet hv hcoord.2.1).1
    rw [hCj, hCi, sub_self, mul_zero, Matrix.zero_apply]

/-- A single-coordinate pair pattern at two lepton-singlet folded
    coordinates commutes with every `genM a`: the folded
    coordinates `8, 9` lift to values `{8, 9, 24, 25}`, disjoint
    from the `genM` support ranges `[18, 24)` and `[26, 32)`, so
    both products vanish. -/
theorem exPairMat_comm_genM_eq_zero_SS {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : v.val = 8 ∨ v.val = 9)
    (z : ℂ) (a : Fin 8) :
    exPairMat u v z * genM a - genM a * exPairMat u v z = 0 := by
  have hPM : exPairMat u v z * genM a = 0 := by
    apply disjoint_mul_zero (fun x => acoord x = v)
    · intro i k hik
      exact (exPairMat_ne_zero hik).2.1
    · intro k j hkj hkv
      have hr := (genM_supp a k j hkj).1
      rw [exAcoord_eq_iff] at hkv
      rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;>
        rcases hkv with hk | hk <;>
        rcases hv with hv | hv <;> omega
  have hMP : genM a * exPairMat u v z = 0 := by
    apply disjoint_mul_zero
      (fun x => (18 ≤ x.val ∧ x.val < 24) ∨ (26 ≤ x.val ∧ x.val < 32))
    · intro i k hik
      exact (genM_supp a i k hik).2
    · intro k j hkj hr
      have hcoord := (exPairMat_ne_zero hkj).1
      rw [exAcoord_eq_iff] at hcoord
      rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;>
        rcases hcoord with hc | hc <;>
        rcases hu with hu | hu <;> omega
  rw [hPM, hMP, sub_self]

/-- **The both-singlets order-one theorem.** Every
    single-coordinate pair pattern at two lepton-singlet folded
    coordinates `u, v` in `{8, 9}` satisfies the order-one
    condition: all three commutators vanish outright (with `genH`
    by the landed `exPairMat_comm_genH_eq_zero`). This covers the
    `(8, 9)` and `(9, 8)` patterns that C96-3a3's orientations A
    and B did not reach. -/
theorem exPairMat_orderOne_SS {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : v.val = 8 ∨ v.val = 9)
    (z : ℂ) : OrderOneHolds (exPairMat u v z) := by
  intro g1 g2
  fin_cases g1
  · show (exPairMat u v z * genC - genC * exPairMat u v z) * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genC - genC * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genC_eq_zero_SS hu hv z,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genH 0 - genH 0 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genH 0 - genH 0 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genH_eq_zero (by omega) (by omega) z 0,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genH 1 - genH 1 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genH 1 - genH 1 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genH_eq_zero (by omega) (by omega) z 1,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genH 2 - genH 2 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genH 2 - genH 2 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genH_eq_zero (by omega) (by omega) z 2,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 0 - genM 0 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 0 - genM 0 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 0,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 1 - genM 1 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 1 - genM 1 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 1,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 2 - genM 2 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 2 - genM 2 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 2,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 3 - genM 3 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 3 - genM 3 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 3,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 4 - genM 4 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 4 - genM 4 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 4,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 5 - genM 5 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 5 - genM 5 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 5,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 6 - genM 6 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 6 - genM 6 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 6,
      zero_mul, mul_zero, sub_zero]
  · show (exPairMat u v z * genM 7 - genM 7 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 7 - genM 7 * exPairMat u v z)
        = 0
    rw [exPairMat_comm_genM_eq_zero_SS hu hv z 7,
      zero_mul, mul_zero, sub_zero]

/-! ## 2. The supplement family: the 8 antisymmetric patterns -/

/-- Folded row coordinate of the `m`-th supplement pair: `8` for
    the first pair `(8, 9)`, `9` for the remaining pairs. -/
def suppU (m : Nat) : Fin 16 :=
  ⟨if m = 0 then 8 else 9, by split_ifs <;> omega⟩

/-- Folded column coordinate of the `m`-th supplement pair: `9`,
    `13`, `14`, `15` for `m = 0, 1, 2` and every `m >= 3`. -/
def suppV (m : Nat) : Fin 16 :=
  ⟨if m = 0 then 9 else if m = 1 then 13 else if m = 2 then 14
    else 15, by split_ifs <;> omega⟩

theorem suppU_val (m : Nat) :
    (suppU m).val = if m = 0 then 8 else 9 := rfl

theorem suppV_val (m : Nat) :
    (suppV m).val = if m = 0 then 9 else if m = 1 then 13
      else if m = 2 then 14 else 15 := rfl

/-- The supplement row coordinate is a lepton singlet. -/
theorem suppU_spec (m : Nat) :
    (suppU m).val = 8 ∨ (suppU m).val = 9 := by
  rw [suppU_val]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- At the first supplement pair the row coordinate is `9` off
    the initial index: for `m ≠ 0` the row is the singlet `9`. -/
theorem suppU_val_of_ne_zero {m : Nat} (hm : m ≠ 0) :
    (suppU m).val = 9 := by
  rw [suppU_val, if_neg hm]

/-- The supplement column coordinate is either the singlet `9`
    (at `m = 0`) or a right-handed coordinate in `[10, 15]`. -/
theorem suppV_spec (m : Nat) :
    (suppV m).val = 9 ∨ (10 ≤ (suppV m).val ∧ (suppV m).val ≤ 15) := by
  rw [suppV_val]
  by_cases h0 : m = 0
  · rw [if_pos h0]
    exact Or.inl rfl
  · rw [if_neg h0]
    by_cases h1 : m = 1
    · rw [if_pos h1]
      exact Or.inr ⟨by norm_num, by norm_num⟩
    · rw [if_neg h1]
      by_cases h2 : m = 2
      · rw [if_pos h2]
        exact Or.inr ⟨by norm_num, by norm_num⟩
      · rw [if_neg h2]
        exact Or.inr ⟨by norm_num, by norm_num⟩

/-- Membership of the `m`-th supplement antisymmetric pattern in
    `PairSpace`: at `m = 0` (the pair `(8, 9)`) by the
    both-singlets theorem `exPairMat_orderOne_SS`; at `m ≠ 0`
    (the pairs `(9, 13)`, `(9, 14)`, `(9, 15)`) by C96-3a3's
    orientations A and B. -/
theorem exAntiMat_supp_mem (m : Nat) (z : ℂ) :
    exAntiMat (suppU m) (suppV m) z ∈ PairSpace := by
  by_cases hm : m = 0
  · have hV : (suppV m).val = 9 := by
      rw [suppV_val, if_pos hm]
    exact exAntiMat_mem
      (exPairMat_orderOne_SS (suppU_spec m) (Or.inr hV) z)
      (exPairMat_orderOne_SS (Or.inr hV) (suppU_spec m) z)
  · have hU : (suppU m).val = 9 := suppU_val_of_ne_zero hm
    have hV : 10 ≤ (suppV m).val ∧ (suppV m).val ≤ 15 := by
      have h9 : (suppV m).val ≠ 9 := by
        rw [suppV_val, if_neg hm]
        split_ifs <;> norm_num
      exact (suppV_spec m).resolve_left h9
    exact exAntiMat_mem
      (exPairMat_orderOne_A (Or.inr hU) hV z)
      (exPairMat_orderOne_B hV (Or.inr hU) z)

/-- **The exotic supplement (C96-3a4 headline).** The 8
    antisymmetric folded patterns left unexhibited by C96-3a3:
    indices `0, 1` are the pair `(8, 9)` (real part `z = 1`,
    imaginary part `z = Complex.I`, via the phase function
    `exPhase`), indices `2, 3` the pair `(9, 13)`, indices
    `4, 5` the pair `(9, 14)`, and indices `6, 7` the pair
    `(9, 15)`. Each is an explicit element of `PairSpace` with
    all four coupling conditions proved. This family is the
    supplement segment of C96-3b's accounting: SM 18 + flipped
    16 + exotic-segment 46 distinct + supplement 8 = 88 distinct
    directions. No finrank and no independence is asserted. -/
noncomputable def pairDirExoticSupp8 (n : Fin 8) : PairSpace :=
  ⟨exAntiMat (suppU (n.val / 2)) (suppV (n.val / 2)) (exPhase n.val),
    exAntiMat_supp_mem _ _⟩

/-- The underlying block of the `n`-th supplement direction is
    the antisymmetric folded pattern at its coordinate pair. -/
theorem pairDirExoticSupp8_apply (n : Fin 8) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ)
      = exAntiMat (suppU (n.val / 2)) (suppV (n.val / 2))
        (exPhase n.val) := rfl

/-- Index `0`: the real `(8, 9)` pattern. -/
theorem pairDirExoticSupp8_0 :
    (pairDirExoticSupp8 0 : Matrix I32 I32 ℂ)
      = exAntiMat 8 9 1 := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((0 : Fin 8).val / 2) = 8 := by decide
  have h2 : suppV ((0 : Fin 8).val / 2) = 9 := by decide
  have h3 : exPhase (0 : Fin 8).val = 1 := by rfl
  rw [h1, h2, h3]

/-- Index `1`: the imaginary `(8, 9)` pattern. -/
theorem pairDirExoticSupp8_1 :
    (pairDirExoticSupp8 1 : Matrix I32 I32 ℂ)
      = exAntiMat 8 9 Complex.I := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((1 : Fin 8).val / 2) = 8 := by decide
  have h2 : suppV ((1 : Fin 8).val / 2) = 9 := by decide
  have h3 : exPhase (1 : Fin 8).val = Complex.I := by rfl
  rw [h1, h2, h3]

/-- Index `2`: the real `(9, 13)` pattern. -/
theorem pairDirExoticSupp8_2 :
    (pairDirExoticSupp8 2 : Matrix I32 I32 ℂ)
      = exAntiMat 9 13 1 := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((2 : Fin 8).val / 2) = 9 := by decide
  have h2 : suppV ((2 : Fin 8).val / 2) = 13 := by decide
  have h3 : exPhase (2 : Fin 8).val = 1 := by rfl
  rw [h1, h2, h3]

/-- Index `3`: the imaginary `(9, 13)` pattern. -/
theorem pairDirExoticSupp8_3 :
    (pairDirExoticSupp8 3 : Matrix I32 I32 ℂ)
      = exAntiMat 9 13 Complex.I := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((3 : Fin 8).val / 2) = 9 := by decide
  have h2 : suppV ((3 : Fin 8).val / 2) = 13 := by decide
  have h3 : exPhase (3 : Fin 8).val = Complex.I := by rfl
  rw [h1, h2, h3]

/-- Index `4`: the real `(9, 14)` pattern. -/
theorem pairDirExoticSupp8_4 :
    (pairDirExoticSupp8 4 : Matrix I32 I32 ℂ)
      = exAntiMat 9 14 1 := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((4 : Fin 8).val / 2) = 9 := by decide
  have h2 : suppV ((4 : Fin 8).val / 2) = 14 := by decide
  have h3 : exPhase (4 : Fin 8).val = 1 := by rfl
  rw [h1, h2, h3]

/-- Index `5`: the imaginary `(9, 14)` pattern. -/
theorem pairDirExoticSupp8_5 :
    (pairDirExoticSupp8 5 : Matrix I32 I32 ℂ)
      = exAntiMat 9 14 Complex.I := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((5 : Fin 8).val / 2) = 9 := by decide
  have h2 : suppV ((5 : Fin 8).val / 2) = 14 := by decide
  have h3 : exPhase (5 : Fin 8).val = Complex.I := by rfl
  rw [h1, h2, h3]

/-- Index `6`: the real `(9, 15)` pattern. -/
theorem pairDirExoticSupp8_6 :
    (pairDirExoticSupp8 6 : Matrix I32 I32 ℂ)
      = exAntiMat 9 15 1 := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((6 : Fin 8).val / 2) = 9 := by decide
  have h2 : suppV ((6 : Fin 8).val / 2) = 15 := by decide
  have h3 : exPhase (6 : Fin 8).val = 1 := by rfl
  rw [h1, h2, h3]

/-- Index `7`: the imaginary `(9, 15)` pattern. -/
theorem pairDirExoticSupp8_7 :
    (pairDirExoticSupp8 7 : Matrix I32 I32 ℂ)
      = exAntiMat 9 15 Complex.I := by
  rw [pairDirExoticSupp8_apply]
  have h1 : suppU ((7 : Fin 8).val / 2) = 9 := by decide
  have h2 : suppV ((7 : Fin 8).val / 2) = 15 := by decide
  have h3 : exPhase (7 : Fin 8).val = Complex.I := by rfl
  rw [h1, h2, h3]

end ThetLogos
