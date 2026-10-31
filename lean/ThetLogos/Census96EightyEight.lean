import ThetLogos.Census96PairSupplement

/-!
# ThetLogos.Census96EightyEight - C96-3b: THE 88 THEOREM (assembly)

Final brick of C96-3 (lane 2 of the Census-96 line; pack
`pack-c96-3b.md`). The frozen interfaces of C96-3a / C96-3a2 /
C96-3a3 / C96-3a4 (`PairSpace`, `mem_pairSpace_iff`, `pairDirSM18`,
`pairDirFlip16`, `pairDirExotic54`, `pairDirExoticSupp8`, and the
`ex*` engine) are imported and untouched; every name defined here
is new. No landed file is edited.

## The distinctness accounting (on the face)

The 88 distinct directions of the T4 split, assembled as
`dir88 : Fin 88 -> PairSpace`:

- indices 0-17: `pairDirSM18` (3a2) - 18 SM-like directions;
- indices 18-33: `pairDirFlip16` (3a2) - 16 flipped directions;
- indices 34-79: the **exotic-distinct 46** (this module,
  `pairDirExoticDistinct46`): the subfamily of `pairDirExotic54`
  with the 8 flipped hermitian directions (its first-12 segment's
  indices 0-7, i.e. `dirs22` 10-17, already used in `pairDirFlip16`)
  REMOVED - concretely `pairDirExotic` positions 8-11 (`dirs22`
  18-21, the NuREbarR / EREbarR survivors) + the hermitian E-slot
  segment `exHermDir` (24) + the anti E-slot segment `exAntiDir`
  (18) = 4 + 24 + 18 = 46;
- indices 80-87: `pairDirExoticSupp8` (3a4) - the 8 antisymmetric
  supplement patterns.

Total: 18 + 16 + 46 + 8 = 88.

## Kills and fences (on the face)

- K-C96-1 (armed): a PROVED 89th independent direction, or any
  proved finrank of `PairSpace` different from 88, kills the T4
  note. A stall is a stall, never a kill.
- K-C96-2 (vacuity): the bound is a pivot-injection, never slot
  counting.
- Generations IMPOSED; CKM/PMNS input-only; Q3 OPEN; NO CLAIM.
  The old 46 -> 10 gloss is UNSOUND AS STATED and is not cited.

## Status of this brick (PARTIAL at the bound seam)

PROVED here (all axiom-clean, see the verification note):

- the assembly `dir88` of the 88 distinct directions, with the
  segment transports `dir88Mat_of_lt18` / `_of_flip` / `_of_exotic`
  / `_of_supp`;
- `dir88Mat_independent` and `dir88_independent`: the 88 directions
  are linearly independent over `ℝ`, by entry pivots (23 extraction
  groups: 4 SM + yR + 4 flipped + G10 + EREbarR + 12 E-slot);
- `finrank_ge_88 : 88 ≤ Module.finrank ℝ PairSpace`.

NOT proved here - the bound seam, named precisely: the inequality
`Module.finrank ℝ PairSpace ≤ 88` is OPEN in this module. The
missing step is the cross-coordinate support-forcing theorem: for
a general `M ∈ PairSpace`, every folded cross coordinate
`(u, v)` outside the 44 ordered pivot slots must vanish - the
A-slots `(0,8),(8,0),(1,9),(9,1),(2,10),(10,2),(3,11),(11,3)`,
the flip slots `(0,9),(9,0),(1,8),(8,1),(2,11),(11,2),(3,10),
(10,3)`, both orders of the 12 E-slot pairs `(u, v)` with
`u ∈ {8, 9}`, `v ∈ {10, ..., 15}`, the pair `(8,9),(9,8)`, and
the diagonals `(8,8)`, `(9,9)`. Given that support theorem, the
pivot-evaluation map at the 88 real pivot functionals used in
the extraction groups is injective and `finrank = 88` follows.
The forcing itself must come from `mem_pairSpace_iff`'s four
conditions (admissibility of `M` and `M*`, order-one for both) -
the order-one forcing on a general element is the unbuilt part.
Per the brick's outcomes this is a STALL, not a kill: K-C96-1
does not fire (no different number is proved), and
`finrank ℝ PairSpace = 88` is NOT claimed by this module.
-/

open Matrix

namespace ThetLogos

/-! ## 1. The exotic-distinct 46 -/

/-- The four exotic directions of `pairDirExotic` NOT duplicated in
    `pairDirFlip16`: positions 8-11 of the landed `Fin 12` family,
    i.e. `dirs22` 18-21 (the NuREbarR / EREbarR survivors, real and
    imaginary parts). Positions 0-7 of `pairDirExotic` are the
    flipped hermitian directions `dirs22` 10-17, already consumed
    by `pairDirFlip16` (as `flipHermDir`), so they are excluded
    here - this exclusion is the distinctness repair of the
    C96-3a3 accounting seam. -/
def exDistinctSeg4 (k : Fin 4) : PairSpace :=
  pairDirExotic ⟨k.val + 8, by have h := k.isLt; omega⟩

/-- The first segment of the exotic-distinct family agrees with
    `pairDirExotic54` at its positions 8-11. -/
theorem exDistinctSeg4_eq_exotic54 (k : Fin 4) :
    exDistinctSeg4 k
      = pairDirExotic54 ⟨k.val + 8, by have h := k.isLt; omega⟩ := by
  have h := pairDirExotic54_exotic ⟨k.val + 8, by have h := k.isLt; omega⟩
  rw [exDistinctSeg4]
  exact h.symm

/-- The underlying block of the `k`-th seg-4 direction is
    `dirs22` at index `k + 18`. -/
theorem exDistinctSeg4_apply (k : Fin 4) :
    (exDistinctSeg4 k : Matrix I32 I32 ℂ)
      = dirs22 ⟨k.val + 18, by have h := k.isLt; omega⟩ := by
  show (pairDirExotic ⟨k.val + 8, by have h := k.isLt; omega⟩
    : Matrix I32 I32 ℂ) = _
  unfold pairDirExotic
  show (pairDir22 ⟨k.val + 8 + 10, by have h := k.isLt; omega⟩
    : Matrix I32 I32 ℂ) = _
  rw [pairDir22_apply]

/-- **The exotic-distinct 46 (C96-3b assembly segment).** The
    exotic directions of the 88, with the 8 flipped duplicates of
    `pairDirExotic54`'s first segment removed: indices 0-3 are
    `exDistinctSeg4` (`dirs22` 18-21), indices 4-27 are the
    hermitian E-slot patterns `exHermDir` (24), indices 28-45 are
    the anti E-slot patterns `exAntiDir` (18). -/
noncomputable def pairDirExoticDistinct46 : Fin 46 → PairSpace :=
  Fin.append (Fin.append exDistinctSeg4 exHermDir) exAntiDir

/-- Segment lemma: indices 0-3 of the exotic-distinct family are
    the seg-4 directions. -/
theorem pairDirExoticDistinct46_seg4 (k : Fin 4) :
    pairDirExoticDistinct46 ⟨k.val, by have h := k.isLt; omega⟩
      = exDistinctSeg4 k := by
  have e1 : (⟨k.val, by have h := k.isLt; omega⟩ : Fin 46)
      = Fin.castAdd 18 (Fin.castAdd 24 k) := Fin.ext rfl
  rw [pairDirExoticDistinct46, e1, Fin.append_left, Fin.append_left]

/-- Segment lemma: indices 4-27 of the exotic-distinct family are
    the hermitian E-slot directions. -/
theorem pairDirExoticDistinct46_herm (k : Fin 24) :
    pairDirExoticDistinct46 ⟨k.val + 4, by have h := k.isLt; omega⟩
      = exHermDir k := by
  have e1 : (⟨k.val + 4, by have h := k.isLt; omega⟩ : Fin 46)
      = Fin.castAdd 18 (Fin.natAdd 4 k) := by
    apply Fin.ext
    show k.val + 4 = 4 + k.val
    omega
  rw [pairDirExoticDistinct46, e1, Fin.append_left, Fin.append_right]

/-- Segment lemma: indices 28-45 of the exotic-distinct family are
    the anti E-slot directions. -/
theorem pairDirExoticDistinct46_anti (k : Fin 18) :
    pairDirExoticDistinct46 ⟨k.val + 28, by have h := k.isLt; omega⟩
      = exAntiDir k := by
  have e1 : (⟨k.val + 28, by have h := k.isLt; omega⟩ : Fin 46)
      = Fin.natAdd 28 k := by
    apply Fin.ext
    show k.val + 28 = 28 + k.val
    omega
  rw [pairDirExoticDistinct46, e1, Fin.append_right]

/-! ## 2. The 88 assembly -/

/-- **The 88 distinct directions (C96-3b assembly).** The single
    indexed family `Fin 88 -> PairSpace` of the 88 theorem:
    SM 18 + flipped 16 + exotic-distinct 46 + supplement 8, in
    this order. Every member is a proved element of `PairSpace`
    by the landed membership theorems of its segment family
    (K-C96-2 guard: no slot is counted, every direction is an
    explicit element with its four coupling conditions proved). -/
noncomputable def dir88 : Fin 88 → PairSpace :=
  Fin.append (Fin.append (Fin.append pairDirSM18 pairDirFlip16)
    pairDirExoticDistinct46) pairDirExoticSupp8

/-- Segment lemma: indices 0-17 of `dir88` are the SM-like
    directions `pairDirSM18`. -/
theorem dir88_SM (k : Fin 18) :
    dir88 ⟨k.val, by have h := k.isLt; omega⟩ = pairDirSM18 k := by
  have e1 : (⟨k.val, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.castAdd 8 (Fin.castAdd 46 (Fin.castAdd 16 k)) := Fin.ext rfl
  rw [dir88, e1, Fin.append_left, Fin.append_left, Fin.append_left]

/-- Segment lemma: indices 18-33 of `dir88` are the flipped
    directions `pairDirFlip16`. -/
theorem dir88_flip (k : Fin 16) :
    dir88 ⟨k.val + 18, by have h := k.isLt; omega⟩ = pairDirFlip16 k := by
  have e1 : (⟨k.val + 18, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.castAdd 8 (Fin.castAdd 46 (Fin.natAdd 18 k)) := by
    apply Fin.ext
    show k.val + 18 = 18 + k.val
    omega
  rw [dir88, e1, Fin.append_left, Fin.append_left, Fin.append_right]

/-- Segment lemma: indices 34-79 of `dir88` are the exotic-distinct
    directions `pairDirExoticDistinct46`. -/
theorem dir88_exotic (k : Fin 46) :
    dir88 ⟨k.val + 34, by have h := k.isLt; omega⟩
      = pairDirExoticDistinct46 k := by
  have e1 : (⟨k.val + 34, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.castAdd 8 (Fin.natAdd 34 k) := by
    apply Fin.ext
    show k.val + 34 = 34 + k.val
    omega
  rw [dir88, e1, Fin.append_left, Fin.append_right]

/-- Segment lemma: indices 80-87 of `dir88` are the supplement
    directions `pairDirExoticSupp8`. -/
theorem dir88_supp (k : Fin 8) :
    dir88 ⟨k.val + 80, by have h := k.isLt; omega⟩
      = pairDirExoticSupp8 k := by
  have e1 : (⟨k.val + 80, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.natAdd 80 k := by
    apply Fin.ext
    show k.val + 80 = 80 + k.val
    omega
  rw [dir88, e1, Fin.append_right]

/-- The underlying-matrix family of the 88 directions: independence
    is proved for this family in `Matrix I32 I32 ℂ` and transported
    to `PairSpace`. -/
noncomputable def dir88Mat (k : Fin 88) : Matrix I32 I32 ℂ := (dir88 k : Matrix I32 I32 ℂ)

/-- `dir88Mat` at an SM index is the SM direction's block. -/
theorem dir88Mat_SM (k : Fin 18) :
    dir88Mat ⟨k.val, by have h := k.isLt; omega⟩
      = (pairDirSM18 k : Matrix I32 I32 ℂ) := by
  rw [dir88Mat, dir88_SM]

/-- `dir88Mat` at a flipped index is the flipped direction's block. -/
theorem dir88Mat_flip (k : Fin 16) :
    dir88Mat ⟨k.val + 18, by have h := k.isLt; omega⟩
      = (pairDirFlip16 k : Matrix I32 I32 ℂ) := by
  rw [dir88Mat, dir88_flip]

/-- `dir88Mat` at an exotic-distinct index is that direction's block. -/
theorem dir88Mat_exotic (k : Fin 46) :
    dir88Mat ⟨k.val + 34, by have h := k.isLt; omega⟩
      = (pairDirExoticDistinct46 k : Matrix I32 I32 ℂ) := by
  rw [dir88Mat, dir88_exotic]

/-- `dir88Mat` at a supplement index is the supplement block. -/
theorem dir88Mat_supp (k : Fin 8) :
    dir88Mat ⟨k.val + 80, by have h := k.isLt; omega⟩
      = (pairDirExoticSupp8 k : Matrix I32 I32 ℂ) := by
  rw [dir88Mat, dir88_supp]

/-! ## 3. Entry infrastructure for the pivot extraction -/

/-- Grading sign `1` on the plus ranges `[0, 8)` and `[24, 32)`. -/
theorem gSign_eq_one_of_val {x : I32} (h : x.val < 8 ∨ 24 ≤ x.val) :
    gSign x = 1 := by
  rw [gSign_apply]
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

/-- Grading sign `-1` on the minus range `[8, 24)`. -/
theorem gSign_eq_neg_one_of_val {x : I32} (h : 8 ≤ x.val ∧ x.val < 24) :
    gSign x = -1 := by
  rw [gSign_apply]
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

/-- Entries of the S-conjugated SM pattern: sign-twisted entries of
    the underlying `dirs22` direction. -/
theorem antiSMMat_apply (k : Fin 8) (i j : I32) :
    antiSMMat k i j
      = aRSgn i * (dirs22 ⟨k.val, by have h := k.isLt; omega⟩ i j
        * aRSgn j) := by
  unfold antiSMMat
  rw [Matrix.mul_assoc, aRSign_mul_apply, mul_aRSign_apply]

/-- Entries of the S-conjugated flipped pattern. -/
theorem antiFlipMat_apply (k : Fin 8) (i j : I32) :
    antiFlipMat k i j
      = aRSgn i * (dirs22 ⟨k.val + 10, by have h := k.isLt; omega⟩ i j
        * aRSgn j) := by
  unfold antiFlipMat
  rw [Matrix.mul_assoc, aRSign_mul_apply, mul_aRSign_apply]

/-- Entries of the anti SM direction: `Complex.I` times the
    S-conjugated pattern. -/
theorem antiSMDir_apply (k : Fin 8) (i j : I32) :
    (antiSMDir k : Matrix I32 I32 ℂ) i j
      = Complex.I * antiSMMat k i j := by
  show (Complex.I • antiSMMat k) i j = _
  rw [Matrix.smul_apply, smul_eq_mul]

/-- Entries of the anti flipped direction. -/
theorem antiFlipDir_apply (k : Fin 8) (i j : I32) :
    (antiFlipDir k : Matrix I32 I32 ℂ) i j
      = Complex.I * antiFlipMat k i j := by
  show (Complex.I • antiFlipMat k) i j = _
  rw [Matrix.smul_apply, smul_eq_mul]

/-- The SM-like family at a hermitian segment index is the
    `dirs22` direction of the same index, entrywise. -/
theorem pairDirSM18_apply_of_lt (k : Fin 10) (i j : I32) :
    (pairDirSM18 ⟨k.val, by have h := k.isLt; omega⟩
      : Matrix I32 I32 ℂ) i j
      = dirs22 ⟨k.val, by have h := k.isLt; omega⟩ i j := by
  rw [pairDirSM18_SM]
  show (pairDirSM k : Matrix I32 I32 ℂ) i j = _
  unfold pairDirSM
  rw [pairDir22_apply]

/-- The SM-like family at an anti segment index is the anti SM
    direction of the same segment index, entrywise. -/
theorem pairDirSM18_apply_of_ge (k : Fin 8) (i j : I32) :
    (pairDirSM18 ⟨10 + k.val, by have h := k.isLt; omega⟩
      : Matrix I32 I32 ℂ) i j
      = (antiSMDir k : Matrix I32 I32 ℂ) i j := by
  rw [pairDirSM18_anti]

/-- The flipped family at a hermitian segment index is the
    `dirs22` direction of index `k + 10`, entrywise. -/
theorem pairDirFlip16_apply_of_lt (k : Fin 8) (i j : I32) :
    (pairDirFlip16 ⟨k.val, by have h := k.isLt; omega⟩
      : Matrix I32 I32 ℂ) i j
      = dirs22 ⟨k.val + 10, by have h := k.isLt; omega⟩ i j := by
  rw [pairDirFlip16_herm]
  show (flipHermDir k : Matrix I32 I32 ℂ) i j = _
  unfold flipHermDir
  rw [pairDir22_apply]

/-- The flipped family at an anti segment index is the anti
    flipped direction of the same segment index, entrywise. -/
theorem pairDirFlip16_apply_of_ge (k : Fin 8) (i j : I32) :
    (pairDirFlip16 ⟨8 + k.val, by have h := k.isLt; omega⟩
      : Matrix I32 I32 ℂ) i j
      = (antiFlipDir k : Matrix I32 I32 ℂ) i j := by
  rw [pairDirFlip16_anti]

/-- J-compatibility transport for `dirs22`: the value at the
    partner entry `(partner j, partner i)` equals the value at
    `(i, j)`. -/
theorem dirs22_partner_entry (m : Fin 22) (i j : I32) :
    dirs22 m (partner j) (partner i) = dirs22 m i j :=
  (jCompat_entry_local _ (dirs22_mem m).2.2.2.1 i j).symm

/-- Self-adjointness transport for `dirs22` at `(25, 8)`. -/
theorem dirs22_apply_25_8 (m : Fin 22) :
    dirs22 m 25 8 = star (dirs22 m 8 25) :=
  selfAdjoint_entry _ (dirs22_mem m).2.2.1 _ _

/-- `smDirac` vanishes off its support (contrapositive form of the
    landed `smDirac_supp_aux`). -/
theorem smDirac_eq_zero_of_not_supp88 {yNu yE yU yD yR : ℂ} {r c : I32}
    (h : ¬ ((r.val < 8 ∧ c.val = r.val + 8) ∨
        (8 ≤ r.val ∧ r.val < 16 ∧ c.val = r.val - 8) ∨
        (16 ≤ r.val ∧ r.val < 24 ∧ c.val = r.val + 8) ∨
        (24 ≤ r.val ∧ r.val < 32 ∧ c.val = r.val - 8) ∨
        (r.val = 8 ∧ c.val = 24) ∨ (r.val = 24 ∧ c.val = 8))) :
    smDirac yNu yE yU yD yR r c = 0 := by
  by_contra hc
  exact h (smDirac_supp_aux _ _ _ _ _ _ _ hc)

/-- Every `dirs22` direction vanishes at an E-slot pivot entry
    `(r, c)` with `r` in `{24, 25}` and `c` in `10..15`: the SM
    directions by their support characterization, the Retarget
    exotics by their support lists. (Reproved here from the landed
    support lemmas; the C96-2a module is not imported.) -/
theorem dirs22_eq_zero_of_newpivot88 {r c : I32}
    (hr : r.val = 24 ∨ r.val = 25)
    (hc : 10 ≤ c.val ∧ c.val ≤ 15) (i : Fin 22) : dirs22 i r c = 0 := by
  have hns : ¬ ((r.val < 8 ∧ c.val = r.val + 8) ∨
      (8 ≤ r.val ∧ r.val < 16 ∧ c.val = r.val - 8) ∨
      (16 ≤ r.val ∧ r.val < 24 ∧ c.val = r.val + 8) ∨
      (24 ≤ r.val ∧ r.val < 32 ∧ c.val = r.val - 8) ∨
      (r.val = 8 ∧ c.val = 24) ∨ (r.val = 24 ∧ c.val = 8)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  fin_cases i
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · exact smDirac_eq_zero_of_not_supp88 hns
  · by_contra hne
    have hs := exoticReNuLeR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticImNuLeR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticReELNuR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticImELNuR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticReULDR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticImULDR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticReDLUR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticImDLUR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticReNuREbarR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticImNuREbarR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticReEREbarR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)
  · by_contra hne
    have hs := exoticImEREbarR_supp r c hne
    rcases hs with (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      (have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2; omega)

/-- A hermitian E-slot pattern vanishes at an entry matching
    neither of its two folded coordinates. -/
theorem exHermMat_eq_zero_of_acoor {u v : Fin 16} (z : ℂ) {r c : I32}
    (h1 : ¬ (acoord r = u ∧ acoord c = v))
    (h2 : ¬ (acoord r = v ∧ acoord c = u)) :
    exHermMat u v z r c = 0 := by
  unfold exHermMat
  rw [Matrix.add_apply, exPairMat_eq_zero_of z h1,
    exPairMat_eq_zero_of z h2, add_zero]

/-- An anti E-slot pattern vanishes at an entry matching neither
    of its two folded coordinates. -/
theorem exAntiMat_eq_zero_of_acoor {u v : Fin 16} (z : ℂ) {r c : I32}
    (h1 : ¬ (acoord r = u ∧ acoord c = v))
    (h2 : ¬ (acoord r = v ∧ acoord c = u)) :
    exAntiMat u v z r c = 0 := by
  unfold exAntiMat
  rw [Matrix.sub_apply, exPairMat_eq_zero_of z h1,
    exPairMat_eq_zero_of z h2, sub_zero]

/-- A single-coordinate pair pattern at its high cross entry
    `(a + 16, b)` (both folded coordinates `>= 8`): the value is
    exactly `z`. -/
theorem exPairMat_apply_hi {a b : Fin 16} (ha : 8 ≤ a.val) (hb : 8 ≤ b.val)
    (z : ℂ) :
    exPairMat a b z ⟨a.val + 16, by have h := a.isLt; omega⟩
        ⟨b.val, by have h := b.isLt; omega⟩ = z := by
  have hgi : gSign (⟨a.val + 16, by have h := a.isLt; omega⟩ : I32) = 1 :=
    gSign_eq_one_of_val (Or.inr (by show 24 ≤ a.val + 16; omega))
  have hgj : gSign (⟨b.val, by have h := b.isLt; omega⟩ : I32) = -1 :=
    gSign_eq_neg_one_of_val ⟨hb, by show b.val < 24; omega⟩
  have hai : acoord (⟨a.val + 16, by have h := a.isLt; omega⟩ : I32) = a := by
    apply Fin.ext
    rw [acoord_val]
    show (a.val + 16) % 16 = a.val
    omega
  have haj : acoord (⟨b.val, by have h := b.isLt; omega⟩ : I32) = b := by
    apply Fin.ext
    rw [acoord_val]
    show b.val % 16 = b.val
    omega
  rw [exPairMat_apply, if_pos hgi, if_neg (by rw [hgj]; exact neg_one_ne_one_complex),
    if_pos ⟨hai, haj⟩]

/-- A single-coordinate pair pattern at a foreign high cross entry
    vanishes. -/
theorem exPairMat_apply_hi_of_ne {a b a' b' : Fin 16} (ha : 8 ≤ a.val)
    (hb : 8 ≤ b.val) (h : ¬ (a = a' ∧ b = b')) (z : ℂ) :
    exPairMat a' b' z ⟨a.val + 16, by have h := a.isLt; omega⟩
        ⟨b.val, by have h := b.isLt; omega⟩ = 0 := by
  apply exPairMat_eq_zero_of z
  have hai : acoord (⟨a.val + 16, by have h := a.isLt; omega⟩ : I32) = a := by
    apply Fin.ext
    rw [acoord_val]
    show (a.val + 16) % 16 = a.val
    omega
  have haj : acoord (⟨b.val, by have h := b.isLt; omega⟩ : I32) = b := by
    apply Fin.ext
    rw [acoord_val]
    show b.val % 16 = b.val
    omega
  rw [hai, haj]
  exact h

/-- Values of a hermitian E-slot pattern at its two cross entries:
    `z` at both `(u + 16, v)` and `(v + 16, u)`. -/
theorem exHermMat_apply_hi {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ) :
    exHermMat u v z ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = z ∧
    exHermMat u v z ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = z := by
  have hu8 : 8 ≤ u.val := by omega
  have hv8 : 8 ≤ v.val := by omega
  have hne : ¬ (u = v ∧ v = u) := by
    rintro ⟨h1, -⟩
    have e := congrArg Fin.val h1
    omega
  have hne2 : ¬ (v = u ∧ u = v) := by
    rintro ⟨h1, -⟩
    have e := congrArg Fin.val h1
    omega
  refine ⟨?_, ?_⟩
  · unfold exHermMat
    rw [Matrix.add_apply, exPairMat_apply_hi hu8 hv8 z,
      exPairMat_apply_hi_of_ne hu8 hv8 hne z, add_zero]
  · unfold exHermMat
    rw [Matrix.add_apply, exPairMat_apply_hi_of_ne hv8 hu8 hne2 z,
      exPairMat_apply_hi hv8 hu8 z, zero_add]

/-- Values of an anti E-slot pattern at its two cross entries:
    `z` at `(u + 16, v)` and `-z` at `(v + 16, u)`. -/
theorem exAntiMat_apply_hi {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ) :
    exAntiMat u v z ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = z ∧
    exAntiMat u v z ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = -z := by
  have hu8 : 8 ≤ u.val := by omega
  have hv8 : 8 ≤ v.val := by omega
  have hne : ¬ (u = v ∧ v = u) := by
    rintro ⟨h1, -⟩
    have e := congrArg Fin.val h1
    omega
  have hne2 : ¬ (v = u ∧ u = v) := by
    rintro ⟨h1, -⟩
    have e := congrArg Fin.val h1
    omega
  refine ⟨?_, ?_⟩
  · unfold exAntiMat
    rw [Matrix.sub_apply, exPairMat_apply_hi hu8 hv8 z,
      exPairMat_apply_hi_of_ne hu8 hv8 hne z, sub_zero]
  · unfold exAntiMat
    rw [Matrix.sub_apply, exPairMat_apply_hi_of_ne hv8 hu8 hne2 z,
      exPairMat_apply_hi hv8 hu8 z, zero_sub]

/-- Vanishing of a hermitian E-slot direction at an entry whose
    folded coordinates cannot match its coordinate pair in either
    order (val-range form). -/
theorem exHermDir_eq_zero_of_vals88 (n : Fin 24) {r c : I32}
    (h : ¬ (((acoord r).val = 8 ∨ (acoord r).val = 9) ∧
          10 ≤ (acoord c).val ∧ (acoord c).val ≤ 15) ∧
        ¬ (((acoord c).val = 8 ∨ (acoord c).val = 9) ∧
          10 ≤ (acoord r).val ∧ (acoord r).val ≤ 15)) :
    (exHermDir n : Matrix I32 I32 ℂ) r c = 0 := by
  show exHermMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
    (exPhase n.val) r c = 0
  apply exHermMat_eq_zero_of_acoor
  · intro hc
    have hu := exMajU_spec (n.val / 2)
    have hv := exMajV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    exact h.1 ⟨by omega, by omega, by omega⟩
  · intro hc
    have hu := exMajU_spec (n.val / 2)
    have hv := exMajV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    exact h.2 ⟨by omega, by omega, by omega⟩

/-- Vanishing of an anti E-slot direction at an entry whose folded
    coordinates cannot match its coordinate pair in either order
    (val-range form). -/
theorem exAntiDir_eq_zero_of_vals88 (n : Fin 18) {r c : I32}
    (h : ¬ (((acoord r).val = 8 ∨ (acoord r).val = 9) ∧
          10 ≤ (acoord c).val ∧ (acoord c).val ≤ 15) ∧
        ¬ (((acoord c).val = 8 ∨ (acoord c).val = 9) ∧
          10 ≤ (acoord r).val ∧ (acoord r).val ≤ 15)) :
    (exAntiDir n : Matrix I32 I32 ℂ) r c = 0 := by
  show exAntiMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
    (exPhase n.val) r c = 0
  apply exAntiMat_eq_zero_of_acoor
  · intro hc
    have hu := exMajU_spec (n.val / 2)
    have hv := exMajV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    exact h.1 ⟨by omega, by omega, by omega⟩
  · intro hc
    have hu := exMajU_spec (n.val / 2)
    have hv := exMajV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    exact h.2 ⟨by omega, by omega, by omega⟩

/-- The supplement folded pairs, jointly: `(8, 9)` at `m = 0` and
    `(9, v)` with `v` in `13..15` afterwards. In particular the
    pair `(9, 9)` never occurs. -/
theorem suppUV_spec (m : Nat) :
    ((suppU m).val = 8 ∧ (suppV m).val = 9) ∨
      ((suppU m).val = 9 ∧ 10 ≤ (suppV m).val ∧ (suppV m).val ≤ 15) := by
  rw [suppU_val, suppV_val]
  by_cases h0 : m = 0
  · rw [if_pos h0, if_pos h0]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : m = 1
    · rw [if_pos h1]
      exact Or.inr ⟨rfl, by norm_num, by norm_num⟩
    · rw [if_neg h1]
      by_cases h2 : m = 2
      · rw [if_pos h2]
        exact Or.inr ⟨rfl, by norm_num, by norm_num⟩
      · rw [if_neg h2]
        exact Or.inr ⟨rfl, by norm_num, by norm_num⟩

/-- Vanishing of a supplement direction at an entry whose folded
    coordinates cannot match its coordinate pair in either order
    (val-range form). -/
theorem supp8_eq_zero_of_vals88 (n : Fin 8) {r c : I32}
    (h : ¬ (((acoord r).val = 8 ∧ (acoord c).val = 9) ∨
          ((acoord r).val = 9 ∧ 10 ≤ (acoord c).val ∧ (acoord c).val ≤ 15)) ∧
        ¬ (((acoord c).val = 8 ∧ (acoord r).val = 9) ∨
          ((acoord c).val = 9 ∧ 10 ≤ (acoord r).val ∧ (acoord r).val ≤ 15))) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) r c = 0 := by
  rw [pairDirExoticSupp8_apply]
  apply exAntiMat_eq_zero_of_acoor
  · intro hc
    have hUV := suppUV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    apply h.1
    rcases hUV with ⟨hu, hv⟩ | ⟨hu, hv1, hv2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  · intro hc
    have hUV := suppUV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    apply h.2
    rcases hUV with ⟨hu, hv⟩ | ⟨hu, hv1, hv2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩

/-! ## 4. Pivot extraction lemmas -/

/-- Sum collapse over `Fin 88` to four active indices. -/
theorem sum_collapse4_88 (f : Fin 88 → ℂ) {a b a' b' : Fin 88}
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b')
    (hba' : b ≠ a') (hbb' : b ≠ b') (ha'b' : a' ≠ b')
    (hvan : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → f i = 0) :
    ∑ i, f i = f a + f b + f a' + f b' := by
  have h1 : ∑ i, f i
      = ∑ i ∈ ({a, b, a', b'} : Finset (Fin 88)), f i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hx
    have hx' := (not_or.mp hx).1
    have hrest := (not_or.mp hx).2
    have hx2 := (not_or.mp hrest).1
    have hrest2 := (not_or.mp hrest).2
    have hx3 := (not_or.mp hrest2).1
    have hx4 := (not_or.mp hrest2).2
    exact hvan x hx' hx2 hx3 hx4
  rw [h1, Finset.sum_insert (by simp [hab, haa', hab']),
    Finset.sum_insert (by simp [hba', hbb']),
    Finset.sum_insert (by simp [ha'b']), Finset.sum_singleton,
    ← add_assoc, ← add_assoc]

/-- **Pair extraction for the 88 family:** if a pivot entry `(r, c)`
    sees only the pair `(a, b)` with values `1` and `Complex.I`,
    then a vanishing real-linear combination has `g a = 0` and
    `g b = 0`. (The `CFKernel22.pivot_extract` argument, for
    `dir88Mat`.) -/
theorem pair_extract88 (r c : I32) (a b : Fin 88) (hab : a ≠ b)
    (hva : dir88Mat a r c = 1) (hvb : dir88Mat b r c = Complex.I)
    (hvan : ∀ i : Fin 88, i ≠ a → i ≠ b → dir88Mat i r c = 0)
    (g : Fin 88 → ℝ) (hg : ∑ i, g i • dir88Mat i = 0) :
    g a = 0 ∧ g b = 0 := by
  have hP : ∑ i : Fin 88, (g i • dir88Mat i) r c = 0 := by
    have h := congrFun (congrFun hg r) c
    rwa [Matrix.sum_apply] at h
  have hcollapse : ∑ i : Fin 88, (g i • dir88Mat i) r c
      = (g a • dir88Mat a) r c + (g b • dir88Mat b) r c := by
    have h1 : ∑ i : Fin 88, (g i • dir88Mat i) r c
        = ∑ i ∈ ({a, b} : Finset (Fin 88)), (g i • dir88Mat i) r c := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro x _ hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      have hx' := not_or.mp hx
      have hv := hvan x hx'.1 hx'.2
      show (g x) • ((dir88Mat x) r c) = 0
      rw [hv, smul_zero]
    have h2 : ∑ i ∈ ({a, b} : Finset (Fin 88)), (g i • dir88Mat i) r c
        = (g a • dir88Mat a) r c + (g b • dir88Mat b) r c :=
      Finset.sum_pair hab
    rw [h1, h2]
  rw [hcollapse] at hP
  have hP2 : (g a) • (dir88Mat a r c) + (g b) • (dir88Mat b r c) = 0 := by
    have e : ∀ i : Fin 88, (g i • dir88Mat i) r c
        = (g i) • (dir88Mat i r c) := fun i => Matrix.smul_apply _ _ _ _
    rw [e a, e b] at hP
    exact hP
  rw [hva, hvb] at hP2
  have h' : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I = 0 := by
    have e1 : (g a) • (1 : ℂ) = ((g a : ℝ) : ℂ) := by simp
    have e2 : (g b) • Complex.I = ((g b : ℝ) : ℂ) * Complex.I := by simp
    rw [e1, e2] at hP2
    simpa using hP2
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp at hre him
  exact ⟨hre, him⟩

/-- **Quad extraction, pattern A (SM / flipped groups):** entries
    `e1, e2` see only the four indices `a, b` (hermitian pair) and
    `a', b'` (anti pair), with values `(1, I, I, -1)` at `e1` and
    `(1, I, -I, 1)` at `e2`. Then all four coefficients vanish. -/
theorem quad_extractA (r1 c1 r2 c2 : I32) (a b a' b' : Fin 88)
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b')
    (hba' : b ≠ a') (hbb' : b ≠ b') (ha'b' : a' ≠ b')
    (hv1 : dir88Mat a r1 c1 = 1) (hv2 : dir88Mat b r1 c1 = Complex.I)
    (hv3 : dir88Mat a' r1 c1 = Complex.I) (hv4 : dir88Mat b' r1 c1 = -1)
    (hw1 : dir88Mat a r2 c2 = 1) (hw2 : dir88Mat b r2 c2 = Complex.I)
    (hw3 : dir88Mat a' r2 c2 = -Complex.I) (hw4 : dir88Mat b' r2 c2 = 1)
    (hvan1 : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b'
      → dir88Mat i r1 c1 = 0)
    (hvan2 : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b'
      → dir88Mat i r2 c2 = 0)
    (g : Fin 88 → ℝ) (hg : ∑ i, g i • dir88Mat i = 0) :
    g a = 0 ∧ g b = 0 ∧ g a' = 0 ∧ g b' = 0 := by
  have hP1 : ∑ i : Fin 88, (g i • dir88Mat i) r1 c1 = 0 := by
    have h := congrFun (congrFun hg r1) c1
    rwa [Matrix.sum_apply] at h
  have hP2 : ∑ i : Fin 88, (g i • dir88Mat i) r2 c2 = 0 := by
    have h := congrFun (congrFun hg r2) c2
    rwa [Matrix.sum_apply] at h
  have hcol1 : ∑ i : Fin 88, (g i • dir88Mat i) r1 c1
      = (g a • dir88Mat a) r1 c1 + (g b • dir88Mat b) r1 c1
        + (g a' • dir88Mat a') r1 c1 + (g b' • dir88Mat b') r1 c1 :=
    sum_collapse4_88 _ hab haa' hab' hba' hbb' ha'b'
      (fun i h1 h2 h3 h4 => by
        rw [Matrix.smul_apply, hvan1 i h1 h2 h3 h4, smul_zero])
  have hcol2 : ∑ i : Fin 88, (g i • dir88Mat i) r2 c2
      = (g a • dir88Mat a) r2 c2 + (g b • dir88Mat b) r2 c2
        + (g a' • dir88Mat a') r2 c2 + (g b' • dir88Mat b') r2 c2 :=
    sum_collapse4_88 _ hab haa' hab' hba' hbb' ha'b'
      (fun i h1 h2 h3 h4 => by
        rw [Matrix.smul_apply, hvan2 i h1 h2 h3 h4, smul_zero])
  rw [hcol1] at hP1
  rw [hcol2] at hP2
  have e : ∀ i : Fin 88, ∀ (r c : I32), (g i • dir88Mat i) r c
      = (g i) • (dir88Mat i r c) := fun i r c => Matrix.smul_apply _ _ _ _
  rw [e a, e b, e a', e b', hv1, hv2, hv3, hv4] at hP1
  rw [e a, e b, e a', e b', hw1, hw2, hw3, hw4] at hP2
  have s1 : ∀ x : ℝ, x • (1 : ℂ) = ((x : ℝ) : ℂ) := fun x => by simp
  have s2 : ∀ x : ℝ, x • Complex.I = ((x : ℝ) : ℂ) * Complex.I :=
    fun x => by simp
  have s3 : ∀ x : ℝ, x • (-1 : ℂ) = - ((x : ℝ) : ℂ) := fun x => by simp
  have s4 : ∀ x : ℝ, x • (-Complex.I) = - (((x : ℝ) : ℂ) * Complex.I) :=
    fun x => by simp
  rw [s1, s2, s2, s3] at hP1
  rw [s1, s2, s4, s1] at hP2
  have hE1 : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I
      + ((g a' : ℝ) : ℂ) * Complex.I - ((g b' : ℝ) : ℂ) = 0 := by
    linear_combination hP1
  have hE2 : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I
      - ((g a' : ℝ) : ℂ) * Complex.I + ((g b' : ℝ) : ℂ) = 0 := by
    linear_combination hP2
  have hre1 := congrArg Complex.re hE1
  have him1 := congrArg Complex.im hE1
  have hre2 := congrArg Complex.re hE2
  have him2 := congrArg Complex.im hE2
  simp at hre1 him1 hre2 him2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Quad extraction, pattern B (E-slot groups):** entries
    `e+, e-` see only the four indices `a, b` (hermitian pair) and
    `a', b'` (anti pair), with values `(1, I, 1, I)` at `e+` and
    `(1, I, -1, -I)` at `e-`. Then all four coefficients vanish. -/
theorem quad_extractB (r1 c1 r2 c2 : I32) (a b a' b' : Fin 88)
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b')
    (hba' : b ≠ a') (hbb' : b ≠ b') (ha'b' : a' ≠ b')
    (hv1 : dir88Mat a r1 c1 = 1) (hv2 : dir88Mat b r1 c1 = Complex.I)
    (hv3 : dir88Mat a' r1 c1 = 1) (hv4 : dir88Mat b' r1 c1 = Complex.I)
    (hw1 : dir88Mat a r2 c2 = 1) (hw2 : dir88Mat b r2 c2 = Complex.I)
    (hw3 : dir88Mat a' r2 c2 = -1) (hw4 : dir88Mat b' r2 c2 = -Complex.I)
    (hvan1 : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b'
      → dir88Mat i r1 c1 = 0)
    (hvan2 : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b'
      → dir88Mat i r2 c2 = 0)
    (g : Fin 88 → ℝ) (hg : ∑ i, g i • dir88Mat i = 0) :
    g a = 0 ∧ g b = 0 ∧ g a' = 0 ∧ g b' = 0 := by
  have hP1 : ∑ i : Fin 88, (g i • dir88Mat i) r1 c1 = 0 := by
    have h := congrFun (congrFun hg r1) c1
    rwa [Matrix.sum_apply] at h
  have hP2 : ∑ i : Fin 88, (g i • dir88Mat i) r2 c2 = 0 := by
    have h := congrFun (congrFun hg r2) c2
    rwa [Matrix.sum_apply] at h
  have hcol1 : ∑ i : Fin 88, (g i • dir88Mat i) r1 c1
      = (g a • dir88Mat a) r1 c1 + (g b • dir88Mat b) r1 c1
        + (g a' • dir88Mat a') r1 c1 + (g b' • dir88Mat b') r1 c1 :=
    sum_collapse4_88 _ hab haa' hab' hba' hbb' ha'b'
      (fun i h1 h2 h3 h4 => by
        rw [Matrix.smul_apply, hvan1 i h1 h2 h3 h4, smul_zero])
  have hcol2 : ∑ i : Fin 88, (g i • dir88Mat i) r2 c2
      = (g a • dir88Mat a) r2 c2 + (g b • dir88Mat b) r2 c2
        + (g a' • dir88Mat a') r2 c2 + (g b' • dir88Mat b') r2 c2 :=
    sum_collapse4_88 _ hab haa' hab' hba' hbb' ha'b'
      (fun i h1 h2 h3 h4 => by
        rw [Matrix.smul_apply, hvan2 i h1 h2 h3 h4, smul_zero])
  rw [hcol1] at hP1
  rw [hcol2] at hP2
  have e : ∀ i : Fin 88, ∀ (r c : I32), (g i • dir88Mat i) r c
      = (g i) • (dir88Mat i r c) := fun i r c => Matrix.smul_apply _ _ _ _
  rw [e a, e b, e a', e b', hv1, hv2, hv3, hv4] at hP1
  rw [e a, e b, e a', e b', hw1, hw2, hw3, hw4] at hP2
  have s1 : ∀ x : ℝ, x • (1 : ℂ) = ((x : ℝ) : ℂ) := fun x => by simp
  have s2 : ∀ x : ℝ, x • Complex.I = ((x : ℝ) : ℂ) * Complex.I :=
    fun x => by simp
  have s3 : ∀ x : ℝ, x • (-1 : ℂ) = - ((x : ℝ) : ℂ) := fun x => by simp
  have s4 : ∀ x : ℝ, x • (-Complex.I) = - (((x : ℝ) : ℂ) * Complex.I) :=
    fun x => by simp
  rw [s1, s2, s1, s2] at hP1
  rw [s1, s2, s3, s4] at hP2
  have hE1 : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I
      + ((g a' : ℝ) : ℂ) + ((g b' : ℝ) : ℂ) * Complex.I = 0 := by
    linear_combination hP1
  have hE2 : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I
      - ((g a' : ℝ) : ℂ) - ((g b' : ℝ) : ℂ) * Complex.I = 0 := by
    linear_combination hP2
  have hre1 := congrArg Complex.re hE1
  have him1 := congrArg Complex.im hE1
  have hre2 := congrArg Complex.re hE2
  have him2 := congrArg Complex.im hE2
  simp at hre1 him1 hre2 him2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Quad extraction, pattern C (the `(8, 25)` group):** entries
    `(8, 25)` and `(25, 8)` see only the four indices `a, b`
    (the NuREbarR pair) and `a', b'` (the supplement `(8, 9)`
    pair), with values `(1, I, 1, -I)` at `(8, 25)` and
    `(1, -I, -1, -I)` at `(25, 8)`. All four coefficients vanish. -/
theorem quad_extractC (a b a' b' : Fin 88)
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b')
    (hba' : b ≠ a') (hbb' : b ≠ b') (ha'b' : a' ≠ b')
    (hv1 : dir88Mat a 8 25 = 1) (hv2 : dir88Mat b 8 25 = Complex.I)
    (hv3 : dir88Mat a' 8 25 = 1) (hv4 : dir88Mat b' 8 25 = -Complex.I)
    (hw1 : dir88Mat a 25 8 = 1) (hw2 : dir88Mat b 25 8 = -Complex.I)
    (hw3 : dir88Mat a' 25 8 = -1) (hw4 : dir88Mat b' 25 8 = -Complex.I)
    (hvan1 : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b'
      → dir88Mat i 8 25 = 0)
    (hvan2 : ∀ i : Fin 88, i ≠ a → i ≠ b → i ≠ a' → i ≠ b'
      → dir88Mat i 25 8 = 0)
    (g : Fin 88 → ℝ) (hg : ∑ i, g i • dir88Mat i = 0) :
    g a = 0 ∧ g b = 0 ∧ g a' = 0 ∧ g b' = 0 := by
  have hP1 : ∑ i : Fin 88, (g i • dir88Mat i) 8 25 = 0 := by
    have h := congrFun (congrFun hg 8) 25
    rwa [Matrix.sum_apply] at h
  have hP2 : ∑ i : Fin 88, (g i • dir88Mat i) 25 8 = 0 := by
    have h := congrFun (congrFun hg 25) 8
    rwa [Matrix.sum_apply] at h
  have hcol1 : ∑ i : Fin 88, (g i • dir88Mat i) 8 25
      = (g a • dir88Mat a) 8 25 + (g b • dir88Mat b) 8 25
        + (g a' • dir88Mat a') 8 25 + (g b' • dir88Mat b') 8 25 :=
    sum_collapse4_88 _ hab haa' hab' hba' hbb' ha'b'
      (fun i h1 h2 h3 h4 => by
        rw [Matrix.smul_apply, hvan1 i h1 h2 h3 h4, smul_zero])
  have hcol2 : ∑ i : Fin 88, (g i • dir88Mat i) 25 8
      = (g a • dir88Mat a) 25 8 + (g b • dir88Mat b) 25 8
        + (g a' • dir88Mat a') 25 8 + (g b' • dir88Mat b') 25 8 :=
    sum_collapse4_88 _ hab haa' hab' hba' hbb' ha'b'
      (fun i h1 h2 h3 h4 => by
        rw [Matrix.smul_apply, hvan2 i h1 h2 h3 h4, smul_zero])
  rw [hcol1] at hP1
  rw [hcol2] at hP2
  have e : ∀ i : Fin 88, ∀ (r c : I32), (g i • dir88Mat i) r c
      = (g i) • (dir88Mat i r c) := fun i r c => Matrix.smul_apply _ _ _ _
  rw [e a, e b, e a', e b', hv1, hv2, hv3, hv4] at hP1
  rw [e a, e b, e a', e b', hw1, hw2, hw3, hw4] at hP2
  have s1 : ∀ x : ℝ, x • (1 : ℂ) = ((x : ℝ) : ℂ) := fun x => by simp
  have s2 : ∀ x : ℝ, x • Complex.I = ((x : ℝ) : ℂ) * Complex.I :=
    fun x => by simp
  have s3 : ∀ x : ℝ, x • (-1 : ℂ) = - ((x : ℝ) : ℂ) := fun x => by simp
  have s4 : ∀ x : ℝ, x • (-Complex.I) = - (((x : ℝ) : ℂ) * Complex.I) :=
    fun x => by simp
  rw [s1, s2, s1, s4] at hP1
  rw [s1, s4, s3, s4] at hP2
  have hE1 : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I
      + ((g a' : ℝ) : ℂ) - ((g b' : ℝ) : ℂ) * Complex.I = 0 := by
    linear_combination hP1
  have hE2 : ((g a : ℝ) : ℂ) - ((g b : ℝ) : ℂ) * Complex.I
      - ((g a' : ℝ) : ℂ) - ((g b' : ℝ) : ℂ) * Complex.I = 0 := by
    linear_combination hP2
  have hre1 := congrArg Complex.re hE1
  have him1 := congrArg Complex.im hE1
  have hre2 := congrArg Complex.re hE2
  have him2 := congrArg Complex.im hE2
  simp at hre1 him1 hre2 him2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## 5. Segment transport for `dir88Mat` -/

/-- `dir88Mat` at an index below 18 is the SM-like block. -/
theorem dir88Mat_of_lt18 {i : Fin 88} (h : i.val < 18) :
    dir88Mat i = (pairDirSM18 ⟨i.val, h⟩ : Matrix I32 I32 ℂ) := by
  have h1 := dir88_SM (⟨i.val, h⟩ : Fin 18)
  have h2 : (⟨(⟨i.val, h⟩ : Fin 18).val,
      by have h3 := i.isLt; omega⟩ : Fin 88) = i := Fin.ext rfl
  rw [h2] at h1
  rw [dir88Mat, h1]

/-- `dir88Mat` at an index in `[18, 34)` is the flipped block. -/
theorem dir88Mat_of_flip {i : Fin 88} (h1 : 18 ≤ i.val) (h2 : i.val < 34) :
    dir88Mat i
      = (pairDirFlip16 ⟨i.val - 18, by omega⟩ : Matrix I32 I32 ℂ) := by
  have h := dir88_flip (⟨i.val - 18, by omega⟩ : Fin 16)
  have e : (⟨(⟨i.val - 18, by omega⟩ : Fin 16).val + 18,
      by show (i.val - 18) + 18 < 88; have h3 := i.isLt; omega⟩ : Fin 88)
      = i := Fin.ext (by show (i.val - 18) + 18 = i.val; omega)
  rw [e] at h
  rw [dir88Mat, h]

/-- `dir88Mat` at an index in `[34, 80)` is the exotic-distinct
    block. -/
theorem dir88Mat_of_exotic {i : Fin 88} (h1 : 34 ≤ i.val) (h2 : i.val < 80) :
    dir88Mat i = (pairDirExoticDistinct46 ⟨i.val - 34, by omega⟩
      : Matrix I32 I32 ℂ) := by
  have h := dir88_exotic (⟨i.val - 34, by omega⟩ : Fin 46)
  have e : (⟨(⟨i.val - 34, by omega⟩ : Fin 46).val + 34,
      by show (i.val - 34) + 34 < 88; have h3 := i.isLt; omega⟩ : Fin 88)
      = i := Fin.ext (by show (i.val - 34) + 34 = i.val; omega)
  rw [e] at h
  rw [dir88Mat, h]

/-- `dir88Mat` at an index in `[80, 88)` is the supplement block. -/
theorem dir88Mat_of_supp {i : Fin 88} (h1 : 80 ≤ i.val) :
    dir88Mat i
      = (pairDirExoticSupp8 ⟨i.val - 80, by have h2 := i.isLt; omega⟩
        : Matrix I32 I32 ℂ) := by
  have h := dir88_supp (⟨i.val - 80, by have h2 := i.isLt; omega⟩ : Fin 8)
  have e : (⟨(⟨i.val - 80, by have h2 := i.isLt; omega⟩ : Fin 8).val + 80,
      by show (i.val - 80) + 80 < 88; have h3 := i.isLt; omega⟩ : Fin 88)
      = i := Fin.ext (by show (i.val - 80) + 80 = i.val; omega)
  rw [e] at h
  rw [dir88Mat, h]

/-- The exotic-distinct family at a seg-4 index is the `dirs22`
    block of index `k + 18`. -/
theorem distinct46_of_lt4 {k : Fin 46} (h : k.val < 4) :
    (pairDirExoticDistinct46 k : Matrix I32 I32 ℂ)
      = dirs22 ⟨k.val + 18, by have h2 := k.isLt; omega⟩ := by
  have h1 := pairDirExoticDistinct46_seg4 (⟨k.val, h⟩ : Fin 4)
  have e : (⟨(⟨k.val, h⟩ : Fin 4).val,
      by have h3 := k.isLt; omega⟩ : Fin 46) = k := Fin.ext rfl
  rw [e] at h1
  rw [h1]
  exact exDistinctSeg4_apply ⟨k.val, h⟩

/-- The exotic-distinct family at a hermitian index is the
    hermitian E-slot pattern. -/
theorem distinct46_of_herm {k : Fin 46} (h1 : 4 ≤ k.val) (h2 : k.val < 28) :
    (pairDirExoticDistinct46 k : Matrix I32 I32 ℂ)
      = exHermMat (exMajU ((k.val - 4) / 2)) (exMajV ((k.val - 4) / 2))
        (exPhase (k.val - 4)) := by
  have h := pairDirExoticDistinct46_herm (⟨k.val - 4, by omega⟩ : Fin 24)
  have e : (⟨(⟨k.val - 4, by omega⟩ : Fin 24).val + 4,
      by show (k.val - 4) + 4 < 46; have h3 := k.isLt; omega⟩ : Fin 46)
      = k := Fin.ext (by show (k.val - 4) + 4 = k.val; omega)
  rw [e] at h
  rw [h]
  rfl

/-- The exotic-distinct family at an anti index is the anti E-slot
    pattern. -/
theorem distinct46_of_anti {k : Fin 46} (h1 : 28 ≤ k.val) :
    (pairDirExoticDistinct46 k : Matrix I32 I32 ℂ)
      = exAntiMat (exMajU ((k.val - 28) / 2)) (exMajV ((k.val - 28) / 2))
        (exPhase (k.val - 28)) := by
  have h := pairDirExoticDistinct46_anti (⟨k.val - 28, by omega⟩ : Fin 18)
  have e : (⟨(⟨k.val - 28, by omega⟩ : Fin 18).val + 28,
      by show (k.val - 28) + 28 < 46; have h3 := k.isLt; omega⟩ : Fin 46)
      = k := Fin.ext (by show (k.val - 28) + 28 = k.val; omega)
  rw [e] at h
  rw [h]
  rfl

/-! ## 6. Segment entry evaluation -/

/-- Inequality of `Fin 22` indices from inequality of values. -/
theorem fin22_ne_of_val_ne {m : Fin 22} {n : Nat} (hn : n < 22)
    (h : m.val ≠ n) : m ≠ ⟨n, hn⟩ :=
  fun hc => h (congrArg Fin.val hc)

/-- The antiparticle sign is `1` below index 24. -/
theorem aRSgn_of_val_lt {i : I32} (h : i.val < 24) : aRSgn i = 1 := by
  rw [aRSgn_apply, if_pos h]

/-- The antiparticle sign is `-1` from index 24 on. -/
theorem aRSgn_of_val_ge {i : I32} (h : 24 ≤ i.val) : aRSgn i = -1 := by
  rw [aRSgn_apply, if_neg (by omega)]

/-- `dirs22` at the partner entry `(24, 16)` equals its value at
    the SM pivot `(0, 8)` (J-compatibility transport). -/
theorem dirs22_apply_24_16 (m : Fin 22) :
    dirs22 m 24 16 = dirs22 m 0 8 := by
  rw [show (24 : I32) = partner 8 by decide,
    show (16 : I32) = partner 0 by decide]
  exact dirs22_partner_entry m 0 8

/-- `dirs22` at the partner entry `(25, 17)` equals its value at
    the SM pivot `(1, 9)`. -/
theorem dirs22_apply_25_17 (m : Fin 22) :
    dirs22 m 25 17 = dirs22 m 1 9 := by
  rw [show (25 : I32) = partner 9 by decide,
    show (17 : I32) = partner 1 by decide]
  exact dirs22_partner_entry m 1 9

/-- `dirs22` at the partner entry `(26, 18)` equals its value at
    the SM pivot `(2, 10)`. -/
theorem dirs22_apply_26_18 (m : Fin 22) :
    dirs22 m 26 18 = dirs22 m 2 10 := by
  rw [show (26 : I32) = partner 10 by decide,
    show (18 : I32) = partner 2 by decide]
  exact dirs22_partner_entry m 2 10

/-- `dirs22` at the partner entry `(27, 19)` equals its value at
    the SM pivot `(3, 11)`. -/
theorem dirs22_apply_27_19 (m : Fin 22) :
    dirs22 m 27 19 = dirs22 m 3 11 := by
  rw [show (27 : I32) = partner 11 by decide,
    show (19 : I32) = partner 3 by decide]
  exact dirs22_partner_entry m 3 11

/-- `dirs22` at the partner entry `(25, 16)` equals its value at
    the flipped pivot `(0, 9)`. -/
theorem dirs22_apply_25_16 (m : Fin 22) :
    dirs22 m 25 16 = dirs22 m 0 9 := by
  rw [show (25 : I32) = partner 9 by decide,
    show (16 : I32) = partner 0 by decide]
  exact dirs22_partner_entry m 0 9

/-- `dirs22` at the partner entry `(24, 17)` equals its value at
    the flipped pivot `(1, 8)`. -/
theorem dirs22_apply_24_17 (m : Fin 22) :
    dirs22 m 24 17 = dirs22 m 1 8 := by
  rw [show (24 : I32) = partner 8 by decide,
    show (17 : I32) = partner 1 by decide]
  exact dirs22_partner_entry m 1 8

/-- `dirs22` at the partner entry `(27, 18)` equals its value at
    the flipped pivot `(2, 11)`. -/
theorem dirs22_apply_27_18 (m : Fin 22) :
    dirs22 m 27 18 = dirs22 m 2 11 := by
  rw [show (27 : I32) = partner 11 by decide,
    show (18 : I32) = partner 2 by decide]
  exact dirs22_partner_entry m 2 11

/-- `dirs22` at the partner entry `(26, 19)` equals its value at
    the flipped pivot `(3, 10)`. -/
theorem dirs22_apply_26_19 (m : Fin 22) :
    dirs22 m 26 19 = dirs22 m 3 10 := by
  rw [show (26 : I32) = partner 10 by decide,
    show (19 : I32) = partner 3 by decide]
  exact dirs22_partner_entry m 3 10

/-- `dirs22` at an E-slot minus entry `(v + 16, u)` equals its
    value at the plus entry `(u + 16, v)` (J-compatibility
    transport). -/
theorem dirs22_apply_em (m : Fin 22) {u v : Nat} (hu : u < 16) (hv : v < 16) :
    dirs22 m ⟨v + 16, by omega⟩ ⟨u, by omega⟩
      = dirs22 m ⟨u + 16, by omega⟩ ⟨v, by omega⟩ := by
  have h := dirs22_partner_entry m ⟨u + 16, by omega⟩ ⟨v, by omega⟩
  have e1 : partner (⟨v, by omega⟩ : I32) = ⟨v + 16, by omega⟩ := by
    apply Fin.ext
    rw [partner_val_eq]
    show (if v < 16 then v + 16 else v - 16) = v + 16
    rw [if_pos hv]
  have e2 : partner (⟨u + 16, by omega⟩ : I32) = ⟨u, by omega⟩ := by
    apply Fin.ext
    rw [partner_val_eq]
    show (if u + 16 < 16 then (u + 16) + 16 else (u + 16) - 16) = u
    rw [if_neg (by omega)]
    omega
  rw [e1, e2] at h
  exact h

/-- Entry evaluation of the SM-like family: hermitian indices read
    `dirs22` directly; anti indices read `Complex.I` times the
    sign-twisted `dirs22` entry. -/
theorem sm18_apply (k : Fin 18) (r c : I32) :
    (pairDirSM18 k : Matrix I32 I32 ℂ) r c
      = if k.val < 10 then dirs22 ⟨k.val, by have h := k.isLt; omega⟩ r c
        else Complex.I * (aRSgn r
          * (dirs22 ⟨k.val - 10, by have h := k.isLt; omega⟩ r c
            * aRSgn c)) := by
  by_cases h : k.val < 10
  · rw [if_pos h]
    have ek : k = Fin.castAdd 8 (⟨k.val, h⟩ : Fin 10) := Fin.ext rfl
    have e2 : pairDirSM18 k = pairDirSM ⟨k.val, h⟩ := by
      conv_lhs => rw [ek]
      rw [pairDirSM18, Fin.append_left]
    rw [e2]
    show (pairDirSM ⟨k.val, h⟩ : Matrix I32 I32 ℂ) r c = _
    unfold pairDirSM
    rw [pairDir22_apply]
  · rw [if_neg h]
    have ek : k = Fin.natAdd 10 (⟨k.val - 10, by omega⟩ : Fin 8) := by
      apply Fin.ext
      show k.val = (Fin.natAdd 10 (⟨k.val - 10, by omega⟩ : Fin 8)).val
      rw [Fin.val_natAdd]
      show k.val = 10 + (k.val - 10)
      omega
    have e2 : pairDirSM18 k = antiSMDir ⟨k.val - 10, by omega⟩ := by
      conv_lhs => rw [ek]
      rw [pairDirSM18, Fin.append_right]
    rw [e2, antiSMDir_apply, antiSMMat_apply]

/-- Entry evaluation of the flipped family: hermitian indices read
    `dirs22` at index `k + 10`; anti indices read `Complex.I` times
    the sign-twisted `dirs22` entry at index `k - 8 + 10`. -/
theorem flip16_apply (k : Fin 16) (r c : I32) :
    (pairDirFlip16 k : Matrix I32 I32 ℂ) r c
      = if h : k.val < 8 then dirs22 ⟨k.val + 10, by omega⟩ r c
        else Complex.I * (aRSgn r
          * (dirs22 ⟨k.val - 8 + 10, by have h2 := k.isLt; omega⟩ r c
            * aRSgn c)) := by
  by_cases h : k.val < 8
  · rw [dif_pos h]
    have ek : k = Fin.castAdd 8 (⟨k.val, h⟩ : Fin 8) := Fin.ext rfl
    have e2 : pairDirFlip16 k = flipHermDir ⟨k.val, h⟩ := by
      conv_lhs => rw [ek]
      rw [pairDirFlip16, Fin.append_left]
    rw [e2]
    show (flipHermDir ⟨k.val, h⟩ : Matrix I32 I32 ℂ) r c = _
    unfold flipHermDir
    rw [pairDir22_apply]
  · rw [dif_neg h]
    have ek : k = Fin.natAdd 8 (⟨k.val - 8, by omega⟩ : Fin 8) := by
      apply Fin.ext
      show k.val = (Fin.natAdd 8 (⟨k.val - 8, by omega⟩ : Fin 8)).val
      rw [Fin.val_natAdd]
      show k.val = 8 + (k.val - 8)
      omega
    have e2 : pairDirFlip16 k = antiFlipDir ⟨k.val - 8, by omega⟩ := by
      conv_lhs => rw [ek]
      rw [pairDirFlip16, Fin.append_right]
    rw [e2, antiFlipDir_apply, antiFlipMat_apply]

/-! ## 7. E-slot pattern pivots and vanishing -/

/-- Folded coordinate of a high index `a + 16` is `a`. -/
theorem acoord_add16 (a : Fin 16) :
    acoord ⟨a.val + 16, by have h := a.isLt; omega⟩ = a := by
  apply Fin.ext
  rw [acoord_val]
  show (a.val + 16) % 16 = a.val
  omega

/-- Folded coordinate of the index `a` (as a 32-index) is `a`. -/
theorem acoord_mk (a : Fin 16) :
    acoord ⟨a.val, by have h := a.isLt; omega⟩ = a := by
  apply Fin.ext
  rw [acoord_val]
  show a.val % 16 = a.val
  omega

/-- A single-coordinate pair pattern at its low cross entry
    `(u, v + 16)` (both folded coordinates `>= 8`): the value is
    `star z` (the `(-, +)` branch). -/
theorem exPairMat_apply_lo {u v : Fin 16} (hu : 8 ≤ u.val) (hv : 8 ≤ v.val)
    (z : ℂ) :
    exPairMat u v z ⟨u.val, by have h := u.isLt; omega⟩
        ⟨v.val + 16, by have h := v.isLt; omega⟩ = star z := by
  have hgi : gSign (⟨u.val, by have h := u.isLt; omega⟩ : I32) = -1 :=
    gSign_eq_neg_one_of_val ⟨hu, by show u.val < 24; omega⟩
  have hgj : gSign (⟨v.val + 16, by have h := v.isLt; omega⟩ : I32) = 1 :=
    gSign_eq_one_of_val (Or.inr (by show 24 ≤ v.val + 16; omega))
  have hai : acoord (⟨u.val, by have h := u.isLt; omega⟩ : I32) = u := by
    apply Fin.ext
    rw [acoord_val]
    show u.val % 16 = u.val
    omega
  have haj : acoord (⟨v.val + 16, by have h := v.isLt; omega⟩ : I32) = v := by
    apply Fin.ext
    rw [acoord_val]
    show (v.val + 16) % 16 = v.val
    omega
  rw [exPairMat_apply, if_neg (by rw [hgi]; exact neg_one_ne_one_complex),
    if_pos hgj, if_pos ⟨hai, haj⟩]

/-- A single-coordinate pair pattern at a foreign low cross entry
    vanishes. -/
theorem exPairMat_apply_lo_of_ne {u v u' v' : Fin 16} (hu : 8 ≤ u.val)
    (hv : 8 ≤ v.val) (h : ¬ (u = u' ∧ v = v')) (z : ℂ) :
    exPairMat u' v' z ⟨u.val, by have h := u.isLt; omega⟩
        ⟨v.val + 16, by have h := v.isLt; omega⟩ = 0 := by
  apply exPairMat_eq_zero_of z
  have hai : acoord (⟨u.val, by have h := u.isLt; omega⟩ : I32) = u := by
    apply Fin.ext
    rw [acoord_val]
    show u.val % 16 = u.val
    omega
  have haj : acoord (⟨v.val + 16, by have h := v.isLt; omega⟩ : I32) = v := by
    apply Fin.ext
    rw [acoord_val]
    show (v.val + 16) % 16 = v.val
    omega
  rw [hai, haj]
  exact h

/-- The anti `(8, 9)` pattern at `(8, 25)`: value `star z`. -/
theorem exAntiMat_apply_8_25 (z : ℂ) :
    exAntiMat (8 : Fin 16) (9 : Fin 16) z (8 : I32) (25 : I32)
      = star z := by
  unfold exAntiMat
  rw [Matrix.sub_apply]
  have h1 : exPairMat (8 : Fin 16) (9 : Fin 16) z (8 : I32) (25 : I32)
      = star z :=
    exPairMat_apply_lo (by decide) (by decide) z
  have h2 : exPairMat (9 : Fin 16) (8 : Fin 16) z (8 : I32) (25 : I32)
      = 0 :=
    exPairMat_apply_lo_of_ne (u := (8 : Fin 16)) (v := (9 : Fin 16))
      (by decide) (by decide) (by decide) z
  rw [h1, h2, sub_zero]

/-- The anti `(8, 9)` pattern at `(25, 8)`: value `-z`. -/
theorem exAntiMat_apply_25_8 (z : ℂ) :
    exAntiMat (8 : Fin 16) (9 : Fin 16) z (25 : I32) (8 : I32)
      = -z := by
  unfold exAntiMat
  rw [Matrix.sub_apply]
  have h1 : exPairMat (8 : Fin 16) (9 : Fin 16) z (25 : I32) (8 : I32)
      = 0 :=
    exPairMat_apply_hi_of_ne (a := (9 : Fin 16)) (b := (8 : Fin 16))
      (by decide) (by decide) (by decide) z
  have h2 : exPairMat (9 : Fin 16) (8 : Fin 16) z (25 : I32) (8 : I32)
      = z :=
    exPairMat_apply_hi (a := (9 : Fin 16)) (b := (8 : Fin 16))
      (by decide) (by decide) z
  rw [h1, h2, zero_sub]

/-- A supplement direction with folded pair `(8, 9)` at `(8, 25)`:
    value `star (exPhase n)`. -/
theorem supp8_apply_8_25 {n : Fin 8} (hU : suppU (n.val / 2) = (8 : Fin 16))
    (hV : suppV (n.val / 2) = (9 : Fin 16)) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) 8 25
      = star (exPhase n.val) := by
  rw [pairDirExoticSupp8_apply, hU, hV]
  exact exAntiMat_apply_8_25 _

/-- A supplement direction with folded pair `(8, 9)` at `(25, 8)`:
    value `-(exPhase n)`. -/
theorem supp8_apply_25_8 {n : Fin 8} (hU : suppU (n.val / 2) = (8 : Fin 16))
    (hV : suppV (n.val / 2) = (9 : Fin 16)) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) 25 8
      = - (exPhase n.val) := by
  rw [pairDirExoticSupp8_apply, hU, hV]
  exact exAntiMat_apply_25_8 _

/-- A supplement direction whose folded pair is not `(8, 9)`
    vanishes at `(8, 25)`. -/
theorem supp8_eq_zero_8_25 {n : Fin 8}
    (h : ¬ (suppU (n.val / 2) = (8 : Fin 16)
      ∧ suppV (n.val / 2) = (9 : Fin 16))) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) 8 25 = 0 := by
  rw [pairDirExoticSupp8_apply]
  have ha8 : acoord (8 : I32) = (8 : Fin 16) := by decide
  have ha25 : acoord (25 : I32) = (9 : Fin 16) := by decide
  apply exAntiMat_eq_zero_of_acoor
  · intro hc
    rw [ha8, ha25] at hc
    exact h ⟨hc.1.symm, hc.2.symm⟩
  · intro hc
    rw [ha8, ha25] at hc
    have hUV := suppUV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    rcases hUV with ⟨hu, hv⟩ | ⟨hu, hv1, hv2⟩ <;> omega

/-- A supplement direction whose folded pair is not `(8, 9)`
    vanishes at `(25, 8)`. -/
theorem supp8_eq_zero_25_8 {n : Fin 8}
    (h : ¬ (suppU (n.val / 2) = (8 : Fin 16)
      ∧ suppV (n.val / 2) = (9 : Fin 16))) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) 25 8 = 0 := by
  rw [pairDirExoticSupp8_apply]
  have ha8 : acoord (8 : I32) = (8 : Fin 16) := by decide
  have ha25 : acoord (25 : I32) = (9 : Fin 16) := by decide
  apply exAntiMat_eq_zero_of_acoor
  · intro hc
    rw [ha25, ha8] at hc
    have hUV := suppUV_spec (n.val / 2)
    have e1 := congrArg Fin.val hc.1
    have e2 := congrArg Fin.val hc.2
    rcases hUV with ⟨hu, hv⟩ | ⟨hu, hv1, hv2⟩ <;> omega
  · intro hc
    rw [ha25, ha8] at hc
    exact h ⟨hc.2.symm, hc.1.symm⟩

/-- Pivot values of a hermitian E-slot direction at its pair's two
    cross entries: `exPhase n` at both. -/
theorem exHermDir_pivot {n : Fin 24} {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (hU : exMajU (n.val / 2) = u) (hV : exMajV (n.val / 2) = v) :
    (exHermDir n : Matrix I32 I32 ℂ)
        ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = exPhase n.val ∧
    (exHermDir n : Matrix I32 I32 ℂ)
        ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = exPhase n.val := by
  show exHermMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = exPhase n.val ∧
    exHermMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = exPhase n.val
  rw [hU, hV]
  exact exHermMat_apply_hi hu hv _

/-- Pivot values of an anti E-slot direction at its pair's two
    cross entries: `exPhase n` at the plus entry, `-(exPhase n)`
    at the minus entry. -/
theorem exAntiDir_pivot {n : Fin 18} {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (hU : exMajU (n.val / 2) = u) (hV : exMajV (n.val / 2) = v) :
    (exAntiDir n : Matrix I32 I32 ℂ)
        ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = exPhase n.val ∧
    (exAntiDir n : Matrix I32 I32 ℂ)
        ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = - (exPhase n.val) := by
  show exAntiMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = exPhase n.val ∧
    exAntiMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = - (exPhase n.val)
  rw [hU, hV]
  exact exAntiMat_apply_hi hu hv _

/-- Pivot values of a supplement direction at its pair's two cross
    entries (pairs `(9, 13)`, `(9, 14)`, `(9, 15)`): `exPhase n`
    at the plus entry, `-(exPhase n)` at the minus entry. -/
theorem supp8_pivot {n : Fin 8} {u v : Fin 16}
    (hu : u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (hU : suppU (n.val / 2) = u) (hV : suppV (n.val / 2) = v) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ)
        ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = exPhase n.val ∧
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ)
        ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = - (exPhase n.val) := by
  rw [pairDirExoticSupp8_apply, hU, hV]
  exact exAntiMat_apply_hi (Or.inr hu) hv _

/-- A hermitian E-slot direction whose folded pair differs from
    `(u, v)` vanishes at `(u, v)`'s two cross entries. -/
theorem exHermDir_eq_zero_of_ne {n : Fin 24} {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (h : ¬ (exMajU (n.val / 2) = u ∧ exMajV (n.val / 2) = v)) :
    (exHermDir n : Matrix I32 I32 ℂ)
        ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = 0 ∧
    (exHermDir n : Matrix I32 I32 ℂ)
        ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = 0 := by
  have hU := exMajU_spec (n.val / 2)
  refine ⟨?_, ?_⟩
  · show exHermMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) _ _ = 0
    apply exHermMat_eq_zero_of_acoor
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      exact h ⟨hc.1.symm, hc.2.symm⟩
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      have e1 := congrArg Fin.val hc.1
      omega
  · show exHermMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) _ _ = 0
    apply exHermMat_eq_zero_of_acoor
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      have e1 := congrArg Fin.val hc.1
      omega
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      exact h ⟨hc.2.symm, hc.1.symm⟩

/-- An anti E-slot direction whose folded pair differs from
    `(u, v)` vanishes at `(u, v)`'s two cross entries. -/
theorem exAntiDir_eq_zero_of_ne {n : Fin 18} {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (h : ¬ (exMajU (n.val / 2) = u ∧ exMajV (n.val / 2) = v)) :
    (exAntiDir n : Matrix I32 I32 ℂ)
        ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = 0 ∧
    (exAntiDir n : Matrix I32 I32 ℂ)
        ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = 0 := by
  have hU := exMajU_spec (n.val / 2)
  refine ⟨?_, ?_⟩
  · show exAntiMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) _ _ = 0
    apply exAntiMat_eq_zero_of_acoor
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      exact h ⟨hc.1.symm, hc.2.symm⟩
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      have e1 := congrArg Fin.val hc.1
      omega
  · show exAntiMat (exMajU (n.val / 2)) (exMajV (n.val / 2))
      (exPhase n.val) _ _ = 0
    apply exAntiMat_eq_zero_of_acoor
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      have e1 := congrArg Fin.val hc.1
      omega
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      exact h ⟨hc.2.symm, hc.1.symm⟩

/-- A supplement direction whose folded pair differs from `(u, v)`
    vanishes at `(u, v)`'s two cross entries. -/
theorem supp8_eq_zero_of_ne {n : Fin 8} {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (h : ¬ (suppU (n.val / 2) = u ∧ suppV (n.val / 2) = v)) :
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ)
        ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = 0 ∧
    (pairDirExoticSupp8 n : Matrix I32 I32 ℂ)
        ⟨v.val + 16, by have h := v.isLt; omega⟩
        ⟨u.val, by have h := u.isLt; omega⟩ = 0 := by
  have hU := suppU_spec (n.val / 2)
  have hUV := suppUV_spec (n.val / 2)
  refine ⟨?_, ?_⟩
  · rw [pairDirExoticSupp8_apply]
    apply exAntiMat_eq_zero_of_acoor
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      exact h ⟨hc.1.symm, hc.2.symm⟩
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      have e1 := congrArg Fin.val hc.1
      have e2 := congrArg Fin.val hc.2
      rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> omega
  · rw [pairDirExoticSupp8_apply]
    apply exAntiMat_eq_zero_of_acoor
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      have e1 := congrArg Fin.val hc.1
      omega
    · intro hc
      rw [acoord_add16, acoord_mk] at hc
      exact h ⟨hc.2.symm, hc.1.symm⟩

/-! ## 8. Group-proof helpers -/

/-- Value inequality of `Fin 88` indices from an index inequality. -/
theorem fin88_val_ne_of_ne {i : Fin 88} {n : Nat} (hn : n < 88)
    (h : i ≠ ⟨n, hn⟩) : i.val ≠ n :=
  fun hc => h (Fin.ext hc)

/-- Convert a `dirs22` vanishing fact from index inequalities to
    value inequalities. -/
theorem dirs22_hvan_val {r c : I32} {A B : Fin 22}
    (h : ∀ m : Fin 22, m ≠ A → m ≠ B → dirs22 m r c = 0) :
    ∀ m : Fin 22, m.val ≠ A.val → m.val ≠ B.val → dirs22 m r c = 0 :=
  fun m hmA hmB => h m (fin22_ne_of_val_ne A.isLt hmA)
    (fin22_ne_of_val_ne B.isLt hmB)

/-- The E-slot pair index is determined by its folded pair: if
    `exMajU m = u` and `exMajV m = v` for an E-slot pair `(u, v)`,
    then `m` is the pair index of `(u, v)`. -/
theorem exMaj_pair_eq_of {m : Nat} (hm : m < 12) {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (hU : exMajU m = u) (hV : exMajV m = v) :
    m = (if u.val = 8 then v.val - 10 else 6 + (v.val - 10)) := by
  have eU := congrArg Fin.val hU
  have eV := congrArg Fin.val hV
  rw [exMajU_val] at eU
  rw [exMajV_val] at eV
  split_ifs at eU with hm6
  · have hu8 : u.val = 8 := by omega
    rw [if_pos hu8]
    omega
  · have hu9 : ¬ u.val = 8 := by omega
    rw [if_neg hu9]
    omega

/-- The supplement pair index is determined by its folded pair
    (for pairs `(9, v)`, `v` in `13..15`): `m = v - 12`. -/
theorem supp_pair_eq_of {m : Nat} (hm : m ≤ 3) {u v : Fin 16}
    (hu : u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (hU : suppU m = u) (hV : suppV m = v) :
    m = v.val - 12 := by
  have eU := congrArg Fin.val hU
  have eV := congrArg Fin.val hV
  rw [suppU_val] at eU
  rw [suppV_val] at eV
  by_cases h0 : m = 0
  · rw [if_pos h0] at eU
    rw [if_pos h0] at eV
    omega
  · rw [if_neg h0] at eU
    rw [if_neg h0] at eV
    by_cases h1 : m = 1
    · rw [if_pos h1] at eV
      omega
    · rw [if_neg h1] at eV
      by_cases h2 : m = 2
      · rw [if_pos h2] at eV
        omega
      · rw [if_neg h2] at eV
        omega

/-- Vanishing of an SM-like direction from a `dirs22` vanishing
    fact at the same entry, given the four relevant index values
    avoid the active pair. -/
theorem sm18_eq_zero_of_hvan {r c : I32} {A B : Fin 22}
    (h22 : ∀ m : Fin 22, m.val ≠ A.val → m.val ≠ B.val → dirs22 m r c = 0)
    {k : Fin 18} (hkA : k.val < 10 → k.val ≠ A.val)
    (hkB : k.val < 10 → k.val ≠ B.val)
    (hkA' : 10 ≤ k.val → k.val - 10 ≠ A.val)
    (hkB' : 10 ≤ k.val → k.val - 10 ≠ B.val) :
    (pairDirSM18 k : Matrix I32 I32 ℂ) r c = 0 := by
  rw [sm18_apply]
  split_ifs with hk
  · exact h22 _ (hkA hk) (hkB hk)
  · have hz := h22 ⟨k.val - 10, by omega⟩ (hkA' (by omega)) (hkB' (by omega))
    rw [hz]
    simp

/-- Vanishing of a flipped direction from a `dirs22` vanishing
    fact at the same entry, given the four relevant index values
    avoid the active pair. -/
theorem flip16_eq_zero_of_hvan {r c : I32} {A B : Fin 22}
    (h22 : ∀ m : Fin 22, m.val ≠ A.val → m.val ≠ B.val → dirs22 m r c = 0)
    {k : Fin 16} (hkA : k.val < 8 → k.val + 10 ≠ A.val)
    (hkB : k.val < 8 → k.val + 10 ≠ B.val)
    (hkA' : 8 ≤ k.val → k.val - 8 + 10 ≠ A.val)
    (hkB' : 8 ≤ k.val → k.val - 8 + 10 ≠ B.val) :
    (pairDirFlip16 k : Matrix I32 I32 ℂ) r c = 0 := by
  rw [flip16_apply]
  split_ifs with hk
  · exact h22 _ (hkA hk) (hkB hk)
  · have hz := h22 ⟨k.val - 8 + 10, by omega⟩ (hkA' (by omega)) (hkB' (by omega))
    rw [hz]
    simp

/-- Vanishing of an SM-like direction when every `dirs22`
    direction vanishes at the entry. -/
theorem sm18_eq_zero_of_all {r c : I32}
    (h22 : ∀ m : Fin 22, dirs22 m r c = 0) (k : Fin 18) :
    (pairDirSM18 k : Matrix I32 I32 ℂ) r c = 0 := by
  rw [sm18_apply]
  split_ifs with hk
  · exact h22 _
  · rw [h22 _]
    simp

/-- Vanishing of a flipped direction when every `dirs22`
    direction vanishes at the entry. -/
theorem flip16_eq_zero_of_all {r c : I32}
    (h22 : ∀ m : Fin 22, dirs22 m r c = 0) (k : Fin 16) :
    (pairDirFlip16 k : Matrix I32 I32 ℂ) r c = 0 := by
  rw [flip16_apply]
  split_ifs with hk
  · exact h22 _
  · rw [h22 _]
    simp

/-- E-slot hermitian/anti vanishing from the folded coordinates of
    the entry (val form): if the entry's folded coordinates match
    no E-slot pair in either order, every hermitian and anti
    E-slot direction vanishes there. -/
theorem eslot_eq_zero_of_acoor_vals {r c : I32} (R C : Nat)
    (hr : (acoord r).val = R) (hc : (acoord c).val = C)
    (hH : ¬ ((R = 8 ∨ R = 9) ∧ 10 ≤ C ∧ C ≤ 15)
      ∧ ¬ ((C = 8 ∨ C = 9) ∧ 10 ≤ R ∧ R ≤ 15)) :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) r c = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) r c = 0) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · apply exHermDir_eq_zero_of_vals88
    rw [hr, hc]
    exact hH
  · apply exAntiDir_eq_zero_of_vals88
    rw [hr, hc]
    exact hH

/-- Supplement vanishing from the folded coordinates of the entry
    (val form). -/
theorem supp_eq_zero_of_acoor_vals {r c : I32} (R C : Nat)
    (hr : (acoord r).val = R) (hc : (acoord c).val = C)
    (hS : ¬ ((R = 8 ∧ C = 9) ∨ (R = 9 ∧ 10 ≤ C ∧ C ≤ 15))
      ∧ ¬ ((C = 8 ∧ R = 9) ∨ (C = 9 ∧ 10 ≤ R ∧ R ≤ 15))) :
    ∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) r c = 0 := by
  intro n
  apply supp8_eq_zero_of_vals88
  rw [hr, hc]
  exact hS

/-- All E-slot and supplement directions vanish at `(0, 8)`. -/
theorem eslot_van_0_8 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (0 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (0 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (0 : I32) (8 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 0 8 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 0 8 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 0 8 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(1, 9)`. -/
theorem eslot_van_1_9 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (1 : I32) (9 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (1 : I32) (9 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (1 : I32) (9 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 1 9 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 1 9 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 1 9 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(2, 10)`. -/
theorem eslot_van_2_10 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (2 : I32) (10 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (2 : I32) (10 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (2 : I32) (10 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 2 10 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 2 10 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 2 10 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(3, 11)`. -/
theorem eslot_van_3_11 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (3 : I32) (11 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (3 : I32) (11 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (3 : I32) (11 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 3 11 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 3 11 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 3 11 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(24, 8)`. -/
theorem eslot_van_24_8 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (24 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (24 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (24 : I32) (8 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 8 8 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 8 8 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 8 8 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(0, 9)`. -/
theorem eslot_van_0_9 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (0 : I32) (9 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (0 : I32) (9 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (0 : I32) (9 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 0 9 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 0 9 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 0 9 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(1, 8)`. -/
theorem eslot_van_1_8 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (1 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (1 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (1 : I32) (8 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 1 8 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 1 8 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 1 8 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(2, 11)`. -/
theorem eslot_van_2_11 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (2 : I32) (11 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (2 : I32) (11 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (2 : I32) (11 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 2 11 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 2 11 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 2 11 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(3, 10)`. -/
theorem eslot_van_3_10 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (3 : I32) (10 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (3 : I32) (10 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (3 : I32) (10 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 3 10 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 3 10 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 3 10 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(9, 25)`. -/
theorem eslot_van_9_25 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (9 : I32) (25 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (9 : I32) (25 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (9 : I32) (25 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 9 9 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 9 9 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 9 9 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(24, 16)`. -/
theorem eslot_van_24_16 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (24 : I32) (16 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (24 : I32) (16 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (24 : I32) (16 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 8 0 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 8 0 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 8 0 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(25, 17)`. -/
theorem eslot_van_25_17 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (25 : I32) (17 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (25 : I32) (17 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (25 : I32) (17 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 9 1 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 9 1 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 9 1 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(26, 18)`. -/
theorem eslot_van_26_18 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (26 : I32) (18 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (26 : I32) (18 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (26 : I32) (18 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 10 2 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 10 2 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 10 2 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(27, 19)`. -/
theorem eslot_van_27_19 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (27 : I32) (19 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (27 : I32) (19 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (27 : I32) (19 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 11 3 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 11 3 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 11 3 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(25, 16)`. -/
theorem eslot_van_25_16 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (25 : I32) (16 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (25 : I32) (16 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (25 : I32) (16 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 9 0 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 9 0 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 9 0 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(24, 17)`. -/
theorem eslot_van_24_17 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (24 : I32) (17 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (24 : I32) (17 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (24 : I32) (17 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 8 1 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 8 1 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 8 1 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(27, 18)`. -/
theorem eslot_van_27_18 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (27 : I32) (18 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (27 : I32) (18 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (27 : I32) (18 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 11 2 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 11 2 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 11 2 (by decide) (by decide) (by decide)⟩

/-- All E-slot and supplement directions vanish at `(26, 19)`. -/
theorem eslot_van_26_19 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (26 : I32) (19 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (26 : I32) (19 : I32) = 0)
      ∧ (∀ n : Fin 8, (pairDirExoticSupp8 n : Matrix I32 I32 ℂ) (26 : I32) (19 : I32) = 0) :=
  ⟨(eslot_eq_zero_of_acoor_vals 10 3 (by decide) (by decide) (by decide)).1,
   (eslot_eq_zero_of_acoor_vals 10 3 (by decide) (by decide) (by decide)).2,
   supp_eq_zero_of_acoor_vals 10 3 (by decide) (by decide) (by decide)⟩

/-- The hermitian and anti E-slot directions vanish at `(8, 25)`
    (the supplement directions do not - they are active there). -/
theorem eslot_van_8_25 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (8 : I32) (25 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (8 : I32) (25 : I32) = 0) :=
  eslot_eq_zero_of_acoor_vals 8 9 (by decide) (by decide) (by decide)

/-- The hermitian and anti E-slot directions vanish at `(25, 8)`
    (the supplement `(8, 9)` directions do not). -/
theorem eslot_van_25_8 :
    (∀ n : Fin 24, (exHermDir n : Matrix I32 I32 ℂ) (25 : I32) (8 : I32) = 0)
      ∧ (∀ n : Fin 18, (exAntiDir n : Matrix I32 I32 ℂ) (25 : I32) (8 : I32) = 0) :=
  eslot_eq_zero_of_acoor_vals 9 8 (by decide) (by decide) (by decide)

/-! ## 9. The extraction groups -/

/-- Extraction group SM-Nu: coefficients 0, 1 (hermitian SM) and
    10, 11 (anti-hermitian partners) vanish in any real relation,
    by the pivots `(0, 8)` and `(24, 16)`. -/
theorem grpSM0_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (0 : Fin 88) = 0 ∧ g (1 : Fin 88) = 0
      ∧ g (10 : Fin 88) = 0 ∧ g (11 : Fin 88) = 0 := by
  have hv1 : dir88Mat (0 : Fin 88) (0 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hva_08
  have hv2 : dir88Mat (1 : Fin 88) (0 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hvb_08
  have hv3 : dir88Mat (10 : Fin 88) (0 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (0 : I32)
      * (dirs22 (0 : Fin 22) (0 : I32) (8 : I32) * aRSgn (8 : I32))) = Complex.I
    rw [aRSgn_of_val_lt (show (0 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (8 : I32).val < 24 by decide), hva_08]
    simp
  have hv4 : dir88Mat (11 : Fin 88) (0 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (0 : I32)
      * (dirs22 (1 : Fin 22) (0 : I32) (8 : I32) * aRSgn (8 : I32))) = -1
    rw [aRSgn_of_val_lt (show (0 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (8 : I32).val < 24 by decide), hvb_08]
    simp
  have hw1 : dir88Mat (0 : Fin 88) (24 : I32) (16 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_24_16]
    exact hva_08
  have hw2 : dir88Mat (1 : Fin 88) (24 : I32) (16 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_24_16]
    exact hvb_08
  have hw3 : dir88Mat (10 : Fin 88) (24 : I32) (16 : I32) = -Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (24 : I32)
      * (dirs22 (0 : Fin 22) (24 : I32) (16 : I32) * aRSgn (16 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (24 : I32).val by decide),
      aRSgn_of_val_lt (show (16 : I32).val < 24 by decide),
      dirs22_apply_24_16, hva_08]
    simp
  have hw4 : dir88Mat (11 : Fin 88) (24 : I32) (16 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (24 : I32)
      * (dirs22 (1 : Fin 22) (24 : I32) (16 : I32) * aRSgn (16 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (24 : I32).val by decide),
      aRSgn_of_val_lt (show (16 : I32).val < 24 by decide),
      dirs22_apply_24_16, hvb_08]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (0 : Fin 88) → i ≠ (1 : Fin 88)
      → i ≠ (10 : Fin 88) → i ≠ (11 : Fin 88)
      → dir88Mat i (0 : I32) (8 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 0 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 1 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 10 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 11 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (0 : Fin 22).val
        → m.val ≠ (1 : Fin 22).val → dirs22 m (0 : I32) (8 : I32) = 0 :=
      dirs22_hvan_val hvan_08
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 0 from hne0)
        (fun _ => show i.val ≠ 1 from hne1)
        (fun h10 => show i.val - 10 ≠ 0 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 1 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 0 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 1 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 0 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 1 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 0 by omega)
              (show (i.val - 34) + 18 ≠ 1 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (0 : I32) (8 : I32) = 0
              exact eslot_van_0_8.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (0 : I32) (8 : I32) = 0
              exact eslot_van_0_8.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_0_8.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (0 : Fin 88) → i ≠ (1 : Fin 88)
      → i ≠ (10 : Fin 88) → i ≠ (11 : Fin 88)
      → dir88Mat i (24 : I32) (16 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 0 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 1 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 10 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 11 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (0 : Fin 22).val
        → m.val ≠ (1 : Fin 22).val → dirs22 m (24 : I32) (16 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_24_16]; exact hvan_08 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 0 from hne0)
        (fun _ => show i.val ≠ 1 from hne1)
        (fun h10 => show i.val - 10 ≠ 0 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 1 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 0 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 1 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 0 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 1 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 0 by omega)
              (show (i.val - 34) + 18 ≠ 1 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (16 : I32) = 0
              exact eslot_van_24_16.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (16 : I32) = 0
              exact eslot_van_24_16.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_24_16.2.2 _
  exact quad_extractA 0 8 24 16 0 1 10 11 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg

/-- Extraction group yR: coefficients 8, 9 vanish in any real
    relation, by the pivot `(24, 8)`. -/
theorem grpYR_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (8 : Fin 88) = 0 ∧ g (9 : Fin 88) = 0 := by
  have hvA : dir88Mat (8 : Fin 88) (24 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hva_24_8
  have hvB : dir88Mat (9 : Fin 88) (24 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hvb_24_8
  have hvan : ∀ i : Fin 88, i ≠ (8 : Fin 88) → i ≠ (9 : Fin 88)
      → dir88Mat i (24 : I32) (8 : I32) = 0 := by
    intro i hi8 hi9
    have hne8 : i.val ≠ 8 := fin88_val_ne_of_ne (by norm_num) hi8
    have hne9 : i.val ≠ 9 := fin88_val_ne_of_ne (by norm_num) hi9
    have h22 : ∀ m : Fin 22, m.val ≠ (8 : Fin 22).val
        → m.val ≠ (9 : Fin 22).val → dirs22 m (24 : I32) (8 : I32) = 0 :=
      dirs22_hvan_val hvan_24_8
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 8 from hne8)
        (fun _ => show i.val ≠ 9 from hne9)
        (fun h10 => show i.val - 10 ≠ 8 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 9 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 8 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 9 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 8 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 9 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 8 by omega)
              (show (i.val - 34) + 18 ≠ 9 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (8 : I32) = 0
              exact eslot_van_24_8.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (8 : I32) = 0
              exact eslot_van_24_8.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_24_8.2.2 _
  exact pair_extract88 24 8 8 9 (by decide) hvA hvB hvan g hg

/-- Extraction group SM-1: coefficients 0, 1 (hermitian SM) and
    10, 11 (anti-hermitian partners) vanish in any real relation,
    by the pivots `(0, 8)` and `(24, 16)`. -/
theorem grpSM1_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (2 : Fin 88) = 0 ∧ g (3 : Fin 88) = 0
      ∧ g (12 : Fin 88) = 0 ∧ g (13 : Fin 88) = 0 := by
  have hv1 : dir88Mat (2 : Fin 88) (1 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hva_19
  have hv2 : dir88Mat (3 : Fin 88) (1 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hvb_19
  have hv3 : dir88Mat (12 : Fin 88) (1 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (1 : I32)
      * (dirs22 (2 : Fin 22) (1 : I32) (9 : I32) * aRSgn (9 : I32))) = Complex.I
    rw [aRSgn_of_val_lt (show (1 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (9 : I32).val < 24 by decide), hva_19]
    simp
  have hv4 : dir88Mat (13 : Fin 88) (1 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (1 : I32)
      * (dirs22 (3 : Fin 22) (1 : I32) (9 : I32) * aRSgn (9 : I32))) = -1
    rw [aRSgn_of_val_lt (show (1 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (9 : I32).val < 24 by decide), hvb_19]
    simp
  have hw1 : dir88Mat (2 : Fin 88) (25 : I32) (17 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_25_17]
    exact hva_19
  have hw2 : dir88Mat (3 : Fin 88) (25 : I32) (17 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_25_17]
    exact hvb_19
  have hw3 : dir88Mat (12 : Fin 88) (25 : I32) (17 : I32) = -Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (25 : I32)
      * (dirs22 (2 : Fin 22) (25 : I32) (17 : I32) * aRSgn (17 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (25 : I32).val by decide),
      aRSgn_of_val_lt (show (17 : I32).val < 24 by decide),
      dirs22_apply_25_17, hva_19]
    simp
  have hw4 : dir88Mat (13 : Fin 88) (25 : I32) (17 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (25 : I32)
      * (dirs22 (3 : Fin 22) (25 : I32) (17 : I32) * aRSgn (17 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (25 : I32).val by decide),
      aRSgn_of_val_lt (show (17 : I32).val < 24 by decide),
      dirs22_apply_25_17, hvb_19]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (2 : Fin 88) → i ≠ (3 : Fin 88)
      → i ≠ (12 : Fin 88) → i ≠ (13 : Fin 88)
      → dir88Mat i (1 : I32) (9 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 2 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 3 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 12 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 13 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (2 : Fin 22).val
        → m.val ≠ (3 : Fin 22).val → dirs22 m (1 : I32) (9 : I32) = 0 :=
      dirs22_hvan_val hvan_19
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 2 from hne0)
        (fun _ => show i.val ≠ 3 from hne1)
        (fun h10 => show i.val - 10 ≠ 2 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 3 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 2 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 3 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 2 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 3 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 2 by omega)
              (show (i.val - 34) + 18 ≠ 3 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (1 : I32) (9 : I32) = 0
              exact eslot_van_1_9.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (1 : I32) (9 : I32) = 0
              exact eslot_van_1_9.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_1_9.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (2 : Fin 88) → i ≠ (3 : Fin 88)
      → i ≠ (12 : Fin 88) → i ≠ (13 : Fin 88)
      → dir88Mat i (25 : I32) (17 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 2 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 3 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 12 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 13 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (2 : Fin 22).val
        → m.val ≠ (3 : Fin 22).val → dirs22 m (25 : I32) (17 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_25_17]; exact hvan_19 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 2 from hne0)
        (fun _ => show i.val ≠ 3 from hne1)
        (fun h10 => show i.val - 10 ≠ 2 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 3 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 2 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 3 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 2 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 3 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 2 by omega)
              (show (i.val - 34) + 18 ≠ 3 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (17 : I32) = 0
              exact eslot_van_25_17.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (17 : I32) = 0
              exact eslot_van_25_17.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_25_17.2.2 _
  exact quad_extractA 1 9 25 17 2 3 12 13 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group SM-2: coefficients 0, 1 (hermitian SM) and
    10, 11 (anti-hermitian partners) vanish in any real relation,
    by the pivots `(0, 8)` and `(24, 16)`. -/
theorem grpSM2_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (4 : Fin 88) = 0 ∧ g (5 : Fin 88) = 0
      ∧ g (14 : Fin 88) = 0 ∧ g (15 : Fin 88) = 0 := by
  have hv1 : dir88Mat (4 : Fin 88) (2 : I32) (10 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hva_2_10
  have hv2 : dir88Mat (5 : Fin 88) (2 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hvb_2_10
  have hv3 : dir88Mat (14 : Fin 88) (2 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (2 : I32)
      * (dirs22 (4 : Fin 22) (2 : I32) (10 : I32) * aRSgn (10 : I32))) = Complex.I
    rw [aRSgn_of_val_lt (show (2 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (10 : I32).val < 24 by decide), hva_2_10]
    simp
  have hv4 : dir88Mat (15 : Fin 88) (2 : I32) (10 : I32) = -1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (2 : I32)
      * (dirs22 (5 : Fin 22) (2 : I32) (10 : I32) * aRSgn (10 : I32))) = -1
    rw [aRSgn_of_val_lt (show (2 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (10 : I32).val < 24 by decide), hvb_2_10]
    simp
  have hw1 : dir88Mat (4 : Fin 88) (26 : I32) (18 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_26_18]
    exact hva_2_10
  have hw2 : dir88Mat (5 : Fin 88) (26 : I32) (18 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_26_18]
    exact hvb_2_10
  have hw3 : dir88Mat (14 : Fin 88) (26 : I32) (18 : I32) = -Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (26 : I32)
      * (dirs22 (4 : Fin 22) (26 : I32) (18 : I32) * aRSgn (18 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (26 : I32).val by decide),
      aRSgn_of_val_lt (show (18 : I32).val < 24 by decide),
      dirs22_apply_26_18, hva_2_10]
    simp
  have hw4 : dir88Mat (15 : Fin 88) (26 : I32) (18 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (26 : I32)
      * (dirs22 (5 : Fin 22) (26 : I32) (18 : I32) * aRSgn (18 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (26 : I32).val by decide),
      aRSgn_of_val_lt (show (18 : I32).val < 24 by decide),
      dirs22_apply_26_18, hvb_2_10]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (4 : Fin 88) → i ≠ (5 : Fin 88)
      → i ≠ (14 : Fin 88) → i ≠ (15 : Fin 88)
      → dir88Mat i (2 : I32) (10 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 4 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 5 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 14 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 15 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (4 : Fin 22).val
        → m.val ≠ (5 : Fin 22).val → dirs22 m (2 : I32) (10 : I32) = 0 :=
      dirs22_hvan_val hvan_2_10
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 4 from hne0)
        (fun _ => show i.val ≠ 5 from hne1)
        (fun h10 => show i.val - 10 ≠ 4 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 5 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 4 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 5 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 4 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 5 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 4 by omega)
              (show (i.val - 34) + 18 ≠ 5 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (2 : I32) (10 : I32) = 0
              exact eslot_van_2_10.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (2 : I32) (10 : I32) = 0
              exact eslot_van_2_10.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_2_10.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (4 : Fin 88) → i ≠ (5 : Fin 88)
      → i ≠ (14 : Fin 88) → i ≠ (15 : Fin 88)
      → dir88Mat i (26 : I32) (18 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 4 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 5 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 14 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 15 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (4 : Fin 22).val
        → m.val ≠ (5 : Fin 22).val → dirs22 m (26 : I32) (18 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_26_18]; exact hvan_2_10 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 4 from hne0)
        (fun _ => show i.val ≠ 5 from hne1)
        (fun h10 => show i.val - 10 ≠ 4 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 5 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 4 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 5 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 4 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 5 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 4 by omega)
              (show (i.val - 34) + 18 ≠ 5 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (18 : I32) = 0
              exact eslot_van_26_18.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (18 : I32) = 0
              exact eslot_van_26_18.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_26_18.2.2 _
  exact quad_extractA 2 10 26 18 4 5 14 15 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group SM-3: coefficients 0, 1 (hermitian SM) and
    10, 11 (anti-hermitian partners) vanish in any real relation,
    by the pivots `(0, 8)` and `(24, 16)`. -/
theorem grpSM3_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (6 : Fin 88) = 0 ∧ g (7 : Fin 88) = 0
      ∧ g (16 : Fin 88) = 0 ∧ g (17 : Fin 88) = 0 := by
  have hv1 : dir88Mat (6 : Fin 88) (3 : I32) (11 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hva_3_11
  have hv2 : dir88Mat (7 : Fin 88) (3 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide)]
    exact hvb_3_11
  have hv3 : dir88Mat (16 : Fin 88) (3 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (3 : I32)
      * (dirs22 (6 : Fin 22) (3 : I32) (11 : I32) * aRSgn (11 : I32))) = Complex.I
    rw [aRSgn_of_val_lt (show (3 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (11 : I32).val < 24 by decide), hva_3_11]
    simp
  have hv4 : dir88Mat (17 : Fin 88) (3 : I32) (11 : I32) = -1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (3 : I32)
      * (dirs22 (7 : Fin 22) (3 : I32) (11 : I32) * aRSgn (11 : I32))) = -1
    rw [aRSgn_of_val_lt (show (3 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (11 : I32).val < 24 by decide), hvb_3_11]
    simp
  have hw1 : dir88Mat (6 : Fin 88) (27 : I32) (19 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_27_19]
    exact hva_3_11
  have hw2 : dir88Mat (7 : Fin 88) (27 : I32) (19 : I32) = Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_pos (by decide),
      dirs22_apply_27_19]
    exact hvb_3_11
  have hw3 : dir88Mat (16 : Fin 88) (27 : I32) (19 : I32) = -Complex.I := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (27 : I32)
      * (dirs22 (6 : Fin 22) (27 : I32) (19 : I32) * aRSgn (19 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (27 : I32).val by decide),
      aRSgn_of_val_lt (show (19 : I32).val < 24 by decide),
      dirs22_apply_27_19, hva_3_11]
    simp
  have hw4 : dir88Mat (17 : Fin 88) (27 : I32) (19 : I32) = 1 := by
    rw [dir88Mat_of_lt18 (by decide), sm18_apply, if_neg (by decide)]
    show Complex.I * (aRSgn (27 : I32)
      * (dirs22 (7 : Fin 22) (27 : I32) (19 : I32) * aRSgn (19 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (27 : I32).val by decide),
      aRSgn_of_val_lt (show (19 : I32).val < 24 by decide),
      dirs22_apply_27_19, hvb_3_11]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (6 : Fin 88) → i ≠ (7 : Fin 88)
      → i ≠ (16 : Fin 88) → i ≠ (17 : Fin 88)
      → dir88Mat i (3 : I32) (11 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 6 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 7 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 16 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 17 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (6 : Fin 22).val
        → m.val ≠ (7 : Fin 22).val → dirs22 m (3 : I32) (11 : I32) = 0 :=
      dirs22_hvan_val hvan_3_11
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 6 from hne0)
        (fun _ => show i.val ≠ 7 from hne1)
        (fun h10 => show i.val - 10 ≠ 6 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 7 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 6 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 7 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 6 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 7 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 6 by omega)
              (show (i.val - 34) + 18 ≠ 7 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (3 : I32) (11 : I32) = 0
              exact eslot_van_3_11.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (3 : I32) (11 : I32) = 0
              exact eslot_van_3_11.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_3_11.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (6 : Fin 88) → i ≠ (7 : Fin 88)
      → i ≠ (16 : Fin 88) → i ≠ (17 : Fin 88)
      → dir88Mat i (27 : I32) (19 : I32) = 0 := by
    intro i hi0 hi1 hi10 hi11
    have hne0 : i.val ≠ 6 := fin88_val_ne_of_ne (by norm_num) hi0
    have hne1 : i.val ≠ 7 := fin88_val_ne_of_ne (by norm_num) hi1
    have hne10 : i.val ≠ 16 := fin88_val_ne_of_ne (by norm_num) hi10
    have hne11 : i.val ≠ 17 := fin88_val_ne_of_ne (by norm_num) hi11
    have h22 : ∀ m : Fin 22, m.val ≠ (6 : Fin 22).val
        → m.val ≠ (7 : Fin 22).val → dirs22 m (27 : I32) (19 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_27_19]; exact hvan_3_11 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22 (fun _ => show i.val ≠ 6 from hne0)
        (fun _ => show i.val ≠ 7 from hne1)
        (fun h10 => show i.val - 10 ≠ 6 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 7 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun _ => show (i.val - 18) + 10 ≠ 6 by omega)
          (fun _ => show (i.val - 18) + 10 ≠ 7 by omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 6 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 7 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 6 by omega)
              (show (i.val - 34) + 18 ≠ 7 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (19 : I32) = 0
              exact eslot_van_27_19.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (19 : I32) = 0
              exact eslot_van_27_19.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_27_19.2.2 _
  exact quad_extractA 3 11 27 19 6 7 16 17 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group FL-0: coefficients 18, 19 (hermitian
    flipped) and 26, 27 (anti-hermitian partners) vanish in any
    real relation, by the pivots `(0, 9)` and `(25, 16)`. -/
theorem grpFL0_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (18 : Fin 88) = 0 ∧ g (19 : Fin 88) = 0
      ∧ g (26 : Fin 88) = 0 ∧ g (27 : Fin 88) = 0 := by
  have hv1 : dir88Mat (18 : Fin 88) (0 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hva_09
  have hv2 : dir88Mat (19 : Fin 88) (0 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hvb_09
  have hv3 : dir88Mat (26 : Fin 88) (0 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (0 : I32)
      * (dirs22 (10 : Fin 22) (0 : I32) (9 : I32) * aRSgn (9 : I32)))
        = Complex.I
    rw [aRSgn_of_val_lt (show (0 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (9 : I32).val < 24 by decide), hva_09]
    simp
  have hv4 : dir88Mat (27 : Fin 88) (0 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (0 : I32)
      * (dirs22 (11 : Fin 22) (0 : I32) (9 : I32) * aRSgn (9 : I32))) = -1
    rw [aRSgn_of_val_lt (show (0 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (9 : I32).val < 24 by decide), hvb_09]
    simp
  have hw1 : dir88Mat (18 : Fin 88) (25 : I32) (16 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_25_16]
    exact hva_09
  have hw2 : dir88Mat (19 : Fin 88) (25 : I32) (16 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_25_16]
    exact hvb_09
  have hw3 : dir88Mat (26 : Fin 88) (25 : I32) (16 : I32) = -Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (25 : I32)
      * (dirs22 (10 : Fin 22) (25 : I32) (16 : I32) * aRSgn (16 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (25 : I32).val by decide),
      aRSgn_of_val_lt (show (16 : I32).val < 24 by decide),
      dirs22_apply_25_16, hva_09]
    simp
  have hw4 : dir88Mat (27 : Fin 88) (25 : I32) (16 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (25 : I32)
      * (dirs22 (11 : Fin 22) (25 : I32) (16 : I32) * aRSgn (16 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (25 : I32).val by decide),
      aRSgn_of_val_lt (show (16 : I32).val < 24 by decide),
      dirs22_apply_25_16, hvb_09]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (18 : Fin 88) → i ≠ (19 : Fin 88)
      → i ≠ (26 : Fin 88) → i ≠ (27 : Fin 88)
      → dir88Mat i (0 : I32) (9 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 18 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 19 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 26 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 27 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (10 : Fin 22).val
        → m.val ≠ (11 : Fin 22).val → dirs22 m (0 : I32) (9 : I32) = 0 :=
      dirs22_hvan_val hvan_09
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 10 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 11 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 10 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 11 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 10 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 11 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 10 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 11 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 10 by omega)
              (show (i.val - 34) + 18 ≠ 11 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (0 : I32) (9 : I32) = 0
              exact eslot_van_0_9.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (0 : I32) (9 : I32) = 0
              exact eslot_van_0_9.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_0_9.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (18 : Fin 88) → i ≠ (19 : Fin 88)
      → i ≠ (26 : Fin 88) → i ≠ (27 : Fin 88)
      → dir88Mat i (25 : I32) (16 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 18 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 19 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 26 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 27 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (10 : Fin 22).val
        → m.val ≠ (11 : Fin 22).val → dirs22 m (25 : I32) (16 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_25_16]; exact hvan_09 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 10 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 11 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 10 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 11 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 10 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 11 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 10 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 11 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 10 by omega)
              (show (i.val - 34) + 18 ≠ 11 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (16 : I32) = 0
              exact eslot_van_25_16.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (16 : I32) = 0
              exact eslot_van_25_16.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_25_16.2.2 _
  exact quad_extractA 0 9 25 16 18 19 26 27 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg

/-- Extraction group FL-1: coefficients 18, 19 (hermitian
    flipped) and 26, 27 (anti-hermitian partners) vanish in any
    real relation, by the pivots `(0, 9)` and `(25, 16)`. -/
theorem grpFL1_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (20 : Fin 88) = 0 ∧ g (21 : Fin 88) = 0
      ∧ g (28 : Fin 88) = 0 ∧ g (29 : Fin 88) = 0 := by
  have hv1 : dir88Mat (20 : Fin 88) (1 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hva_18
  have hv2 : dir88Mat (21 : Fin 88) (1 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hvb_18
  have hv3 : dir88Mat (28 : Fin 88) (1 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (1 : I32)
      * (dirs22 (12 : Fin 22) (1 : I32) (8 : I32) * aRSgn (8 : I32)))
        = Complex.I
    rw [aRSgn_of_val_lt (show (1 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (8 : I32).val < 24 by decide), hva_18]
    simp
  have hv4 : dir88Mat (29 : Fin 88) (1 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (1 : I32)
      * (dirs22 (13 : Fin 22) (1 : I32) (8 : I32) * aRSgn (8 : I32))) = -1
    rw [aRSgn_of_val_lt (show (1 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (8 : I32).val < 24 by decide), hvb_18]
    simp
  have hw1 : dir88Mat (20 : Fin 88) (24 : I32) (17 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_24_17]
    exact hva_18
  have hw2 : dir88Mat (21 : Fin 88) (24 : I32) (17 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_24_17]
    exact hvb_18
  have hw3 : dir88Mat (28 : Fin 88) (24 : I32) (17 : I32) = -Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (24 : I32)
      * (dirs22 (12 : Fin 22) (24 : I32) (17 : I32) * aRSgn (17 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (24 : I32).val by decide),
      aRSgn_of_val_lt (show (17 : I32).val < 24 by decide),
      dirs22_apply_24_17, hva_18]
    simp
  have hw4 : dir88Mat (29 : Fin 88) (24 : I32) (17 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (24 : I32)
      * (dirs22 (13 : Fin 22) (24 : I32) (17 : I32) * aRSgn (17 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (24 : I32).val by decide),
      aRSgn_of_val_lt (show (17 : I32).val < 24 by decide),
      dirs22_apply_24_17, hvb_18]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (20 : Fin 88) → i ≠ (21 : Fin 88)
      → i ≠ (28 : Fin 88) → i ≠ (29 : Fin 88)
      → dir88Mat i (1 : I32) (8 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 20 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 21 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 28 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 29 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (12 : Fin 22).val
        → m.val ≠ (13 : Fin 22).val → dirs22 m (1 : I32) (8 : I32) = 0 :=
      dirs22_hvan_val hvan_18
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 12 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 13 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 12 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 13 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 12 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 13 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 12 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 13 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 12 by omega)
              (show (i.val - 34) + 18 ≠ 13 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (1 : I32) (8 : I32) = 0
              exact eslot_van_1_8.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (1 : I32) (8 : I32) = 0
              exact eslot_van_1_8.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_1_8.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (20 : Fin 88) → i ≠ (21 : Fin 88)
      → i ≠ (28 : Fin 88) → i ≠ (29 : Fin 88)
      → dir88Mat i (24 : I32) (17 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 20 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 21 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 28 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 29 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (12 : Fin 22).val
        → m.val ≠ (13 : Fin 22).val → dirs22 m (24 : I32) (17 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_24_17]; exact hvan_18 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 12 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 13 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 12 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 13 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 12 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 13 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 12 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 13 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 12 by omega)
              (show (i.val - 34) + 18 ≠ 13 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (17 : I32) = 0
              exact eslot_van_24_17.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (17 : I32) = 0
              exact eslot_van_24_17.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_24_17.2.2 _
  exact quad_extractA 1 8 24 17 20 21 28 29 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group FL-2: coefficients 18, 19 (hermitian
    flipped) and 26, 27 (anti-hermitian partners) vanish in any
    real relation, by the pivots `(0, 9)` and `(25, 16)`. -/
theorem grpFL2_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (22 : Fin 88) = 0 ∧ g (23 : Fin 88) = 0
      ∧ g (30 : Fin 88) = 0 ∧ g (31 : Fin 88) = 0 := by
  have hv1 : dir88Mat (22 : Fin 88) (2 : I32) (11 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hva_2_11
  have hv2 : dir88Mat (23 : Fin 88) (2 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hvb_2_11
  have hv3 : dir88Mat (30 : Fin 88) (2 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (2 : I32)
      * (dirs22 (14 : Fin 22) (2 : I32) (11 : I32) * aRSgn (11 : I32)))
        = Complex.I
    rw [aRSgn_of_val_lt (show (2 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (11 : I32).val < 24 by decide), hva_2_11]
    simp
  have hv4 : dir88Mat (31 : Fin 88) (2 : I32) (11 : I32) = -1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (2 : I32)
      * (dirs22 (15 : Fin 22) (2 : I32) (11 : I32) * aRSgn (11 : I32))) = -1
    rw [aRSgn_of_val_lt (show (2 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (11 : I32).val < 24 by decide), hvb_2_11]
    simp
  have hw1 : dir88Mat (22 : Fin 88) (27 : I32) (18 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_27_18]
    exact hva_2_11
  have hw2 : dir88Mat (23 : Fin 88) (27 : I32) (18 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_27_18]
    exact hvb_2_11
  have hw3 : dir88Mat (30 : Fin 88) (27 : I32) (18 : I32) = -Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (27 : I32)
      * (dirs22 (14 : Fin 22) (27 : I32) (18 : I32) * aRSgn (18 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (27 : I32).val by decide),
      aRSgn_of_val_lt (show (18 : I32).val < 24 by decide),
      dirs22_apply_27_18, hva_2_11]
    simp
  have hw4 : dir88Mat (31 : Fin 88) (27 : I32) (18 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (27 : I32)
      * (dirs22 (15 : Fin 22) (27 : I32) (18 : I32) * aRSgn (18 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (27 : I32).val by decide),
      aRSgn_of_val_lt (show (18 : I32).val < 24 by decide),
      dirs22_apply_27_18, hvb_2_11]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (22 : Fin 88) → i ≠ (23 : Fin 88)
      → i ≠ (30 : Fin 88) → i ≠ (31 : Fin 88)
      → dir88Mat i (2 : I32) (11 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 22 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 23 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 30 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 31 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (14 : Fin 22).val
        → m.val ≠ (15 : Fin 22).val → dirs22 m (2 : I32) (11 : I32) = 0 :=
      dirs22_hvan_val hvan_2_11
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 14 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 15 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 14 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 15 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 14 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 15 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 14 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 15 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 14 by omega)
              (show (i.val - 34) + 18 ≠ 15 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (2 : I32) (11 : I32) = 0
              exact eslot_van_2_11.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (2 : I32) (11 : I32) = 0
              exact eslot_van_2_11.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_2_11.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (22 : Fin 88) → i ≠ (23 : Fin 88)
      → i ≠ (30 : Fin 88) → i ≠ (31 : Fin 88)
      → dir88Mat i (27 : I32) (18 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 22 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 23 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 30 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 31 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (14 : Fin 22).val
        → m.val ≠ (15 : Fin 22).val → dirs22 m (27 : I32) (18 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_27_18]; exact hvan_2_11 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 14 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 15 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 14 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 15 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 14 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 15 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 14 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 15 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 14 by omega)
              (show (i.val - 34) + 18 ≠ 15 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (18 : I32) = 0
              exact eslot_van_27_18.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (18 : I32) = 0
              exact eslot_van_27_18.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_27_18.2.2 _
  exact quad_extractA 2 11 27 18 22 23 30 31 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group FL-3: coefficients 18, 19 (hermitian
    flipped) and 26, 27 (anti-hermitian partners) vanish in any
    real relation, by the pivots `(0, 9)` and `(25, 16)`. -/
theorem grpFL3_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (24 : Fin 88) = 0 ∧ g (25 : Fin 88) = 0
      ∧ g (32 : Fin 88) = 0 ∧ g (33 : Fin 88) = 0 := by
  have hv1 : dir88Mat (24 : Fin 88) (3 : I32) (10 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hva_3_10
  have hv2 : dir88Mat (25 : Fin 88) (3 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide)]
    exact hvb_3_10
  have hv3 : dir88Mat (32 : Fin 88) (3 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (3 : I32)
      * (dirs22 (16 : Fin 22) (3 : I32) (10 : I32) * aRSgn (10 : I32)))
        = Complex.I
    rw [aRSgn_of_val_lt (show (3 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (10 : I32).val < 24 by decide), hva_3_10]
    simp
  have hv4 : dir88Mat (33 : Fin 88) (3 : I32) (10 : I32) = -1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (3 : I32)
      * (dirs22 (17 : Fin 22) (3 : I32) (10 : I32) * aRSgn (10 : I32))) = -1
    rw [aRSgn_of_val_lt (show (3 : I32).val < 24 by decide),
      aRSgn_of_val_lt (show (10 : I32).val < 24 by decide), hvb_3_10]
    simp
  have hw1 : dir88Mat (24 : Fin 88) (26 : I32) (19 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_26_19]
    exact hva_3_10
  have hw2 : dir88Mat (25 : Fin 88) (26 : I32) (19 : I32) = Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_pos (by decide), dirs22_apply_26_19]
    exact hvb_3_10
  have hw3 : dir88Mat (32 : Fin 88) (26 : I32) (19 : I32) = -Complex.I := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (26 : I32)
      * (dirs22 (16 : Fin 22) (26 : I32) (19 : I32) * aRSgn (19 : I32)))
        = -Complex.I
    rw [aRSgn_of_val_ge (show 24 ≤ (26 : I32).val by decide),
      aRSgn_of_val_lt (show (19 : I32).val < 24 by decide),
      dirs22_apply_26_19, hva_3_10]
    simp
  have hw4 : dir88Mat (33 : Fin 88) (26 : I32) (19 : I32) = 1 := by
    rw [dir88Mat_of_flip (by decide) (by decide), flip16_apply,
      dif_neg (by decide)]
    show Complex.I * (aRSgn (26 : I32)
      * (dirs22 (17 : Fin 22) (26 : I32) (19 : I32) * aRSgn (19 : I32))) = 1
    rw [aRSgn_of_val_ge (show 24 ≤ (26 : I32).val by decide),
      aRSgn_of_val_lt (show (19 : I32).val < 24 by decide),
      dirs22_apply_26_19, hvb_3_10]
    simp
  have hvan1 : ∀ i : Fin 88, i ≠ (24 : Fin 88) → i ≠ (25 : Fin 88)
      → i ≠ (32 : Fin 88) → i ≠ (33 : Fin 88)
      → dir88Mat i (3 : I32) (10 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 24 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 25 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 32 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 33 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (16 : Fin 22).val
        → m.val ≠ (17 : Fin 22).val → dirs22 m (3 : I32) (10 : I32) = 0 :=
      dirs22_hvan_val hvan_3_10
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 16 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 17 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 16 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 17 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 16 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 17 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 16 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 17 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 16 by omega)
              (show (i.val - 34) + 18 ≠ 17 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (3 : I32) (10 : I32) = 0
              exact eslot_van_3_10.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (3 : I32) (10 : I32) = 0
              exact eslot_van_3_10.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_3_10.2.2 _
  have hvan2 : ∀ i : Fin 88, i ≠ (24 : Fin 88) → i ≠ (25 : Fin 88)
      → i ≠ (32 : Fin 88) → i ≠ (33 : Fin 88)
      → dir88Mat i (26 : I32) (19 : I32) = 0 := by
    intro i hi18 hi19 hi26 hi27
    have hne18 : i.val ≠ 24 := fin88_val_ne_of_ne (by norm_num) hi18
    have hne19 : i.val ≠ 25 := fin88_val_ne_of_ne (by norm_num) hi19
    have hne26 : i.val ≠ 32 := fin88_val_ne_of_ne (by norm_num) hi26
    have hne27 : i.val ≠ 33 := fin88_val_ne_of_ne (by norm_num) hi27
    have h22 : ∀ m : Fin 22, m.val ≠ (16 : Fin 22).val
        → m.val ≠ (17 : Fin 22).val → dirs22 m (26 : I32) (19 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_26_19]; exact hvan_3_10 m h1 h2)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 16 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 17 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 16 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 17 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 16 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 17 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 16 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 17 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 16 by omega)
              (show (i.val - 34) + 18 ≠ 17 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (19 : I32) = 0
              exact eslot_van_26_19.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (19 : I32) = 0
              exact eslot_van_26_19.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_26_19.2.2 _
  exact quad_extractA 3 10 26 19 24 25 32 33 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group G10: coefficients 34, 35 (the seg4 pair
    `(18, 19)`) and 80, 81 (the supplement `(8, 9)` pair) vanish
    in any real relation, by the pivots `(8, 25)` and `(25, 8)`. -/
theorem grpG10_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (34 : Fin 88) = 0 ∧ g (35 : Fin 88) = 0
      ∧ g (80 : Fin 88) = 0 ∧ g (81 : Fin 88) = 0 := by
  have hv1 : dir88Mat (34 : Fin 88) (8 : I32) (25 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_lt4 (by decide)]
    exact hva_8_25
  have hv2 : dir88Mat (35 : Fin 88) (8 : I32) (25 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_lt4 (by decide)]
    exact hvb_8_25
  have hv3 : dir88Mat (80 : Fin 88) (8 : I32) (25 : I32) = 1 := by
    rw [dir88Mat_of_supp (by decide),
      supp8_apply_8_25 (by decide) (by decide)]
    show star (1 : ℂ) = 1
    simp
  have hv4 : dir88Mat (81 : Fin 88) (8 : I32) (25 : I32) = -Complex.I := by
    rw [dir88Mat_of_supp (by decide),
      supp8_apply_8_25 (by decide) (by decide)]
    show star (Complex.I : ℂ) = -Complex.I
    exact star_I_eq_neg_I
  have hw1 : dir88Mat (34 : Fin 88) (25 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_lt4 (by decide), dirs22_apply_25_8]
    show star (dirs22 (18 : Fin 22) (8 : I32) (25 : I32)) = 1
    rw [hva_8_25]
    simp
  have hw2 : dir88Mat (35 : Fin 88) (25 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_lt4 (by decide), dirs22_apply_25_8]
    show star (dirs22 (19 : Fin 22) (8 : I32) (25 : I32)) = -Complex.I
    rw [hvb_8_25]
    exact star_I_eq_neg_I
  have hw3 : dir88Mat (80 : Fin 88) (25 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_supp (by decide),
      supp8_apply_25_8 (by decide) (by decide)]
    show -(exPhase 0) = -1
    rw [show exPhase 0 = 1 from rfl]
  have hw4 : dir88Mat (81 : Fin 88) (25 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_supp (by decide),
      supp8_apply_25_8 (by decide) (by decide)]
    show -(exPhase 1) = -Complex.I
    rw [show exPhase 1 = Complex.I from rfl]
  have hvan1 : ∀ i : Fin 88, i ≠ (34 : Fin 88) → i ≠ (35 : Fin 88)
      → i ≠ (80 : Fin 88) → i ≠ (81 : Fin 88)
      → dir88Mat i (8 : I32) (25 : I32) = 0 := by
    intro i hi34 hi35 hi80 hi81
    have hne34 : i.val ≠ 34 := fin88_val_ne_of_ne (by norm_num) hi34
    have hne35 : i.val ≠ 35 := fin88_val_ne_of_ne (by norm_num) hi35
    have hne80 : i.val ≠ 80 := fin88_val_ne_of_ne (by norm_num) hi80
    have hne81 : i.val ≠ 81 := fin88_val_ne_of_ne (by norm_num) hi81
    have h22 : ∀ m : Fin 22, m.val ≠ (18 : Fin 22).val
        → m.val ≠ (19 : Fin 22).val → dirs22 m (8 : I32) (25 : I32) = 0 :=
      dirs22_hvan_val hvan_8_25
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 18 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 19 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 18 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 19 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 18 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 19 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 18 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 19 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 18 by omega)
              (show (i.val - 34) + 18 ≠ 19 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (8 : I32) (25 : I32) = 0
              exact eslot_van_8_25.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (8 : I32) (25 : I32) = 0
              exact eslot_van_8_25.2 _
        · rw [dir88Mat_of_supp (by omega)]
          have hU9 : (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)).val
              = 9 := by
            rw [suppU_val]
            split_ifs with hm0
            · exfalso
              have hm0' : (i.val - 80) / 2 = 0 := hm0
              omega
            · rfl
          refine supp8_eq_zero_8_25 (n := ⟨i.val - 80, by omega⟩) ?_
          rintro ⟨hc1, -⟩
          have e1 := congrArg Fin.val hc1
          omega
  have hvan2 : ∀ i : Fin 88, i ≠ (34 : Fin 88) → i ≠ (35 : Fin 88)
      → i ≠ (80 : Fin 88) → i ≠ (81 : Fin 88)
      → dir88Mat i (25 : I32) (8 : I32) = 0 := by
    intro i hi34 hi35 hi80 hi81
    have hne34 : i.val ≠ 34 := fin88_val_ne_of_ne (by norm_num) hi34
    have hne35 : i.val ≠ 35 := fin88_val_ne_of_ne (by norm_num) hi35
    have hne80 : i.val ≠ 80 := fin88_val_ne_of_ne (by norm_num) hi80
    have hne81 : i.val ≠ 81 := fin88_val_ne_of_ne (by norm_num) hi81
    have h22 : ∀ m : Fin 22, m.val ≠ (18 : Fin 22).val
        → m.val ≠ (19 : Fin 22).val → dirs22 m (25 : I32) (8 : I32) = 0 :=
      dirs22_hvan_val (fun m h1 h2 => by
        rw [dirs22_apply_25_8, hvan_8_25 m h1 h2]; simp)
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 18 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 19 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 18 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 19 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 18 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 19 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 18 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 19 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 18 by omega)
              (show (i.val - 34) + 18 ≠ 19 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (8 : I32) = 0
              exact eslot_van_25_8.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (8 : I32) = 0
              exact eslot_van_25_8.2 _
        · rw [dir88Mat_of_supp (by omega)]
          have hU9 : (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)).val
              = 9 := by
            rw [suppU_val]
            split_ifs with hm0
            · exfalso
              have hm0' : (i.val - 80) / 2 = 0 := hm0
              omega
            · rfl
          refine supp8_eq_zero_25_8 (n := ⟨i.val - 80, by omega⟩) ?_
          rintro ⟨hc1, -⟩
          have e1 := congrArg Fin.val hc1
          omega
  exact quad_extractC 34 35 80 81 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4 hw1 hw2 hw3 hw4
    hvan1 hvan2 g hg

/-- Extraction group EREbarR: coefficients 36, 37 vanish in any
    real relation, by the pivot `(9, 25)`. -/
theorem grpER_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (36 : Fin 88) = 0 ∧ g (37 : Fin 88) = 0 := by
  have hvA : dir88Mat (36 : Fin 88) (9 : I32) (25 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_lt4 (by decide)]
    exact hva_9_25
  have hvB : dir88Mat (37 : Fin 88) (9 : I32) (25 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_lt4 (by decide)]
    exact hvb_9_25
  have hvan : ∀ i : Fin 88, i ≠ (36 : Fin 88) → i ≠ (37 : Fin 88)
      → dir88Mat i (9 : I32) (25 : I32) = 0 := by
    intro i hi36 hi37
    have hne36 : i.val ≠ 36 := fin88_val_ne_of_ne (by norm_num) hi36
    have hne37 : i.val ≠ 37 := fin88_val_ne_of_ne (by norm_num) hi37
    have h22 : ∀ m : Fin 22, m.val ≠ (20 : Fin 22).val
        → m.val ≠ (21 : Fin 22).val → dirs22 m (9 : I32) (25 : I32) = 0 :=
      dirs22_hvan_val hvan_9_25
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_hvan h22
        (fun hk => show i.val ≠ 20 by have hk' : i.val < 10 := hk; omega)
        (fun hk => show i.val ≠ 21 by have hk' : i.val < 10 := hk; omega)
        (fun h10 => show i.val - 10 ≠ 20 by have h10' : 10 ≤ i.val := h10; omega)
        (fun h10 => show i.val - 10 ≠ 21 by have h10' : 10 ≤ i.val := h10; omega)
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_hvan h22
          (fun hk => show (i.val - 18) + 10 ≠ 20 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun hk => show (i.val - 18) + 10 ≠ 21 by have hk' : i.val - 18 < 8 := hk; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 20 by have h8' : 8 ≤ i.val - 18 := h8; omega)
          (fun h8 => show (i.val - 18) - 8 + 10 ≠ 21 by have h8' : 8 ≤ i.val - 18 := h8; omega)
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _ (show (i.val - 34) + 18 ≠ 20 by omega)
              (show (i.val - 34) + 18 ≠ 21 by omega)
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (9 : I32) (25 : I32) = 0
              exact eslot_van_9_25.1 _
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (9 : I32) (25 : I32) = 0
              exact eslot_van_9_25.2.1 _
        · rw [dir88Mat_of_supp (by omega)]
          exact eslot_van_9_25.2.2 _
  exact pair_extract88 9 25 36 37 (by decide) hvA hvB hvan g hg

/-- Extraction group E-0: coefficients 38, 39 (hermitian E-slot
    pair `(8, 10)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(24, 10)`
    and `(26, 8)`. -/
theorem grpE0_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (38 : Fin 88) = 0 ∧ g (39 : Fin 88) = 0
      ∧ g (62 : Fin 88) = 0 ∧ g (63 : Fin 88) = 0 := by
  have hv1 : dir88Mat (38 : Fin 88) (24 : I32) (10 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (0 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (10 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (39 : Fin 88) (24 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (1 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (10 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (62 : Fin 88) (24 : I32) (10 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (0 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (10 : I32) = 1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (63 : Fin 88) (24 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (1 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (10 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (38 : Fin 88) (26 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (0 : Fin 24) : Matrix I32 I32 ℂ) (26 : I32) (8 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (39 : Fin 88) (26 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (1 : Fin 24) : Matrix I32 I32 ℂ) (26 : I32) (8 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (62 : Fin 88) (26 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (0 : Fin 18) : Matrix I32 I32 ℂ) (26 : I32) (8 : I32) = -1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (63 : Fin 88) (26 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (1 : Fin 18) : Matrix I32 I32 ℂ) (26 : I32) (8 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (38 : Fin 88) → i ≠ (39 : Fin 88)
      → i ≠ (62 : Fin 88) → i ≠ (63 : Fin 88)
      → dir88Mat i (24 : I32) (10 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 38 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 39 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 62 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 63 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (24 : I32) (10 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (10 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 0 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (10 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 0 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (10 : Fin 16)) := by
            intro hc
            have hsp := suppUV_spec ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (38 : Fin 88) → i ≠ (39 : Fin 88)
      → i ≠ (62 : Fin 88) → i ≠ (63 : Fin 88)
      → dir88Mat i (26 : I32) (8 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 38 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 39 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 62 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 63 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (26 : I32) (8 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨10 + 16, by omega⟩ ⟨8, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 0 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 0 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (10 : Fin 16)) := by
            intro hc
            have hsp := suppUV_spec ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 24 10 26 8 38 39 62 63 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg

/-- Extraction group E-1: coefficients 38, 39 (hermitian E-slot
    pair `(8, 11)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(24, 11)`
    and `(27, 8)`. -/
theorem grpE1_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (40 : Fin 88) = 0 ∧ g (41 : Fin 88) = 0
      ∧ g (64 : Fin 88) = 0 ∧ g (65 : Fin 88) = 0 := by
  have hv1 : dir88Mat (40 : Fin 88) (24 : I32) (11 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (2 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (11 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (41 : Fin 88) (24 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (3 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (11 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (64 : Fin 88) (24 : I32) (11 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (2 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (11 : I32) = 1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (65 : Fin 88) (24 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (3 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (11 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (40 : Fin 88) (27 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (2 : Fin 24) : Matrix I32 I32 ℂ) (27 : I32) (8 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (41 : Fin 88) (27 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (3 : Fin 24) : Matrix I32 I32 ℂ) (27 : I32) (8 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (64 : Fin 88) (27 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (2 : Fin 18) : Matrix I32 I32 ℂ) (27 : I32) (8 : I32) = -1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (65 : Fin 88) (27 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (3 : Fin 18) : Matrix I32 I32 ℂ) (27 : I32) (8 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (40 : Fin 88) → i ≠ (41 : Fin 88)
      → i ≠ (64 : Fin 88) → i ≠ (65 : Fin 88)
      → dir88Mat i (24 : I32) (11 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 40 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 41 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 64 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 65 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (24 : I32) (11 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (11 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 1 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (11 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 1 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (11 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (40 : Fin 88) → i ≠ (41 : Fin 88)
      → i ≠ (64 : Fin 88) → i ≠ (65 : Fin 88)
      → dir88Mat i (27 : I32) (8 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 40 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 41 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 64 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 65 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (27 : I32) (8 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨11 + 16, by omega⟩ ⟨8, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 1 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 1 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (11 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 24 11 27 8 40 41 64 65 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-2: coefficients 38, 39 (hermitian E-slot
    pair `(8, 12)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(24, 12)`
    and `(28, 8)`. -/
theorem grpE2_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (42 : Fin 88) = 0 ∧ g (43 : Fin 88) = 0
      ∧ g (66 : Fin 88) = 0 ∧ g (67 : Fin 88) = 0 := by
  have hv1 : dir88Mat (42 : Fin 88) (24 : I32) (12 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (4 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (12 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (43 : Fin 88) (24 : I32) (12 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (5 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (12 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (66 : Fin 88) (24 : I32) (12 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (4 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (12 : I32) = 1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (67 : Fin 88) (24 : I32) (12 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (5 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (12 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (42 : Fin 88) (28 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (4 : Fin 24) : Matrix I32 I32 ℂ) (28 : I32) (8 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (43 : Fin 88) (28 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (5 : Fin 24) : Matrix I32 I32 ℂ) (28 : I32) (8 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (66 : Fin 88) (28 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (4 : Fin 18) : Matrix I32 I32 ℂ) (28 : I32) (8 : I32) = -1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (67 : Fin 88) (28 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (5 : Fin 18) : Matrix I32 I32 ℂ) (28 : I32) (8 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (42 : Fin 88) → i ≠ (43 : Fin 88)
      → i ≠ (66 : Fin 88) → i ≠ (67 : Fin 88)
      → dir88Mat i (24 : I32) (12 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 42 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 43 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 66 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 67 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (24 : I32) (12 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (12 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 2 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (12 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 2 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (12 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (42 : Fin 88) → i ≠ (43 : Fin 88)
      → i ≠ (66 : Fin 88) → i ≠ (67 : Fin 88)
      → dir88Mat i (28 : I32) (8 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 42 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 43 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 66 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 67 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (28 : I32) (8 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨12 + 16, by omega⟩ ⟨8, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (28 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 2 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (28 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 2 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (12 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 24 12 28 8 42 43 66 67 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-3: coefficients 38, 39 (hermitian E-slot
    pair `(8, 13)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(24, 13)`
    and `(29, 8)`. -/
theorem grpE3_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (44 : Fin 88) = 0 ∧ g (45 : Fin 88) = 0
      ∧ g (68 : Fin 88) = 0 ∧ g (69 : Fin 88) = 0 := by
  have hv1 : dir88Mat (44 : Fin 88) (24 : I32) (13 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (6 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (13 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (45 : Fin 88) (24 : I32) (13 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (7 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (13 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (68 : Fin 88) (24 : I32) (13 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (6 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (13 : I32) = 1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (69 : Fin 88) (24 : I32) (13 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (7 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (13 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (44 : Fin 88) (29 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (6 : Fin 24) : Matrix I32 I32 ℂ) (29 : I32) (8 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (45 : Fin 88) (29 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (7 : Fin 24) : Matrix I32 I32 ℂ) (29 : I32) (8 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (68 : Fin 88) (29 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (6 : Fin 18) : Matrix I32 I32 ℂ) (29 : I32) (8 : I32) = -1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (69 : Fin 88) (29 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (7 : Fin 18) : Matrix I32 I32 ℂ) (29 : I32) (8 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (44 : Fin 88) → i ≠ (45 : Fin 88)
      → i ≠ (68 : Fin 88) → i ≠ (69 : Fin 88)
      → dir88Mat i (24 : I32) (13 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 44 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 45 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 68 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 69 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (24 : I32) (13 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (13 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 3 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (13 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 3 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (13 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (44 : Fin 88) → i ≠ (45 : Fin 88)
      → i ≠ (68 : Fin 88) → i ≠ (69 : Fin 88)
      → dir88Mat i (29 : I32) (8 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 44 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 45 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 68 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 69 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (29 : I32) (8 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨13 + 16, by omega⟩ ⟨8, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (29 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 3 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (29 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 3 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (13 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 24 13 29 8 44 45 68 69 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-4: coefficients 38, 39 (hermitian E-slot
    pair `(8, 14)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(24, 14)`
    and `(30, 8)`. -/
theorem grpE4_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (46 : Fin 88) = 0 ∧ g (47 : Fin 88) = 0
      ∧ g (70 : Fin 88) = 0 ∧ g (71 : Fin 88) = 0 := by
  have hv1 : dir88Mat (46 : Fin 88) (24 : I32) (14 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (8 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (14 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (47 : Fin 88) (24 : I32) (14 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (9 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (14 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (70 : Fin 88) (24 : I32) (14 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (8 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (14 : I32) = 1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (71 : Fin 88) (24 : I32) (14 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (9 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (14 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (46 : Fin 88) (30 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (8 : Fin 24) : Matrix I32 I32 ℂ) (30 : I32) (8 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (47 : Fin 88) (30 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (9 : Fin 24) : Matrix I32 I32 ℂ) (30 : I32) (8 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (70 : Fin 88) (30 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (8 : Fin 18) : Matrix I32 I32 ℂ) (30 : I32) (8 : I32) = -1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (71 : Fin 88) (30 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (9 : Fin 18) : Matrix I32 I32 ℂ) (30 : I32) (8 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (46 : Fin 88) → i ≠ (47 : Fin 88)
      → i ≠ (70 : Fin 88) → i ≠ (71 : Fin 88)
      → dir88Mat i (24 : I32) (14 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 46 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 47 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 70 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 71 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (24 : I32) (14 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (14 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 4 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (14 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 4 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (14 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (46 : Fin 88) → i ≠ (47 : Fin 88)
      → i ≠ (70 : Fin 88) → i ≠ (71 : Fin 88)
      → dir88Mat i (30 : I32) (8 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 46 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 47 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 70 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 71 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (30 : I32) (8 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨14 + 16, by omega⟩ ⟨8, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (30 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 4 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (30 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 4 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (14 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 24 14 30 8 46 47 70 71 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-5: coefficients 38, 39 (hermitian E-slot
    pair `(8, 15)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(24, 15)`
    and `(31, 8)`. -/
theorem grpE5_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (48 : Fin 88) = 0 ∧ g (49 : Fin 88) = 0
      ∧ g (72 : Fin 88) = 0 ∧ g (73 : Fin 88) = 0 := by
  have hv1 : dir88Mat (48 : Fin 88) (24 : I32) (15 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (10 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (15 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (49 : Fin 88) (24 : I32) (15 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (11 : Fin 24) : Matrix I32 I32 ℂ) (24 : I32) (15 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (72 : Fin 88) (24 : I32) (15 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (10 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (15 : I32) = 1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (73 : Fin 88) (24 : I32) (15 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (11 : Fin 18) : Matrix I32 I32 ℂ) (24 : I32) (15 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (48 : Fin 88) (31 : I32) (8 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (10 : Fin 24) : Matrix I32 I32 ℂ) (31 : I32) (8 : I32) = 1
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (49 : Fin 88) (31 : I32) (8 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (11 : Fin 24) : Matrix I32 I32 ℂ) (31 : I32) (8 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (72 : Fin 88) (31 : I32) (8 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (10 : Fin 18) : Matrix I32 I32 ℂ) (31 : I32) (8 : I32) = -1
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (73 : Fin 88) (31 : I32) (8 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (11 : Fin 18) : Matrix I32 I32 ℂ) (31 : I32) (8 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (8 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (48 : Fin 88) → i ≠ (49 : Fin 88)
      → i ≠ (72 : Fin 88) → i ≠ (73 : Fin 88)
      → dir88Mat i (24 : I32) (15 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 48 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 49 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 72 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 73 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (24 : I32) (15 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (15 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 5 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (24 : I32) (15 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 5 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (15 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (48 : Fin 88) → i ≠ (49 : Fin 88)
      → i ≠ (72 : Fin 88) → i ≠ (73 : Fin 88)
      → dir88Mat i (31 : I32) (8 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 48 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 49 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 72 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 73 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (31 : I32) (8 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨15 + 16, by omega⟩ ⟨8, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (31 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 5 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (31 : I32) (8 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (8 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 5 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (8 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (15 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 24 15 31 8 48 49 72 73 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-6: coefficients 38, 39 (hermitian E-slot
    pair `(9, 10)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(25, 10)`
    and `(26, 9)`. -/
theorem grpE6_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (50 : Fin 88) = 0 ∧ g (51 : Fin 88) = 0
      ∧ g (74 : Fin 88) = 0 ∧ g (75 : Fin 88) = 0 := by
  have hv1 : dir88Mat (50 : Fin 88) (25 : I32) (10 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (12 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (10 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (51 : Fin 88) (25 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (13 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (10 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (74 : Fin 88) (25 : I32) (10 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (12 : Fin 18) : Matrix I32 I32 ℂ) (25 : I32) (10 : I32) = 1
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (75 : Fin 88) (25 : I32) (10 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (13 : Fin 18) : Matrix I32 I32 ℂ) (25 : I32) (10 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (50 : Fin 88) (26 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (12 : Fin 24) : Matrix I32 I32 ℂ) (26 : I32) (9 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (51 : Fin 88) (26 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (13 : Fin 24) : Matrix I32 I32 ℂ) (26 : I32) (9 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (74 : Fin 88) (26 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (12 : Fin 18) : Matrix I32 I32 ℂ) (26 : I32) (9 : I32) = -1
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (75 : Fin 88) (26 : I32) (9 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (13 : Fin 18) : Matrix I32 I32 ℂ) (26 : I32) (9 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (10 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (50 : Fin 88) → i ≠ (51 : Fin 88)
      → i ≠ (74 : Fin 88) → i ≠ (75 : Fin 88)
      → dir88Mat i (25 : I32) (10 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 50 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 51 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 74 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 75 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (25 : I32) (10 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (10 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 6 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (10 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 6 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (10 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (50 : Fin 88) → i ≠ (51 : Fin 88)
      → i ≠ (74 : Fin 88) → i ≠ (75 : Fin 88)
      → dir88Mat i (26 : I32) (9 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 50 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 51 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 74 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 75 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (26 : I32) (9 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨10 + 16, by omega⟩ ⟨9, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 6 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (26 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (10 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 6 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (10 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 25 10 26 9 50 51 74 75 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-7: coefficients 38, 39 (hermitian E-slot
    pair `(9, 11)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(25, 11)`
    and `(27, 9)`. -/
theorem grpE7_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (52 : Fin 88) = 0 ∧ g (53 : Fin 88) = 0
      ∧ g (76 : Fin 88) = 0 ∧ g (77 : Fin 88) = 0 := by
  have hv1 : dir88Mat (52 : Fin 88) (25 : I32) (11 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (14 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (11 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (53 : Fin 88) (25 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (15 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (11 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (76 : Fin 88) (25 : I32) (11 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (14 : Fin 18) : Matrix I32 I32 ℂ) (25 : I32) (11 : I32) = 1
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (77 : Fin 88) (25 : I32) (11 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (15 : Fin 18) : Matrix I32 I32 ℂ) (25 : I32) (11 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (52 : Fin 88) (27 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (14 : Fin 24) : Matrix I32 I32 ℂ) (27 : I32) (9 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (53 : Fin 88) (27 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (15 : Fin 24) : Matrix I32 I32 ℂ) (27 : I32) (9 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (76 : Fin 88) (27 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (14 : Fin 18) : Matrix I32 I32 ℂ) (27 : I32) (9 : I32) = -1
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (77 : Fin 88) (27 : I32) (9 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (15 : Fin 18) : Matrix I32 I32 ℂ) (27 : I32) (9 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (11 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (52 : Fin 88) → i ≠ (53 : Fin 88)
      → i ≠ (76 : Fin 88) → i ≠ (77 : Fin 88)
      → dir88Mat i (25 : I32) (11 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 52 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 53 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 76 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 77 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (25 : I32) (11 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (11 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 7 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (11 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 7 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (11 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (52 : Fin 88) → i ≠ (53 : Fin 88)
      → i ≠ (76 : Fin 88) → i ≠ (77 : Fin 88)
      → dir88Mat i (27 : I32) (9 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 52 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 53 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 76 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 77 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (27 : I32) (9 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨11 + 16, by omega⟩ ⟨9, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 7 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (27 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (11 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 7 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (11 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 25 11 27 9 52 53 76 77 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-8: coefficients 38, 39 (hermitian E-slot
    pair `(9, 12)`) and 62, 63 (its anti-hermitian partners)
    vanish in any real relation, by the cross entries `(25, 12)`
    and `(28, 9)`. -/
theorem grpE8_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (54 : Fin 88) = 0 ∧ g (55 : Fin 88) = 0
      ∧ g (78 : Fin 88) = 0 ∧ g (79 : Fin 88) = 0 := by
  have hv1 : dir88Mat (54 : Fin 88) (25 : I32) (12 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (16 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (12 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (55 : Fin 88) (25 : I32) (12 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (17 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (12 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (78 : Fin 88) (25 : I32) (12 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (16 : Fin 18) : Matrix I32 I32 ℂ) (25 : I32) (12 : I32) = 1
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (79 : Fin 88) (25 : I32) (12 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (17 : Fin 18) : Matrix I32 I32 ℂ) (25 : I32) (12 : I32)
      = Complex.I
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (54 : Fin 88) (28 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (16 : Fin 24) : Matrix I32 I32 ℂ) (28 : I32) (9 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (55 : Fin 88) (28 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (17 : Fin 24) : Matrix I32 I32 ℂ) (28 : I32) (9 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (78 : Fin 88) (28 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (16 : Fin 18) : Matrix I32 I32 ℂ) (28 : I32) (9 : I32) = -1
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (79 : Fin 88) (28 : I32) (9 : I32) = -Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_anti (by decide)]
    show (exAntiDir (17 : Fin 18) : Matrix I32 I32 ℂ) (28 : I32) (9 : I32)
      = -Complex.I
    exact (exAntiDir_pivot (u := (9 : Fin 16)) (v := (12 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (54 : Fin 88) → i ≠ (55 : Fin 88)
      → i ≠ (78 : Fin 88) → i ≠ (79 : Fin 88)
      → dir88Mat i (25 : I32) (12 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 54 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 55 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 78 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 79 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (25 : I32) (12 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (12 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 8 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (12 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 8 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (12 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (54 : Fin 88) → i ≠ (55 : Fin 88)
      → i ≠ (78 : Fin 88) → i ≠ (79 : Fin 88)
      → dir88Mat i (28 : I32) (9 : I32) = 0 := by
    intro i hi38 hi39 hi62 hi63
    have hne38 : i.val ≠ 54 := fin88_val_ne_of_ne (by norm_num) hi38
    have hne39 : i.val ≠ 55 := fin88_val_ne_of_ne (by norm_num) hi39
    have hne62 : i.val ≠ 78 := fin88_val_ne_of_ne (by norm_num) hi62
    have hne63 : i.val ≠ 79 := fin88_val_ne_of_ne (by norm_num) hi63
    have h22 : ∀ m : Fin 22, dirs22 m (28 : I32) (9 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨12 + 16, by omega⟩ ⟨9, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (28 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 8 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (28 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (12 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 8 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (12 : Fin 16)) := by
            intro hc
            have e1 := congrArg Fin.val hc.1
            have e2 := congrArg Fin.val hc.2
            rw [suppU_val] at e1
            rw [suppV_val] at e2
            split_ifs at e1 e2 <;> omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 25 12 28 9 54 55 78 79 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-9: coefficients 56, 57 (hermitian E-slot
    pair `(9, 13)`) and 82, 83 (its supplement partners) vanish
    in any real relation, by the cross entries `(25, 13)` and
    `(29, 9)`. -/
theorem grpE9_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (56 : Fin 88) = 0 ∧ g (57 : Fin 88) = 0
      ∧ g (82 : Fin 88) = 0 ∧ g (83 : Fin 88) = 0 := by
  have hv1 : dir88Mat (56 : Fin 88) (25 : I32) (13 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (18 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (13 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (57 : Fin 88) (25 : I32) (13 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (19 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (13 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (82 : Fin 88) (25 : I32) (13 : I32) = 1 := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (2 : Fin 8) : Matrix I32 I32 ℂ) (25 : I32)
      (13 : I32) = 1
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (83 : Fin 88) (25 : I32) (13 : I32) = Complex.I := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (3 : Fin 8) : Matrix I32 I32 ℂ) (25 : I32)
      (13 : I32) = Complex.I
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (56 : Fin 88) (29 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (18 : Fin 24) : Matrix I32 I32 ℂ) (29 : I32) (9 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (57 : Fin 88) (29 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (19 : Fin 24) : Matrix I32 I32 ℂ) (29 : I32) (9 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (82 : Fin 88) (29 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (2 : Fin 8) : Matrix I32 I32 ℂ) (29 : I32)
      (9 : I32) = -1
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (83 : Fin 88) (29 : I32) (9 : I32) = -Complex.I := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (3 : Fin 8) : Matrix I32 I32 ℂ) (29 : I32)
      (9 : I32) = -Complex.I
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (13 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (56 : Fin 88) → i ≠ (57 : Fin 88)
      → i ≠ (82 : Fin 88) → i ≠ (83 : Fin 88)
      → dir88Mat i (25 : I32) (13 : I32) = 0 := by
    intro i hi56 hi57 hi82 hi83
    have hne56 : i.val ≠ 56 := fin88_val_ne_of_ne (by norm_num) hi56
    have hne57 : i.val ≠ 57 := fin88_val_ne_of_ne (by norm_num) hi57
    have hne82 : i.val ≠ 82 := fin88_val_ne_of_ne (by norm_num) hi82
    have hne83 : i.val ≠ 83 := fin88_val_ne_of_ne (by norm_num) hi83
    have h22 : ∀ m : Fin 22, dirs22 m (25 : I32) (13 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (13 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 9 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (13 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 9 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (13 : Fin 16)) := by
            intro hc
            have hpm := supp_pair_eq_of
              (by have h1 := (⟨i.val - 80, by omega⟩ : Fin 8).isLt; omega)
              (by decide) (by decide) hc.1 hc.2
            have hpm' : (i.val - 80) / 2 = 1 := hpm
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (56 : Fin 88) → i ≠ (57 : Fin 88)
      → i ≠ (82 : Fin 88) → i ≠ (83 : Fin 88)
      → dir88Mat i (29 : I32) (9 : I32) = 0 := by
    intro i hi56 hi57 hi82 hi83
    have hne56 : i.val ≠ 56 := fin88_val_ne_of_ne (by norm_num) hi56
    have hne57 : i.val ≠ 57 := fin88_val_ne_of_ne (by norm_num) hi57
    have hne82 : i.val ≠ 82 := fin88_val_ne_of_ne (by norm_num) hi82
    have hne83 : i.val ≠ 83 := fin88_val_ne_of_ne (by norm_num) hi83
    have h22 : ∀ m : Fin 22, dirs22 m (29 : I32) (9 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨13 + 16, by omega⟩ ⟨9, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (29 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 9 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (29 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (13 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 9 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (13 : Fin 16)) := by
            intro hc
            have hpm := supp_pair_eq_of
              (by have h1 := (⟨i.val - 80, by omega⟩ : Fin 8).isLt; omega)
              (by decide) (by decide) hc.1 hc.2
            have hpm' : (i.val - 80) / 2 = 1 := hpm
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 25 13 29 9 56 57 82 83 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg

/-- Extraction group E-10: coefficients 56, 57 (hermitian E-slot
    pair `(9, 14)`) and 82, 83 (its supplement partners) vanish
    in any real relation, by the cross entries `(25, 14)` and
    `(30, 9)`. -/
theorem grpE10_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (58 : Fin 88) = 0 ∧ g (59 : Fin 88) = 0
      ∧ g (84 : Fin 88) = 0 ∧ g (85 : Fin 88) = 0 := by
  have hv1 : dir88Mat (58 : Fin 88) (25 : I32) (14 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (20 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (14 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (59 : Fin 88) (25 : I32) (14 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (21 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (14 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (84 : Fin 88) (25 : I32) (14 : I32) = 1 := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (4 : Fin 8) : Matrix I32 I32 ℂ) (25 : I32)
      (14 : I32) = 1
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (85 : Fin 88) (25 : I32) (14 : I32) = Complex.I := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (5 : Fin 8) : Matrix I32 I32 ℂ) (25 : I32)
      (14 : I32) = Complex.I
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (58 : Fin 88) (30 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (20 : Fin 24) : Matrix I32 I32 ℂ) (30 : I32) (9 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (59 : Fin 88) (30 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (21 : Fin 24) : Matrix I32 I32 ℂ) (30 : I32) (9 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (84 : Fin 88) (30 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (4 : Fin 8) : Matrix I32 I32 ℂ) (30 : I32)
      (9 : I32) = -1
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (85 : Fin 88) (30 : I32) (9 : I32) = -Complex.I := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (5 : Fin 8) : Matrix I32 I32 ℂ) (30 : I32)
      (9 : I32) = -Complex.I
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (14 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (58 : Fin 88) → i ≠ (59 : Fin 88)
      → i ≠ (84 : Fin 88) → i ≠ (85 : Fin 88)
      → dir88Mat i (25 : I32) (14 : I32) = 0 := by
    intro i hi56 hi57 hi82 hi83
    have hne56 : i.val ≠ 58 := fin88_val_ne_of_ne (by norm_num) hi56
    have hne57 : i.val ≠ 59 := fin88_val_ne_of_ne (by norm_num) hi57
    have hne82 : i.val ≠ 84 := fin88_val_ne_of_ne (by norm_num) hi82
    have hne83 : i.val ≠ 85 := fin88_val_ne_of_ne (by norm_num) hi83
    have h22 : ∀ m : Fin 22, dirs22 m (25 : I32) (14 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (14 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 10 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (14 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 10 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (14 : Fin 16)) := by
            intro hc
            have hpm := supp_pair_eq_of
              (by have h1 := (⟨i.val - 80, by omega⟩ : Fin 8).isLt; omega)
              (by decide) (by decide) hc.1 hc.2
            have hpm' : (i.val - 80) / 2 = 2 := hpm
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (58 : Fin 88) → i ≠ (59 : Fin 88)
      → i ≠ (84 : Fin 88) → i ≠ (85 : Fin 88)
      → dir88Mat i (30 : I32) (9 : I32) = 0 := by
    intro i hi56 hi57 hi82 hi83
    have hne56 : i.val ≠ 58 := fin88_val_ne_of_ne (by norm_num) hi56
    have hne57 : i.val ≠ 59 := fin88_val_ne_of_ne (by norm_num) hi57
    have hne82 : i.val ≠ 84 := fin88_val_ne_of_ne (by norm_num) hi82
    have hne83 : i.val ≠ 85 := fin88_val_ne_of_ne (by norm_num) hi83
    have h22 : ∀ m : Fin 22, dirs22 m (30 : I32) (9 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨14 + 16, by omega⟩ ⟨9, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (30 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 10 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (30 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (14 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 10 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (14 : Fin 16)) := by
            intro hc
            have hpm := supp_pair_eq_of
              (by have h1 := (⟨i.val - 80, by omega⟩ : Fin 8).isLt; omega)
              (by decide) (by decide) hc.1 hc.2
            have hpm' : (i.val - 80) / 2 = 2 := hpm
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 25 14 30 9 58 59 84 85 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-- Extraction group E-11: coefficients 56, 57 (hermitian E-slot
    pair `(9, 15)`) and 82, 83 (its supplement partners) vanish
    in any real relation, by the cross entries `(25, 15)` and
    `(31, 9)`. -/
theorem grpE11_coeffs (g : Fin 88 → ℝ)
    (hg : ∑ i, g i • dir88Mat i = 0) :
    g (60 : Fin 88) = 0 ∧ g (61 : Fin 88) = 0
      ∧ g (86 : Fin 88) = 0 ∧ g (87 : Fin 88) = 0 := by
  have hv1 : dir88Mat (60 : Fin 88) (25 : I32) (15 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (22 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (15 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv2 : dir88Mat (61 : Fin 88) (25 : I32) (15 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (23 : Fin 24) : Matrix I32 I32 ℂ) (25 : I32) (15 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv3 : dir88Mat (86 : Fin 88) (25 : I32) (15 : I32) = 1 := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (6 : Fin 8) : Matrix I32 I32 ℂ) (25 : I32)
      (15 : I32) = 1
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hv4 : dir88Mat (87 : Fin 88) (25 : I32) (15 : I32) = Complex.I := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (7 : Fin 8) : Matrix I32 I32 ℂ) (25 : I32)
      (15 : I32) = Complex.I
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).1
  have hw1 : dir88Mat (60 : Fin 88) (31 : I32) (9 : I32) = 1 := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (22 : Fin 24) : Matrix I32 I32 ℂ) (31 : I32) (9 : I32) = 1
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw2 : dir88Mat (61 : Fin 88) (31 : I32) (9 : I32) = Complex.I := by
    rw [dir88Mat_of_exotic (by decide) (by decide),
      distinct46_of_herm (by decide) (by decide)]
    show (exHermDir (23 : Fin 24) : Matrix I32 I32 ℂ) (31 : I32) (9 : I32)
      = Complex.I
    exact (exHermDir_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw3 : dir88Mat (86 : Fin 88) (31 : I32) (9 : I32) = -1 := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (6 : Fin 8) : Matrix I32 I32 ℂ) (31 : I32)
      (9 : I32) = -1
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hw4 : dir88Mat (87 : Fin 88) (31 : I32) (9 : I32) = -Complex.I := by
    rw [dir88Mat_of_supp (by decide)]
    show (pairDirExoticSupp8 (7 : Fin 8) : Matrix I32 I32 ℂ) (31 : I32)
      (9 : I32) = -Complex.I
    exact (supp8_pivot (u := (9 : Fin 16)) (v := (15 : Fin 16))
      (by decide) (by decide) (by decide) (by decide)).2
  have hvan1 : ∀ i : Fin 88, i ≠ (60 : Fin 88) → i ≠ (61 : Fin 88)
      → i ≠ (86 : Fin 88) → i ≠ (87 : Fin 88)
      → dir88Mat i (25 : I32) (15 : I32) = 0 := by
    intro i hi56 hi57 hi82 hi83
    have hne56 : i.val ≠ 60 := fin88_val_ne_of_ne (by norm_num) hi56
    have hne57 : i.val ≠ 61 := fin88_val_ne_of_ne (by norm_num) hi57
    have hne82 : i.val ≠ 86 := fin88_val_ne_of_ne (by norm_num) hi82
    have hne83 : i.val ≠ 87 := fin88_val_ne_of_ne (by norm_num) hi83
    have h22 : ∀ m : Fin 22, dirs22 m (25 : I32) (15 : I32) = 0 :=
      fun m => dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (15 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 11 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).1
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (25 : I32) (15 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 11 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).1
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (15 : Fin 16)) := by
            intro hc
            have hpm := supp_pair_eq_of
              (by have h1 := (⟨i.val - 80, by omega⟩ : Fin 8).isLt; omega)
              (by decide) (by decide) hc.1 hc.2
            have hpm' : (i.val - 80) / 2 = 3 := hpm
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).1
  have hvan2 : ∀ i : Fin 88, i ≠ (60 : Fin 88) → i ≠ (61 : Fin 88)
      → i ≠ (86 : Fin 88) → i ≠ (87 : Fin 88)
      → dir88Mat i (31 : I32) (9 : I32) = 0 := by
    intro i hi56 hi57 hi82 hi83
    have hne56 : i.val ≠ 60 := fin88_val_ne_of_ne (by norm_num) hi56
    have hne57 : i.val ≠ 61 := fin88_val_ne_of_ne (by norm_num) hi57
    have hne82 : i.val ≠ 86 := fin88_val_ne_of_ne (by norm_num) hi82
    have hne83 : i.val ≠ 87 := fin88_val_ne_of_ne (by norm_num) hi83
    have h22 : ∀ m : Fin 22, dirs22 m (31 : I32) (9 : I32) = 0 :=
      fun m => by
        show dirs22 m ⟨15 + 16, by omega⟩ ⟨9, by omega⟩ = 0
        rw [dirs22_apply_em m (by omega) (by omega)]
        exact dirs22_eq_zero_of_newpivot88 (by decide) (by decide) m
    by_cases h18 : i.val < 18
    · rw [dir88Mat_of_lt18 h18]
      exact sm18_eq_zero_of_all h22 _
    · by_cases h34 : i.val < 34
      · rw [dir88Mat_of_flip (by omega) h34]
        exact flip16_eq_zero_of_all h22 _
      · by_cases h80 : i.val < 80
        · rw [dir88Mat_of_exotic (by omega) h80]
          by_cases h38 : i.val < 38
          · rw [distinct46_of_lt4 (show i.val - 34 < 4 by omega)]
            exact h22 _
          · by_cases h62 : i.val < 62
            · rw [distinct46_of_herm (show 4 ≤ i.val - 34 by omega)
                (show i.val - 34 < 28 by omega)]
              show (exHermDir ⟨i.val - 38, by omega⟩ : Matrix I32 I32 ℂ)
                (31 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 38, by omega⟩ : Fin 24).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 38) / 2 = 11 := hpm
                omega
              exact (exHermDir_eq_zero_of_ne (by decide) (by decide) hne).2
            · rw [distinct46_of_anti (show 28 ≤ i.val - 34 by omega)]
              show (exAntiDir ⟨i.val - 62, by omega⟩ : Matrix I32 I32 ℂ)
                (31 : I32) (9 : I32) = 0
              have hne : ¬ (exMajU ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (9 : Fin 16)
                ∧ exMajV ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2)
                  = (15 : Fin 16)) := by
                intro hc
                have hpm := exMaj_pair_eq_of
                  (show ((⟨i.val - 62, by omega⟩ : Fin 18).val / 2) < 12
                    by omega) (by decide) (by decide) hc.1 hc.2
                have hpm' : (i.val - 62) / 2 = 11 := hpm
                omega
              exact (exAntiDir_eq_zero_of_ne (by decide) (by decide) hne).2
        · rw [dir88Mat_of_supp (by omega)]
          have hne : ¬ (suppU ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (9 : Fin 16)
            ∧ suppV ((⟨i.val - 80, by omega⟩ : Fin 8).val / 2)
              = (15 : Fin 16)) := by
            intro hc
            have hpm := supp_pair_eq_of
              (by have h1 := (⟨i.val - 80, by omega⟩ : Fin 8).isLt; omega)
              (by decide) (by decide) hc.1 hc.2
            have hpm' : (i.val - 80) / 2 = 3 := hpm
            omega
          exact (supp8_eq_zero_of_ne (by decide) (by decide) hne).2
  exact quad_extractB 25 15 31 9 60 61 86 87 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv1 hv2 hv3 hv4
    hw1 hw2 hw3 hw4 hvan1 hvan2 g hg


/-! ## 10. Independence assembly -/

/-- The 88 matrices `dir88Mat` are linearly independent over the
    reals: every coefficient in a real relation vanishes, by the
    23 extraction groups. -/
theorem dir88Mat_independent : LinearIndependent ℝ dir88Mat := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · exact (grpSM0_coeffs g hg).1
  · exact (grpSM0_coeffs g hg).2.1
  · exact (grpSM1_coeffs g hg).1
  · exact (grpSM1_coeffs g hg).2.1
  · exact (grpSM2_coeffs g hg).1
  · exact (grpSM2_coeffs g hg).2.1
  · exact (grpSM3_coeffs g hg).1
  · exact (grpSM3_coeffs g hg).2.1
  · exact (grpYR_coeffs g hg).1
  · exact (grpYR_coeffs g hg).2
  · exact (grpSM0_coeffs g hg).2.2.1
  · exact (grpSM0_coeffs g hg).2.2.2
  · exact (grpSM1_coeffs g hg).2.2.1
  · exact (grpSM1_coeffs g hg).2.2.2
  · exact (grpSM2_coeffs g hg).2.2.1
  · exact (grpSM2_coeffs g hg).2.2.2
  · exact (grpSM3_coeffs g hg).2.2.1
  · exact (grpSM3_coeffs g hg).2.2.2
  · exact (grpFL0_coeffs g hg).1
  · exact (grpFL0_coeffs g hg).2.1
  · exact (grpFL1_coeffs g hg).1
  · exact (grpFL1_coeffs g hg).2.1
  · exact (grpFL2_coeffs g hg).1
  · exact (grpFL2_coeffs g hg).2.1
  · exact (grpFL3_coeffs g hg).1
  · exact (grpFL3_coeffs g hg).2.1
  · exact (grpFL0_coeffs g hg).2.2.1
  · exact (grpFL0_coeffs g hg).2.2.2
  · exact (grpFL1_coeffs g hg).2.2.1
  · exact (grpFL1_coeffs g hg).2.2.2
  · exact (grpFL2_coeffs g hg).2.2.1
  · exact (grpFL2_coeffs g hg).2.2.2
  · exact (grpFL3_coeffs g hg).2.2.1
  · exact (grpFL3_coeffs g hg).2.2.2
  · exact (grpG10_coeffs g hg).1
  · exact (grpG10_coeffs g hg).2.1
  · exact (grpER_coeffs g hg).1
  · exact (grpER_coeffs g hg).2
  · exact (grpE0_coeffs g hg).1
  · exact (grpE0_coeffs g hg).2.1
  · exact (grpE1_coeffs g hg).1
  · exact (grpE1_coeffs g hg).2.1
  · exact (grpE2_coeffs g hg).1
  · exact (grpE2_coeffs g hg).2.1
  · exact (grpE3_coeffs g hg).1
  · exact (grpE3_coeffs g hg).2.1
  · exact (grpE4_coeffs g hg).1
  · exact (grpE4_coeffs g hg).2.1
  · exact (grpE5_coeffs g hg).1
  · exact (grpE5_coeffs g hg).2.1
  · exact (grpE6_coeffs g hg).1
  · exact (grpE6_coeffs g hg).2.1
  · exact (grpE7_coeffs g hg).1
  · exact (grpE7_coeffs g hg).2.1
  · exact (grpE8_coeffs g hg).1
  · exact (grpE8_coeffs g hg).2.1
  · exact (grpE9_coeffs g hg).1
  · exact (grpE9_coeffs g hg).2.1
  · exact (grpE10_coeffs g hg).1
  · exact (grpE10_coeffs g hg).2.1
  · exact (grpE11_coeffs g hg).1
  · exact (grpE11_coeffs g hg).2.1
  · exact (grpE0_coeffs g hg).2.2.1
  · exact (grpE0_coeffs g hg).2.2.2
  · exact (grpE1_coeffs g hg).2.2.1
  · exact (grpE1_coeffs g hg).2.2.2
  · exact (grpE2_coeffs g hg).2.2.1
  · exact (grpE2_coeffs g hg).2.2.2
  · exact (grpE3_coeffs g hg).2.2.1
  · exact (grpE3_coeffs g hg).2.2.2
  · exact (grpE4_coeffs g hg).2.2.1
  · exact (grpE4_coeffs g hg).2.2.2
  · exact (grpE5_coeffs g hg).2.2.1
  · exact (grpE5_coeffs g hg).2.2.2
  · exact (grpE6_coeffs g hg).2.2.1
  · exact (grpE6_coeffs g hg).2.2.2
  · exact (grpE7_coeffs g hg).2.2.1
  · exact (grpE7_coeffs g hg).2.2.2
  · exact (grpE8_coeffs g hg).2.2.1
  · exact (grpE8_coeffs g hg).2.2.2
  · exact (grpG10_coeffs g hg).2.2.1
  · exact (grpG10_coeffs g hg).2.2.2
  · exact (grpE9_coeffs g hg).2.2.1
  · exact (grpE9_coeffs g hg).2.2.2
  · exact (grpE10_coeffs g hg).2.2.1
  · exact (grpE10_coeffs g hg).2.2.2
  · exact (grpE11_coeffs g hg).2.2.1
  · exact (grpE11_coeffs g hg).2.2.2

/-- The 88 directions `dir88` in `PairSpace` are linearly
    independent over the reals (transport of the matrix
    independence along the subtype coercion). -/
theorem dir88_independent : LinearIndependent ℝ dir88 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, g j • dir88Mat j = 0 := by
    have h := congrArg (⇑(Submodule.subtype PairSpace)) hg
    simp only [map_sum, map_smul, LinearMap.zero_apply,
      Submodule.coe_subtype] at h
    exact h
  exact (Fintype.linearIndependent_iff.mp dir88Mat_independent) g hg' i

/-- Lower bound: the real finrank of `PairSpace` is at least 88. -/
theorem finrank_ge_88 : 88 ≤ Module.finrank ℝ PairSpace := by
  have h := dir88_independent.fintype_card_le_finrank
  simpa using h

end ThetLogos
