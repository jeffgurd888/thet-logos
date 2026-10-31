import ThetLogos.Census96PairSpace
import ThetLogos.Census96PairDirections

/-!
# ThetLogos.Census96PairExotic - C96-3a3: pair directions III (exotic)

Continuation of C96-3a / C96-3a2 (lane 2 of the Census-96 line; pack
`pack-c96-3a3.md`). The frozen interfaces of C96-3a (`PairSpace`,
`mem_pairSpace_iff`, `pairDir22`, `pairDirSM`, `pairDirExotic`,
`dir88Of`) and C96-3a2 (`IsAntiAdm32`, `pairSpace_of_isAntiAdm32`,
`aRSign`, `isAntiAdm32_aRSign_conj`, `pairDirSM18`, `pairDirFlip16`)
are imported and untouched; every name defined here is new.

## What this module does

It completes the exotic direction family to 54:
`pairDirExotic54 : Fin 54 -> PairSpace`, whose first 12 indices are
C96-3a's landed `pairDirExotic` and whose remaining 42 indices are
the exotic Majorana E-slot pair patterns, in two segments:

* **New hermitian patterns (24).** For each folded E-slot coordinate
  `(u, v)` with `u` in `{8, 9}` and `v` in `{10, ..., 15}`, the
  hermitian single-coordinate direction `exHermMat u v z`
  (`z = 1` real part, `z = Complex.I` imaginary part), an element of
  `PairSpace` through the hermitian embedding
  `pairSpace_of_isAdm32`. These are the pair analogues of the
  one-generation exotic Majorana directions at the same folded
  coordinates.
* **Anti patterns (18).** For the folded coordinate pairs
  `(8, v)` with `v` in `{10, ..., 15}` and `(9, 10)`, `(9, 11)`,
  `(9, 12)`, the antisymmetric folded patterns `exAntiMat u v z`
  (`z = 1`, `z = Complex.I`): non-hermitian elements of `PairSpace`
  with `(exAntiMat u v z).conjTranspose = - exAntiMat u v z`,
  proved directly through `mem_pairSpace_iff`. (The S-conjugation
  transport of C96-3a2 discharges no E-slot pattern: every E-slot
  support entry joins equal partner twists, since both folded
  coordinates are `>= 8`; the anti directions of the E-slot are the
  antisymmetric folded patterns instead.)

Named remainder (a stall seam, not a kill): the antisymmetric
folded patterns at the coordinate pairs `(8, 9)`, `(9, 13)`,
`(9, 14)`, `(9, 15)` (real and imaginary parts, 8 directions) are
NOT included in `pairDirExotic54`; the order-one theorems below
cover the `(9, 13..15)` pairs as well, so they are available to
any future re-indexing, but the frozen segment size 54 is met
without them.

All 42 new directions rest on one generic order-one theorem,
`exPairMat_orderOne`: a single-coordinate folded pair pattern
`exPairMat u v z = admBlockMatOf (delta at (u, v))` at an E-slot
coordinate satisfies `OrderOneHolds`. Membership of the hermitian
and anti combinations then follows from additivity of the order-one
condition and the conjugate-transpose formula
`exPairMat_conjTranspose : (exPairMat u v z).conjTranspose
= exPairMat v u z`.

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

/-! ## 1. Single-coordinate folded pair patterns -/

/-- The single-coordinate folded cross-block: value `z` at the
    folded coordinate `(u, v)`, zero elsewhere. -/
def exPairZ (u v : Fin 16) (z : ℂ) : Fin 16 × Fin 16 → ℂ :=
  fun p => if p = (u, v) then z else 0

theorem exPairZ_apply (u v : Fin 16) (z : ℂ) (a b : Fin 16) :
    exPairZ u v z (a, b) = if (a = u ∧ b = v) then z else 0 := by
  unfold exPairZ
  by_cases h : (a, b) = (u, v)
  · rw [if_pos h]
    have h1 : a = u := congrArg Prod.fst h
    have h2 : b = v := congrArg Prod.snd h
    rw [if_pos ⟨h1, h2⟩]
  · rw [if_neg h]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext h1 h2)

/-- **The single-coordinate folded pair pattern** at `(u, v)` with
    value `z`: the block-admissible matrix `admBlockMatOf` of the
    single-coordinate cross-block. Block-admissibility is the landed
    `admBlockMatOf_isAdmBlock`. -/
noncomputable def exPairMat (u v : Fin 16) (z : ℂ) : Matrix I32 I32 ℂ :=
  admBlockMatOf (exPairZ u v z)

theorem exPairMat_apply (u v : Fin 16) (z : ℂ) (i j : I32) :
    exPairMat u v z i j =
      if gSign i = 1 then
        (if gSign j = 1 then 0 else
          if (acoord i = u ∧ acoord j = v) then z else 0)
      else
        (if gSign j = 1 then
          if (acoord i = u ∧ acoord j = v) then star z else 0
          else 0) := by
  unfold exPairMat
  rw [admBlockMatOf_apply, exPairZ_apply]
  split_ifs <;> simp_all

/-- A single-coordinate pair pattern vanishes at any entry whose
    folded coordinate pair is not `(u, v)`. -/
theorem exPairMat_eq_zero_of {u v : Fin 16} (z : ℂ) {i j : I32}
    (h : ¬ (acoord i = u ∧ acoord j = v)) : exPairMat u v z i j = 0 := by
  rw [exPairMat_apply]
  split_ifs <;> simp_all

/-- Block-admissibility of a single-coordinate pair pattern. -/
theorem exPairMat_isAdmBlock (u v : Fin 16) (z : ℂ) :
    IsAdmBlock (exPairMat u v z) :=
  admBlockMatOf_isAdmBlock _

/-- Support of a single-coordinate pair pattern: a nonzero entry has
    folded coordinates exactly `(u, v)` and joins opposite grading
    signs. -/
theorem exPairMat_ne_zero {u v : Fin 16} {z : ℂ} {i j : I32}
    (h : exPairMat u v z i j ≠ 0) :
    acoord i = u ∧ acoord j = v ∧ gSign i ≠ gSign j := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    exact h (exPairMat_eq_zero_of z (fun hh => hc hh.1))
  · by_contra hc
    exact h (exPairMat_eq_zero_of z (fun hh => hc hh.2))
  · intro hgg
    exact h (gammaOdd_entry_eq_zero_of_gSign_eq _
      (exPairMat_isAdmBlock u v z).1 hgg)

/-- **Conjugate-transpose of a single-coordinate pair pattern:**
    transposition swaps the folded coordinates and does NOT star
    the value (the two stars of the pair parameterization cancel):
    `(exPairMat u v z).conjTranspose = exPairMat v u z`. -/
theorem exPairMat_conjTranspose (u v : Fin 16) (z : ℂ) :
    (exPairMat u v z).conjTranspose = exPairMat v u z := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [exPairMat_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all [star_star]

/-! ## 2. Hermitian and anti combinations of pair patterns -/

/-- The order-one condition is closed under subtraction (from the
    landed `orderOneHolds_add` and `orderOneHolds_neg`). -/
theorem orderOneHolds_sub {M N : Matrix I32 I32 ℂ}
    (hM : OrderOneHolds M) (hN : OrderOneHolds N) :
    OrderOneHolds (M - N) := by
  rw [sub_eq_add_neg]
  exact orderOneHolds_add hM (orderOneHolds_neg hN)

/-- **The hermitian E-slot pattern** at folded coordinate `(u, v)`:
    the symmetric combination of the two single-coordinate pair
    patterns. -/
noncomputable def exHermMat (u v : Fin 16) (z : ℂ) : Matrix I32 I32 ℂ :=
  exPairMat u v z + exPairMat v u z

theorem exHermMat_conjTranspose (u v : Fin 16) (z : ℂ) :
    (exHermMat u v z).conjTranspose = exHermMat u v z := by
  unfold exHermMat
  rw [Matrix.conjTranspose_add, exPairMat_conjTranspose,
    exPairMat_conjTranspose, add_comm]

theorem exHermMat_isAdmBlock (u v : Fin 16) (z : ℂ) :
    IsAdmBlock (exHermMat u v z) :=
  AdmBlock.add_mem (exPairMat_isAdmBlock u v z)
    (exPairMat_isAdmBlock v u z)

/-- A hermitian E-slot pattern is one-generation admissible: the
    transpose-form J-condition is the conj form (via self-adjointness
    and the landed bridge `entrywiseConj_eq_transpose_of_selfAdjoint`)
    closed by `UJ * UJ = 1`. -/
theorem exHermMat_isAdm32 (u v : Fin 16) (z : ℂ) :
    IsAdm32 (exHermMat u v z) := by
  have hsa := exHermMat_conjTranspose u v z
  have hAdm := exHermMat_isAdmBlock u v z
  refine ⟨hsa, hAdm.1, ?_⟩
  calc UJ * (exHermMat u v z).transpose * UJ
      = (UJ * entrywiseConj (exHermMat u v z)) * UJ := by
        rw [entrywiseConj_eq_transpose_of_selfAdjoint hsa]
    _ = (exHermMat u v z * UJ) * UJ := by rw [hAdm.2]
    _ = exHermMat u v z := by
        rw [mul_assoc, UJ_mul_self, mul_one]

/-- Membership of a hermitian E-slot pattern in `PairSpace`, from
    order-one of the two single-coordinate patterns. -/
theorem exHermMat_mem {u v : Fin 16} {z : ℂ}
    (h1 : OrderOneHolds (exPairMat u v z))
    (h2 : OrderOneHolds (exPairMat v u z)) :
    exHermMat u v z ∈ PairSpace :=
  pairSpace_of_isAdm32 (exHermMat_isAdm32 u v z)
    (orderOneHolds_add h1 h2)

/-- **The anti E-slot pattern** at folded coordinate pair `(u, v)`:
    the antisymmetric combination of the two single-coordinate pair
    patterns. It is anti-hermitian:
    `(exAntiMat u v z).conjTranspose = - exAntiMat u v z`. -/
noncomputable def exAntiMat (u v : Fin 16) (z : ℂ) : Matrix I32 I32 ℂ :=
  exPairMat u v z - exPairMat v u z

theorem exAntiMat_conjTranspose (u v : Fin 16) (z : ℂ) :
    (exAntiMat u v z).conjTranspose = - exAntiMat u v z := by
  unfold exAntiMat
  rw [Matrix.conjTranspose_sub, exPairMat_conjTranspose,
    exPairMat_conjTranspose, neg_sub]

theorem exAntiMat_isAdmBlock (u v : Fin 16) (z : ℂ) :
    IsAdmBlock (exAntiMat u v z) :=
  AdmBlock.sub_mem (exPairMat_isAdmBlock u v z)
    (exPairMat_isAdmBlock v u z)

/-- Membership of an anti E-slot pattern in `PairSpace`, from
    order-one of the two single-coordinate patterns: the partner
    conditions are the negations of the first member's. -/
theorem exAntiMat_mem {u v : Fin 16} {z : ℂ}
    (h1 : OrderOneHolds (exPairMat u v z))
    (h2 : OrderOneHolds (exPairMat v u z)) :
    exAntiMat u v z ∈ PairSpace := by
  have hOO : OrderOneHolds (exAntiMat u v z) := orderOneHolds_sub h1 h2
  have hAdm : IsAdmBlock (exAntiMat u v z) := exAntiMat_isAdmBlock u v z
  refine ⟨hAdm, ?_, hOO, ?_⟩
  · rw [exAntiMat_conjTranspose]; exact AdmBlock.neg_mem hAdm
  · rw [exAntiMat_conjTranspose]; exact orderOneHolds_neg hOO

/-! ## 3. The generic order-one theorem for E-slot pair patterns -/

/-- Folded-coordinate characterization: `acoord x = a` iff the index
    is one of the two lifts of `a`. -/
theorem exAcoord_eq_iff {x : I32} {a : Fin 16} :
    acoord x = a ↔ x.val = a.val ∨ x.val = a.val + 16 := by
  constructor
  · intro h
    have h2 : x.val % 16 = a.val := by
      have h3 := congrArg Fin.val h
      rwa [acoord_val] at h3
    have hlt := x.isLt
    omega
  · intro h
    apply Fin.ext
    rw [acoord_val]
    have ha : a.val < 16 := a.isLt
    rcases h with h | h <;> rw [h] <;> omega

/-- An index with the same value as a folded coordinate has that
    folded coordinate. -/
theorem exAcoord_of_val_eq {x : I32} {a : Fin 16} (h : x.val = a.val) :
    acoord x = a :=
  exAcoord_eq_iff.mpr (Or.inl h)

/-- `gSign` at indices 24-31 is `1`. -/
theorem exGSign_eq_one_of_ge_24 {x : I32} (hx : 24 ≤ x.val) :
    gSign x = 1 := by
  rw [gSign_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rfl

/-- If `gSign x` is not `1`, the index lies in the minus range 8-23. -/
theorem exVal_range_of_gSign_ne_one {x : I32} (h : gSign x ≠ 1) :
    8 ≤ x.val ∧ x.val < 24 := by
  by_cases h8 : x.val < 8
  · exfalso
    apply h
    rw [gSign_apply, if_pos h8]
  · by_cases h24 : 24 ≤ x.val
    · exfalso
      exact h (exGSign_eq_one_of_ge_24 h24)
    · omega

/-- A nonzero entry of a matrix product has a nonzero path. -/
theorem exMul_apply_ne_zero_extract {A B : Matrix I32 I32 ℂ} {i j : I32}
    (h : (A * B) i j ≠ 0) : ∃ l, A i l ≠ 0 ∧ B l j ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : A i l = 0
  · rw [hl, zero_mul]
  · rw [hc l hl, mul_zero]

/-- Double-commutator vanishing from support confinement (assembled
    from the landed `disjoint_mul_zero`). -/
theorem exDcomm_eq_zero_of_support {C Y : Matrix I32 I32 ℂ}
    (P Q : I32 → Prop)
    (hC1 : ∀ i k, C i k ≠ 0 → P k) (hC2 : ∀ k j, C k j ≠ 0 → P k)
    (hY1 : ∀ i k, Y i k ≠ 0 → Q k) (hY2 : ∀ k j, Y k j ≠ 0 → Q k)
    (hPQ : ∀ k, Q k → ¬ P k) :
    C * Y - Y * C = 0 := by
  have hA : C * Y = 0 :=
    disjoint_mul_zero P hC1 (fun k j hkj => hPQ k (hY2 k j hkj))
  have hB : Y * C = 0 :=
    disjoint_mul_zero Q hY1 (fun k j hkj hQk => hPQ k hQk (hC2 k j hkj))
  rw [hA, hB, sub_self]

/-- Commutation with the diagonal opposite `genC`: if every nonzero
    entry of `C` joins indices of equal `genCOpVal`, then `C`
    commutes with `smGenOp 0`. -/
theorem exComm_genOpC_eq_zero_of {C : Matrix I32 I32 ℂ}
    (hC : ∀ i j, C i j ≠ 0 → genCOpVal j = genCOpVal i) :
    C * smGenOp 0 - smGenOp 0 * C = 0 := by
  ext i j
  have h1 : (C * smGenOp 0) i j = C i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [smGenOp_zero_eq j j, if_pos rfl]
    · intro l _ hlj
      rw [smGenOp_zero_eq l j, if_neg hlj, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have h2 : (smGenOp 0 * C) i j = genCOpVal i * C i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [smGenOp_zero_eq i i, if_pos rfl]
    · intro l _ hli
      rw [smGenOp_zero_eq i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  rw [Matrix.sub_apply, h1, h2]
  by_cases hCij : C i j = 0
  · rw [hCij, zero_mul, mul_zero, sub_zero, Matrix.zero_apply]
  · rw [hC i j hCij, mul_comm, sub_self, Matrix.zero_apply]

/-- Triplet-mates in the folded sense: `x` shares a triplet label
    with the index of value `n`. -/
def exTripMate (n : Nat) (x : I32) : Prop :=
  ∃ t : Fin 4, ∃ p q : Fin 3,
    tripletOf n = some (t, p) ∧ tripletOf x.val = some (t, q)

theorem exTripMate_val_range {n : Nat} {x : I32} (h : exTripMate n x) :
    (18 ≤ x.val ∧ x.val < 24) ∨ (26 ≤ x.val ∧ x.val < 32) := by
  obtain ⟨t, p, q, -, hx⟩ := h
  have h2 := tripletOf_eig x.val x.isLt t q hx
  rcases h2 with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

theorem exTripMate_val_ge {n : Nat} (hn : 26 ≤ n ∧ n < 32) {x : I32}
    (h : exTripMate n x) : 26 ≤ x.val ∧ x.val < 32 := by
  obtain ⟨t, p, q, hn', hx⟩ := h
  have ht := tripletOf_eig n (by omega) t p hn'
  have hx2 := tripletOf_eig x.val x.isLt t q hx
  rcases ht with ⟨ht1, h1, h2⟩ | ⟨ht1, h1, h2⟩
  · omega
  · rcases hx2 with ⟨h3, -, -⟩ | ⟨-, h3, h4⟩
    · omega
    · exact ⟨h3, h4⟩

/-- Numeric form of `genCVal`: it is `Complex.I` exactly on the
    index set `[8, 16) ∪ {16, 17, 24, 25}` and `0` elsewhere. -/
theorem exGenCVal_apply (y : I32) :
    genCVal y = if (8 ≤ y.val ∧ y.val < 16) ∨ y.val = 16 ∨ y.val = 17 ∨
        y.val = 24 ∨ y.val = 25 then Complex.I else 0 := by
  unfold genCVal
  by_cases h1 : 8 ≤ y.val ∧ y.val < 16
  · rw [if_pos h1, if_pos (by omega)]
  · by_cases h2 : y.val = 16 ∨ y.val = 17 ∨ y.val = 24 ∨ y.val = 25
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]

/-- The `genC` evaluation table at a lepton-singlet folded
    coordinate (8 or 9): both lifts have `genCVal` and `genCOpVal`
    equal to `Complex.I`. -/
theorem exGenC_table_singlet {w : Fin 16} (hw : w.val = 8 ∨ w.val = 9)
    {x : I32} (hx : acoord x = w) :
    genCVal x = Complex.I ∧ genCOpVal x = Complex.I := by
  rw [exAcoord_eq_iff] at hx
  have hval : ∀ y : I32, y.val = w.val ∨ y.val = w.val + 16 →
      genCVal y = Complex.I := by
    intro y hy
    rw [exGenCVal_apply, if_pos (by omega)]
  refine ⟨hval x hx, ?_⟩
  have hp : (partner x).val = w.val ∨ (partner x).val = w.val + 16 := by
    rw [partner_val_eq]
    rcases hx with hx | hx
    · rw [if_pos (by omega : x.val < 16)]
      exact Or.inr (by rw [hx])
    · rw [if_neg (by omega : ¬ x.val < 16)]
      exact Or.inl (by omega)
  show genCVal (partner x) = Complex.I
  exact hval (partner x) hp

/-- The `genC` evaluation table at a right-handed folded coordinate
    (10-15): the particle lift has charges `(I, 0)`, the antiparticle
    lift `(0, I)`. -/
theorem exGenC_table_quark {w : Fin 16} (hw : 10 ≤ w.val ∧ w.val ≤ 15)
    {x : I32} (hx : acoord x = w) :
    (x.val = w.val ∧ genCVal x = Complex.I ∧ genCOpVal x = 0) ∨
    (x.val = w.val + 16 ∧ genCVal x = 0 ∧ genCOpVal x = Complex.I) := by
  rw [exAcoord_eq_iff] at hx
  rcases hx with hx | hx
  · refine Or.inl ⟨hx, ?_, ?_⟩
    · rw [exGenCVal_apply, if_pos (by omega)]
    · show genCVal (partner x) = 0
      have hp : (partner x).val = w.val + 16 := by
        rw [partner_val_eq, if_pos (by omega : x.val < 16), hx]
      rw [exGenCVal_apply, hp, if_neg (by omega)]
  · refine Or.inr ⟨hx, ?_, ?_⟩
    · rw [exGenCVal_apply, hx, if_neg (by omega)]
    · show genCVal (partner x) = Complex.I
      have hp : (partner x).val = w.val := by
        rw [partner_val_eq, if_neg (by omega : ¬ x.val < 16)]
        omega
      rw [exGenCVal_apply, hp, if_pos (by omega)]

/-- `genCOpVal` at a 26-31 index is `Complex.I`. -/
theorem exGenCOpVal_eq_I_of_ge_26 {x : I32}
    (hx : 26 ≤ x.val ∧ x.val < 32) : genCOpVal x = Complex.I := by
  show genCVal (partner x) = Complex.I
  have hp : (partner x).val = x.val - 16 := by
    rw [partner_val_eq, if_neg (by omega)]
  rw [exGenCVal_apply, hp, if_pos (by omega)]

/-- A single-coordinate E-slot pair pattern commutes with every
    `genH k`: its support indices avoid the doublet range 0-7. -/
theorem exPairMat_comm_genH_eq_zero {u v : Fin 16}
    (hu : 8 ≤ u.val) (hv : 8 ≤ v.val) (z : ℂ) (k : Fin 3) :
    exPairMat u v z * genH k - genH k * exPairMat u v z = 0 := by
  have hDcol : ∀ i l, exPairMat u v z i l ≠ 0 → 8 ≤ l.val := by
    intro i l hl
    have hc := (exPairMat_ne_zero hl).2.1
    rw [exAcoord_eq_iff] at hc
    omega
  have hDrow : ∀ l j, exPairMat u v z l j ≠ 0 → 8 ≤ l.val := by
    intro l j hl
    have hc := (exPairMat_ne_zero hl).1
    rw [exAcoord_eq_iff] at hc
    omega
  have h1 : exPairMat u v z * genH k = 0 := by
    apply disjoint_mul_zero (fun x => 8 ≤ x.val)
    · exact hDcol
    · intro l j hlj
      have h2 := (genH_supp k l j hlj).1
      omega
  have h2 : genH k * exPairMat u v z = 0 := by
    apply disjoint_mul_zero (fun x => x.val < 8)
    · intro i l hil
      exact (genH_supp k i l hil).2
    · intro l j hlj
      have h3 := hDrow l j hlj
      omega
  rw [h1, h2, sub_self]

/-- The `(genC, genC°)` factor condition, orientation A (singlet
    row, right-handed column): at every support entry one of the two
    charge-difference factors vanishes. -/
theorem exPairMat_factor_CC_A {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ) (i j : I32)
    (h : exPairMat u v z i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  have hcoord := exPairMat_ne_zero h
  obtain ⟨hCi, hOi⟩ := exGenC_table_singlet hu hcoord.1
  rcases exGenC_table_quark hv hcoord.2.1 with ⟨-, hCj, -⟩ | ⟨-, -, hOj⟩
  · rw [hCj, hCi, sub_self, zero_mul]
  · rw [hOj, hOi, sub_self, mul_zero]

/-- The `(genC, genC°)` factor condition, orientation B
    (right-handed row, singlet column). -/
theorem exPairMat_factor_CC_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9)
    (z : ℂ) (i j : I32) (h : exPairMat u v z i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  have hcoord := exPairMat_ne_zero h
  obtain ⟨hCj, hOj⟩ := exGenC_table_singlet hv hcoord.2.1
  rcases exGenC_table_quark hu hcoord.1 with ⟨-, hCi, -⟩ | ⟨-, -, hOi⟩
  · rw [hCi, hCj, sub_self, zero_mul]
  · rw [hOi, hOj, sub_self, mul_zero]

/-- Support of `[M, genC]`, orientation A: the commutator of a
    single-coordinate pattern with `genC` is supported on the single
    entry `(u, v + 16)`. -/
theorem exPairMat_comm_genC_support_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    {i j : I32}
    (h : (exPairMat u v z * genC - genC * exPairMat u v z) i j ≠ 0) :
    i.val = u.val ∧ j.val = v.val + 16 := by
  have h2 := comm_diag_entry (exPairMat u v z) genCVal genC
    (fun x y => genC_eq_diag x y) i j
  rw [h2] at h
  obtain ⟨hD, hC⟩ := mul_ne_zero_iff.mp h
  have hcoord := exPairMat_ne_zero hD
  obtain ⟨hCi, -⟩ := exGenC_table_singlet hu hcoord.1
  have hjv : j.val = v.val + 16 := by
    rcases exGenC_table_quark hv hcoord.2.1 with
      ⟨hvalj, hCj, -⟩ | ⟨hvalj, -, -⟩
    · exfalso
      apply hC
      rw [hCj, hCi, sub_self]
    · exact hvalj
  have hgj : gSign j = 1 := exGSign_eq_one_of_ge_24 (by omega)
  have hgi : gSign i ≠ 1 := fun hh => hcoord.2.2 (hh.trans hgj.symm)
  have hrange := exVal_range_of_gSign_ne_one hgi
  have hci := hcoord.1
  rw [exAcoord_eq_iff] at hci
  exact ⟨by omega, hjv⟩

/-- Support of `[M, genC]`, orientation B: the commutator is
    supported on the single entry `(u + 16, v)`. -/
theorem exPairMat_comm_genC_support_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    {i j : I32}
    (h : (exPairMat u v z * genC - genC * exPairMat u v z) i j ≠ 0) :
    i.val = u.val + 16 ∧ j.val = v.val := by
  have h2 := comm_diag_entry (exPairMat u v z) genCVal genC
    (fun x y => genC_eq_diag x y) i j
  rw [h2] at h
  obtain ⟨hD, hC⟩ := mul_ne_zero_iff.mp h
  have hcoord := exPairMat_ne_zero hD
  obtain ⟨hCj, -⟩ := exGenC_table_singlet hv hcoord.2.1
  have hiv : i.val = u.val + 16 := by
    rcases exGenC_table_quark hu hcoord.1 with
      ⟨hvali, hCi, -⟩ | ⟨hvali, -, -⟩
    · exfalso
      apply hC
      rw [hCi, hCj, sub_self]
    · exact hvali
  have hgi : gSign i = 1 := exGSign_eq_one_of_ge_24 (by omega)
  have hgj : gSign j ≠ 1 :=
    fun hh => hcoord.2.2 (hgi.trans hh.symm)
  have hrange := exVal_range_of_gSign_ne_one hgj
  have hcj := hcoord.2.1
  rw [exAcoord_eq_iff] at hcj
  exact ⟨hiv, by omega⟩

/-- Support of `[M, genM a]`, orientation A: nonzero entries join
    the singlet index `u` to the colour triplet of `v + 16` (the
    `genM * M` product vanishes outright). -/
theorem exPairMat_comm_genM_support_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) {i j : I32}
    (h : (exPairMat u v z * genM a - genM a * exPairMat u v z) i j ≠ 0) :
    i.val = u.val ∧ exTripMate (v.val + 16) j := by
  have hne : (exPairMat u v z * genM a) i j ≠ 0 ∨
      (genM a * exPairMat u v z) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [Matrix.sub_apply, hc.1, hc.2, sub_self])
  rcases hne with hDG | hGD
  · obtain ⟨l, hDl, hGl⟩ := exMul_apply_ne_zero_extract hDG
    obtain ⟨t, p, q, hlt, hjt⟩ := genM_supp_triplet a l j hGl
    have hrange : (18 ≤ l.val ∧ l.val < 24) ∨ (26 ≤ l.val ∧ l.val < 32) :=
      (genM_supp a l j hGl).1
    have hcoord := exPairMat_ne_zero hDl
    have hlv : l.val = v.val + 16 := by
      have h2 := hcoord.2.1
      rw [exAcoord_eq_iff] at h2
      rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> omega
    have hival : i.val = u.val := by
      have h2 := hcoord.1
      rw [exAcoord_eq_iff] at h2
      have hgl : gSign l = 1 := exGSign_eq_one_of_ge_24 (by omega)
      have hgi : gSign i ≠ 1 := fun hh => hcoord.2.2 (hh.trans hgl.symm)
      have hrangei := exVal_range_of_gSign_ne_one hgi
      rcases hu with hu | hu <;> omega
    exact ⟨hival, t, p, q, by rwa [hlv] at hlt, hjt⟩
  · exfalso
    obtain ⟨l, hGl, hDl⟩ := exMul_apply_ne_zero_extract hGD
    have hrange : (18 ≤ l.val ∧ l.val < 24) ∨ (26 ≤ l.val ∧ l.val < 32) :=
      (genM_supp a i l hGl).2
    have hcoord := exPairMat_ne_zero hDl
    have h2 := hcoord.1
    rw [exAcoord_eq_iff] at h2
    rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;>
      rcases hu with hu | hu <;> omega

/-- Support of `[M, genM a]`, orientation B: nonzero entries join
    the colour triplet of `u + 16` to the singlet index `v` (the
    `M * genM` product vanishes outright). -/
theorem exPairMat_comm_genM_support_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (a : Fin 8) {i j : I32}
    (h : (exPairMat u v z * genM a - genM a * exPairMat u v z) i j ≠ 0) :
    exTripMate (u.val + 16) i ∧ j.val = v.val := by
  have hne : (exPairMat u v z * genM a) i j ≠ 0 ∨
      (genM a * exPairMat u v z) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [Matrix.sub_apply, hc.1, hc.2, sub_self])
  rcases hne with hDG | hGD
  · exfalso
    obtain ⟨l, hDl, hGl⟩ := exMul_apply_ne_zero_extract hDG
    have hrange : (18 ≤ l.val ∧ l.val < 24) ∨ (26 ≤ l.val ∧ l.val < 32) :=
      (genM_supp a l j hGl).1
    have hcoord := exPairMat_ne_zero hDl
    have h2 := hcoord.2.1
    rw [exAcoord_eq_iff] at h2
    rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;>
      rcases hv with hv | hv <;> omega
  · obtain ⟨l, hGl, hDl⟩ := exMul_apply_ne_zero_extract hGD
    obtain ⟨t, p, q, hit, hlt⟩ := genM_supp_triplet a i l hGl
    have hrange : (18 ≤ l.val ∧ l.val < 24) ∨ (26 ≤ l.val ∧ l.val < 32) :=
      (genM_supp a i l hGl).2
    have hcoord := exPairMat_ne_zero hDl
    have hlv : l.val = u.val + 16 := by
      have h2 := hcoord.1
      rw [exAcoord_eq_iff] at h2
      rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> omega
    have hjval : j.val = v.val := by
      have h2 := hcoord.2.1
      rw [exAcoord_eq_iff] at h2
      have hgl : gSign l = 1 := exGSign_eq_one_of_ge_24 (by omega)
      have hgj : gSign j ≠ 1 := fun hh => hcoord.2.2 (hgl.trans hh.symm)
      have hrangej := exVal_range_of_gSign_ne_one hgj
      rcases hv with hv | hv <;> omega
    exact ⟨⟨t, q, p, by rwa [hlv] at hlt, hit⟩, hjval⟩

/-- Double commutators of `[M, genC]` against the `genH`
    opposites, orientation A. -/
theorem exPairMat_dcomm_genC_genHOp_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (k : Fin 3) :
    (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = v.val + 16 ∨ x.val = u.val)
    (fun x => 16 ≤ x.val ∧ x.val < 24)
  · intro i k2 hik
    have hs := exPairMat_comm_genC_support_A hu hv z hik
    exact Or.inl hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genC_support_A hu hv z hkj
    exact Or.inr hs.1
  · intro i k2 hik
    have hs := UJ_genH_transpose_UJ_supp k i k2 hik
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · intro k2 j hkj
    have hs := UJ_genH_transpose_UJ_supp k k2 j hkj
    exact ⟨hs.1, hs.2.1⟩
  · intro k2 ⟨h1, h2⟩ h3
    rcases h3 with h3 | h3 <;> omega

/-- Double commutators of `[M, genC]` against the `genM`
    opposites, orientation A. -/
theorem exPairMat_dcomm_genC_genMOp_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) :
    (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = v.val + 16 ∨ x.val = u.val)
    (fun x => (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16))
  · intro i k2 hik
    have hs := exPairMat_comm_genC_support_A hu hv z hik
    exact Or.inl hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genC_support_A hu hv z hkj
    exact Or.inr hs.1
  · intro i k2 hik
    have hs := UJ_genM_transpose_UJ_supp a i k2 hik
    exact hs.2
  · intro k2 j hkj
    have hs := UJ_genM_transpose_UJ_supp a k2 j hkj
    exact hs.1
  · intro k2 h1 h3
    rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h3 with h3 | h3 <;> omega

/-- All double commutators with first generator `genC`,
    orientation A. -/
theorem exPairMat_oo_genC_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (g2 : Fin 12) :
    (exPairMat u v z * genC - genC * exPairMat u v z) * smGenOp g2
      - smGenOp g2 * (exPairMat u v z * genC - genC * exPairMat u v z)
      = 0 := by
  fin_cases g2
  · exact oo_C_C_of_factor _ (exPairMat_factor_CC_A hu hv z)
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH 0).transpose * UJ)
      - (UJ * (genH 0).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genHOp_A hu hv z 0
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH 1).transpose * UJ)
      - (UJ * (genH 1).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genHOp_A hu hv z 1
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH 2).transpose * UJ)
      - (UJ * (genH 2).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genHOp_A hu hv z 2
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 0).transpose * UJ)
      - (UJ * (genM 0).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 0
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 1).transpose * UJ)
      - (UJ * (genM 1).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 1
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 2).transpose * UJ)
      - (UJ * (genM 2).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 2
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 3).transpose * UJ)
      - (UJ * (genM 3).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 3
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 4).transpose * UJ)
      - (UJ * (genM 4).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 4
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 5).transpose * UJ)
      - (UJ * (genM 5).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 5
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 6).transpose * UJ)
      - (UJ * (genM 6).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 6
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 7).transpose * UJ)
      - (UJ * (genM 7).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_A hu hv z 7

/-- Double commutators of `[M, genM a]` against the `genH`
    opposites, orientation A. -/
theorem exPairMat_dcomm_genM_genHOp_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) (k : Fin 3) :
    (exPairMat u v z * genM a - genM a * exPairMat u v z)
        * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ)
        * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = u.val ∨ exTripMate (v.val + 16) x)
    (fun x => 16 ≤ x.val ∧ x.val < 24)
  · intro i k2 hik
    have hs := exPairMat_comm_genM_support_A hu hv z a hik
    exact Or.inr hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genM_support_A hu hv z a hkj
    exact Or.inl hs.1
  · intro i k2 hik
    have hs := UJ_genH_transpose_UJ_supp k i k2 hik
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · intro k2 j hkj
    have hs := UJ_genH_transpose_UJ_supp k k2 j hkj
    exact ⟨hs.1, hs.2.1⟩
  · intro k2 ⟨h1, h2⟩ h3
    rcases h3 with h3 | h3
    · omega
    · have h4 := exTripMate_val_ge (n := v.val + 16) (by omega) h3
      omega

/-- Double commutators of `[M, genM a]` against the `genM`
    opposites, orientation A. -/
theorem exPairMat_dcomm_genM_genMOp_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a b : Fin 8) :
    (exPairMat u v z * genM a - genM a * exPairMat u v z)
        * (UJ * (genM b).transpose * UJ)
      - (UJ * (genM b).transpose * UJ)
        * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = u.val ∨ exTripMate (v.val + 16) x)
    (fun x => (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16))
  · intro i k2 hik
    have hs := exPairMat_comm_genM_support_A hu hv z a hik
    exact Or.inr hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genM_support_A hu hv z a hkj
    exact Or.inl hs.1
  · intro i k2 hik
    have hs := UJ_genM_transpose_UJ_supp b i k2 hik
    exact hs.2
  · intro k2 j hkj
    have hs := UJ_genM_transpose_UJ_supp b k2 j hkj
    exact hs.1
  · intro k2 h1 h3
    rcases h3 with h3 | h3
    · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have h4 := exTripMate_val_range h3
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega

/-- All double commutators with first generator `genM a`,
    orientation A. -/
theorem exPairMat_oo_genM_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) (g2 : Fin 12) :
    (exPairMat u v z * genM a - genM a * exPairMat u v z) * smGenOp g2
      - smGenOp g2 * (exPairMat u v z * genM a - genM a * exPairMat u v z)
      = 0 := by
  fin_cases g2
  · apply exComm_genOpC_eq_zero_of
    intro i j hij
    have hs := exPairMat_comm_genM_support_A hu hv z a hij
    have h1 : genCOpVal i = Complex.I :=
      (exGenC_table_singlet hu (exAcoord_of_val_eq hs.1)).2
    have h2 : genCOpVal j = Complex.I :=
      exGenCOpVal_eq_I_of_ge_26 (exTripMate_val_ge (n := v.val + 16)
        (by omega) hs.2)
    rw [h1, h2]
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genHOp_A hu hv z a 0
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genHOp_A hu hv z a 1
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genHOp_A hu hv z a 2
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 0
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 1
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 2
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 3
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 4
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 5
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 6
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_A hu hv z a 7

/-- **The generic E-slot order-one theorem, orientation A.** Every
    single-coordinate pair pattern at a lepton-singlet row `u`
    (8 or 9) and a right-handed column `v` (10-15) satisfies the
    order-one condition. -/
theorem exPairMat_orderOne_A {u v : Fin 16}
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15)
    (z : ℂ) : OrderOneHolds (exPairMat u v z) := by
  intro g1 g2
  fin_cases g1
  · show (exPairMat u v z * genC - genC * exPairMat u v z) * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genC - genC * exPairMat u v z)
        = 0
    exact exPairMat_oo_genC_A hu hv z g2
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
    exact exPairMat_oo_genM_A hu hv z 0 g2
  · show (exPairMat u v z * genM 1 - genM 1 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 1 - genM 1 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 1 g2
  · show (exPairMat u v z * genM 2 - genM 2 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 2 - genM 2 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 2 g2
  · show (exPairMat u v z * genM 3 - genM 3 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 3 - genM 3 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 3 g2
  · show (exPairMat u v z * genM 4 - genM 4 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 4 - genM 4 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 4 g2
  · show (exPairMat u v z * genM 5 - genM 5 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 5 - genM 5 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 5 g2
  · show (exPairMat u v z * genM 6 - genM 6 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 6 - genM 6 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 6 g2
  · show (exPairMat u v z * genM 7 - genM 7 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 7 - genM 7 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_A hu hv z 7 g2

/-- Double commutators of `[M, genC]` against the `genH`
    opposites, orientation B. -/
theorem exPairMat_dcomm_genC_genHOp_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (k : Fin 3) :
    (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = u.val + 16 ∨ x.val = v.val)
    (fun x => 16 ≤ x.val ∧ x.val < 24)
  · intro i k2 hik
    have hs := exPairMat_comm_genC_support_B hu hv z hik
    exact Or.inr hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genC_support_B hu hv z hkj
    exact Or.inl hs.1
  · intro i k2 hik
    have hs := UJ_genH_transpose_UJ_supp k i k2 hik
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · intro k2 j hkj
    have hs := UJ_genH_transpose_UJ_supp k k2 j hkj
    exact ⟨hs.1, hs.2.1⟩
  · intro k2 ⟨h1, h2⟩ h3
    rcases h3 with h3 | h3 <;> omega

/-- Double commutators of `[M, genC]` against the `genM`
    opposites, orientation B. -/
theorem exPairMat_dcomm_genC_genMOp_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (a : Fin 8) :
    (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = u.val + 16 ∨ x.val = v.val)
    (fun x => (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16))
  · intro i k2 hik
    have hs := exPairMat_comm_genC_support_B hu hv z hik
    exact Or.inr hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genC_support_B hu hv z hkj
    exact Or.inl hs.1
  · intro i k2 hik
    have hs := UJ_genM_transpose_UJ_supp a i k2 hik
    exact hs.2
  · intro k2 j hkj
    have hs := UJ_genM_transpose_UJ_supp a k2 j hkj
    exact hs.1
  · intro k2 h1 h3
    rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h3 with h3 | h3 <;> omega

/-- All double commutators with first generator `genC`,
    orientation B. -/
theorem exPairMat_oo_genC_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (g2 : Fin 12) :
    (exPairMat u v z * genC - genC * exPairMat u v z) * smGenOp g2
      - smGenOp g2 * (exPairMat u v z * genC - genC * exPairMat u v z)
      = 0 := by
  fin_cases g2
  · exact oo_C_C_of_factor _ (exPairMat_factor_CC_B hu hv z)
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH 0).transpose * UJ)
      - (UJ * (genH 0).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genHOp_B hu hv z 0
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH 1).transpose * UJ)
      - (UJ * (genH 1).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genHOp_B hu hv z 1
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genH 2).transpose * UJ)
      - (UJ * (genH 2).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genHOp_B hu hv z 2
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 0).transpose * UJ)
      - (UJ * (genM 0).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 0
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 1).transpose * UJ)
      - (UJ * (genM 1).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 1
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 2).transpose * UJ)
      - (UJ * (genM 2).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 2
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 3).transpose * UJ)
      - (UJ * (genM 3).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 3
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 4).transpose * UJ)
      - (UJ * (genM 4).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 4
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 5).transpose * UJ)
      - (UJ * (genM 5).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 5
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 6).transpose * UJ)
      - (UJ * (genM 6).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 6
  · show (exPairMat u v z * genC - genC * exPairMat u v z)
        * (UJ * (genM 7).transpose * UJ)
      - (UJ * (genM 7).transpose * UJ)
        * (exPairMat u v z * genC - genC * exPairMat u v z) = 0
    exact exPairMat_dcomm_genC_genMOp_B hu hv z 7

/-- Double commutators of `[M, genM a]` against the `genH`
    opposites, orientation B. -/
theorem exPairMat_dcomm_genM_genHOp_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (a : Fin 8) (k : Fin 3) :
    (exPairMat u v z * genM a - genM a * exPairMat u v z)
        * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ)
        * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = v.val ∨ exTripMate (u.val + 16) x)
    (fun x => 16 ≤ x.val ∧ x.val < 24)
  · intro i k2 hik
    have hs := exPairMat_comm_genM_support_B hu hv z a hik
    exact Or.inl hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genM_support_B hu hv z a hkj
    exact Or.inr hs.1
  · intro i k2 hik
    have hs := UJ_genH_transpose_UJ_supp k i k2 hik
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · intro k2 j hkj
    have hs := UJ_genH_transpose_UJ_supp k k2 j hkj
    exact ⟨hs.1, hs.2.1⟩
  · intro k2 ⟨h1, h2⟩ h3
    rcases h3 with h3 | h3
    · omega
    · have h4 := exTripMate_val_ge (n := u.val + 16) (by omega) h3
      omega

/-- Double commutators of `[M, genM a]` against the `genM`
    opposites, orientation B. -/
theorem exPairMat_dcomm_genM_genMOp_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (a b : Fin 8) :
    (exPairMat u v z * genM a - genM a * exPairMat u v z)
        * (UJ * (genM b).transpose * UJ)
      - (UJ * (genM b).transpose * UJ)
        * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0 := by
  apply exDcomm_eq_zero_of_support
    (fun x => x.val = v.val ∨ exTripMate (u.val + 16) x)
    (fun x => (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16))
  · intro i k2 hik
    have hs := exPairMat_comm_genM_support_B hu hv z a hik
    exact Or.inl hs.2
  · intro k2 j hkj
    have hs := exPairMat_comm_genM_support_B hu hv z a hkj
    exact Or.inr hs.1
  · intro i k2 hik
    have hs := UJ_genM_transpose_UJ_supp b i k2 hik
    exact hs.2
  · intro k2 j hkj
    have hs := UJ_genM_transpose_UJ_supp b k2 j hkj
    exact hs.1
  · intro k2 h1 h3
    rcases h3 with h3 | h3
    · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have h4 := exTripMate_val_range h3
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega

/-- All double commutators with first generator `genM a`,
    orientation B. -/
theorem exPairMat_oo_genM_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9) (z : ℂ)
    (a : Fin 8) (g2 : Fin 12) :
    (exPairMat u v z * genM a - genM a * exPairMat u v z) * smGenOp g2
      - smGenOp g2 * (exPairMat u v z * genM a - genM a * exPairMat u v z)
      = 0 := by
  fin_cases g2
  · apply exComm_genOpC_eq_zero_of
    intro i j hij
    have hs := exPairMat_comm_genM_support_B hu hv z a hij
    have h1 : genCOpVal i = Complex.I :=
      exGenCOpVal_eq_I_of_ge_26 (exTripMate_val_ge (n := u.val + 16)
        (by omega) hs.1)
    have h2 : genCOpVal j = Complex.I :=
      (exGenC_table_singlet hv (exAcoord_of_val_eq hs.2)).2
    rw [h1, h2]
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genHOp_B hu hv z a 0
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genHOp_B hu hv z a 1
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genHOp_B hu hv z a 2
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 0
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 1
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 2
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 3
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 4
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 5
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 6
  · show (exPairMat u v z * genM a - genM a * exPairMat u v z)
          * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ)
          * (exPairMat u v z * genM a - genM a * exPairMat u v z) = 0
    exact exPairMat_dcomm_genM_genMOp_B hu hv z a 7

/-- **The generic E-slot order-one theorem, orientation B.** Every
    single-coordinate pair pattern at a right-handed row `u`
    (10-15) and a lepton-singlet column `v` (8 or 9) satisfies the
    order-one condition. -/
theorem exPairMat_orderOne_B {u v : Fin 16}
    (hu : 10 ≤ u.val ∧ u.val ≤ 15) (hv : v.val = 8 ∨ v.val = 9)
    (z : ℂ) : OrderOneHolds (exPairMat u v z) := by
  intro g1 g2
  fin_cases g1
  · show (exPairMat u v z * genC - genC * exPairMat u v z) * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genC - genC * exPairMat u v z)
        = 0
    exact exPairMat_oo_genC_B hu hv z g2
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
    exact exPairMat_oo_genM_B hu hv z 0 g2
  · show (exPairMat u v z * genM 1 - genM 1 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 1 - genM 1 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 1 g2
  · show (exPairMat u v z * genM 2 - genM 2 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 2 - genM 2 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 2 g2
  · show (exPairMat u v z * genM 3 - genM 3 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 3 - genM 3 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 3 g2
  · show (exPairMat u v z * genM 4 - genM 4 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 4 - genM 4 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 4 g2
  · show (exPairMat u v z * genM 5 - genM 5 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 5 - genM 5 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 5 g2
  · show (exPairMat u v z * genM 6 - genM 6 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 6 - genM 6 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 6 g2
  · show (exPairMat u v z * genM 7 - genM 7 * exPairMat u v z)
          * smGenOp g2
        - smGenOp g2 * (exPairMat u v z * genM 7 - genM 7 * exPairMat u v z)
        = 0
    exact exPairMat_oo_genM_B hu hv z 7 g2


/-! ## 4. The completed exotic family -/

/-- Folded row coordinate of the `m`-th E-slot Majorana coordinate
    pair: `8` for the first six pairs, `9` for the next six. -/
def exMajU (m : Nat) : Fin 16 :=
  ⟨if m < 6 then 8 else 9, by split_ifs <;> omega⟩

/-- Folded column coordinate of the `m`-th E-slot Majorana
    coordinate pair: `10 + m % 6`, cycling through `10..15`. -/
def exMajV (m : Nat) : Fin 16 :=
  ⟨10 + m % 6, by
    have h := Nat.mod_lt m (show 0 < 6 by norm_num)
    omega⟩

/-- Phase of the `n`-th direction in a family: even `n` is the real
    part of its coordinate pair, odd `n` the imaginary part. -/
def exPhase (n : Nat) : ℂ := if n % 2 = 0 then 1 else Complex.I

theorem exMajU_val (m : Nat) :
    (exMajU m).val = if m < 6 then 8 else 9 := rfl

theorem exMajV_val (m : Nat) : (exMajV m).val = 10 + m % 6 := rfl

theorem exMajU_spec (m : Nat) :
    (exMajU m).val = 8 ∨ (exMajU m).val = 9 := by
  rw [exMajU_val]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exMajV_spec (m : Nat) :
    10 ≤ (exMajV m).val ∧ (exMajV m).val ≤ 15 := by
  rw [exMajV_val]
  have h := Nat.mod_lt m (show 0 < 6 by norm_num)
  omega

/-- The 24 new hermitian exotic directions: the hermitian E-slot
    patterns at the twelve coordinate pairs `(8, 10..15)` and
    `(9, 10..15)`, real part then imaginary part at each pair. -/
noncomputable def exHermDir (n : Fin 24) : PairSpace :=
  ⟨exHermMat (exMajU (n.val / 2)) (exMajV (n.val / 2)) (exPhase n.val),
    exHermMat_mem
      (exPairMat_orderOne_A (exMajU_spec _) (exMajV_spec _) _)
      (exPairMat_orderOne_B (exMajV_spec _) (exMajU_spec _) _)⟩

/-- The 18 anti exotic directions: the antisymmetric E-slot
    patterns at the nine coordinate pairs `(8, 10..15)`, `(9, 10)`,
    `(9, 11)`, `(9, 12)`, real part then imaginary part at each
    pair. -/
noncomputable def exAntiDir (n : Fin 18) : PairSpace :=
  ⟨exAntiMat (exMajU (n.val / 2)) (exMajV (n.val / 2)) (exPhase n.val),
    exAntiMat_mem
      (exPairMat_orderOne_A (exMajU_spec _) (exMajV_spec _) _)
      (exPairMat_orderOne_B (exMajV_spec _) (exMajU_spec _) _)⟩

/-- **The completed exotic family (C96-3a3 headline).** The 54
    exotic pair directions: indices `0-11` are C96-3a's landed
    `pairDirExotic` (the W22 hermitian survivors), indices `12-35`
    are the 24 new hermitian E-slot patterns `exHermDir`, and
    indices `36-53` are the 18 anti E-slot patterns `exAntiDir`.
    In the segment form C96-3b consumes through `dir88Of`. -/
noncomputable def pairDirExotic54 : Fin 54 → PairSpace :=
  Fin.append (Fin.append pairDirExotic exHermDir) exAntiDir

/-- The landed segment of the completed family: the first 12
    indices are `pairDirExotic`. -/
theorem pairDirExotic54_exotic (k : Fin 12) :
    pairDirExotic54 ⟨k.val, by have h := k.isLt; omega⟩
      = pairDirExotic k := by
  have e1 : (⟨k.val, by have h := k.isLt; omega⟩ : Fin 54)
      = Fin.castAdd 18 (Fin.castAdd 24 k) := Fin.ext rfl
  rw [pairDirExotic54, e1, Fin.append_left, Fin.append_left]

/-- The hermitian segment of the completed family: indices `12-35`
    are the new hermitian E-slot patterns. -/
theorem pairDirExotic54_herm (k : Fin 24) :
    pairDirExotic54 ⟨k.val + 12, by have h := k.isLt; omega⟩
      = exHermDir k := by
  have e1 : (⟨k.val + 12, by have h := k.isLt; omega⟩ : Fin 54)
      = Fin.castAdd 18 (Fin.natAdd 12 k) := by
    apply Fin.ext
    show k.val + 12 = 12 + k.val
    omega
  rw [pairDirExotic54, e1, Fin.append_left, Fin.append_right]

/-- The anti segment of the completed family: indices `36-53` are
    the anti E-slot patterns. -/
theorem pairDirExotic54_anti (k : Fin 18) :
    pairDirExotic54 ⟨k.val + 36, by have h := k.isLt; omega⟩
      = exAntiDir k := by
  have e1 : (⟨k.val + 36, by have h := k.isLt; omega⟩ : Fin 54)
      = Fin.natAdd 36 k := by
    apply Fin.ext
    show k.val + 36 = 36 + k.val
    omega
  rw [pairDirExotic54, e1, Fin.append_right]

end ThetLogos
