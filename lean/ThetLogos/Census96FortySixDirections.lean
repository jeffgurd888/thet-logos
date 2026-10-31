import ThetLogos.Census96
import ThetLogos.Census96Decoupling
import ThetLogos.CFKernel22
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# ThetLogos.Census96FortySixDirections - C96-2a: the 46 directions (LANE 1)

Directions half of the one-generation 46 theorem (scoping memo
`scoping-census96-2026-10-30.md` section 1.A / section 3 row C96-2; pack
`pack-c96-2a.md`). The upper bound (`finrank` at most 46) and the
`finrank = 46` assembly are C96-2b, NOT this brick: no finrank headline
is stated here.

## What is proved here (T1 when the build is green)

* An explicit family `dir46 : Fin 46 -> Sol32` of 46 directions of the
  one-generation census space `Sol32 = {D | IsAdm32 D /\ OrderOneHolds D}`
  (the pin's space, `Census96.lean`), organized exactly per the census
  decomposition **46 = 10 + 8 + 28**:
  - indices 0-9: the 10 SM Yukawa + Majorana directions (consumed from
    the landed CF line: `smDir*` specializations of `smDirac`, via
    `dirs22` of `CFKernel22.lean`);
  - indices 10-17: the 8 flipped-Yukawa directions (consumed: the four
    Retarget exotic pairs `exotic{Re,Im}{NuLeR, ELNuR, ULDR, DLUR}`,
    again via `dirs22`);
  - indices 18-45: the 28 exotic Majorana directions: 4 consumed
    (`exotic{Re,Im}{NuREbarR, EREbarR}`, via `dirs22`) and 24 new,
    built here as single folded-coordinate directions `majDir u v z`
    at the coordinates `(8, v)` and `(9, v)` for `v = 10..15`
    (real and imaginary parts), through the landed parameterization
    `adm32MatOf` of `Census96Decoupling.lean` (so admissibility of the
    new directions is `adm32MatOf_isAdm32`, and order-one is proved by
    one generic entry-pivot support argument, `majDir_orderOne`).
* Membership: by construction — `dir46` is defined into the
  subtype `Sol32` itself, so every `dir46 k` is a census-space
  element on its face (admissibility and order-one are discharged
  inside the definition's terms).
* Independence: `LinearIndependent R dir46` (`dir46_independent`),
  proved by entry pivots: 23 complex pivot entries, one per complex
  coordinate (the SM/flipped pivots are the landed `CFKernel22`
  pivots; the 12 new Majorana pivots are the entries `(u + 16, v)`).

## Kills and fences (on the face)

* K-C96-1 is armed: a proved 47th independent direction would kill
  the census number. None is produced here; the 46 below are exactly
  the registered split 10 + 8 + 28.
* K-C96-2 (vacuity): these are elements of the order-one space with
  independence proved, not parameter slots.
* Generations are IMPOSED; CKM/PMNS input-only; this brick counts
  slots/directions and derives no flavour quantity; Q3 OPEN;
  NO CLAIM. The old 46 -> 10 gloss is UNSOUND AS STATED and is never
  cited as support; the corrected cut 46 -> 22 (`CFKernel22`) stands
  beside this theorem (different space: `IsW22` adds `[D, C_F] = 0`).
-/

open Matrix

namespace ThetLogos

/-! ## Section 1. Single folded coordinates and the Majorana directions -/

/-- The coordinate function on `Upper16` with value `z` at the single
    folded coordinate `(u, v)` and `0` elsewhere. Tier T2. -/
def coordFn (u v : Fin 16) (z : ℂ) : Upper16 → ℂ :=
  fun p => if p.1 = (u, v) then z else 0

theorem symMatOf_coordFn {u v : Fin 16} (huv : u ≤ v) (z : ℂ) (a b : Fin 16) :
    symMatOf (coordFn u v z) a b =
      if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then z else 0 := by
  unfold symMatOf coordFn
  by_cases h : a ≤ b
  · rw [dif_pos h]
    by_cases h1 : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
    · rw [if_pos h1]
      have h2 : (a, b) = (u, v) := by
        rcases h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · rw [Prod.mk.injEq]; exact ⟨h3, h4⟩
        · have hvu : v ≤ u := by
            have h5 : a ≤ b := h
            rw [h3, h4] at h5
            exact h5
          have huv' : u = v := le_antisymm huv hvu
          rw [Prod.mk.injEq]
          exact ⟨h3.trans huv'.symm, h4.trans huv'⟩
      rw [if_pos h2]
    · rw [if_neg h1]
      have h2 : (a, b) ≠ (u, v) := by
        intro hc
        apply h1
        left
        simp only [Prod.mk.injEq] at hc
        exact hc
      rw [if_neg h2]
  · rw [dif_neg h]
    by_cases h1 : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
    · rw [if_pos h1]
      have h2 : (b, a) = (u, v) := by
        rcases h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · have hba : b ≤ a := le_of_not_ge h
          have hvu : v ≤ u := by
            rw [h3, h4] at hba
            exact hba
          have huv' : u = v := le_antisymm huv hvu
          rw [Prod.mk.injEq]
          exact ⟨h4.trans huv'.symm, h3.trans huv'⟩
        · rw [Prod.mk.injEq]; exact ⟨h4, h3⟩
      rw [if_pos h2]
    · rw [if_neg h1]
      have h2 : (b, a) ≠ (u, v) := by
        intro hc
        apply h1
        right
        simp only [Prod.mk.injEq] at hc
        exact ⟨hc.2, hc.1⟩
      rw [if_neg h2]

/-- The exotic Majorana direction at folded coordinate `(u, v)` with
    value `z`: the admissible matrix whose folded symmetric block is
    the single coordinate `(u, v)`. Built through the landed
    parameterization `adm32MatOf`, so `IsAdm32` is free
    (`adm32MatOf_isAdm32`). Tier T2. -/
noncomputable def majDir (u v : Fin 16) (z : ℂ) : Matrix I32 I32 ℂ :=
  adm32MatOf (coordFn u v z)

/-- Entry formula for a Majorana direction, in folded coordinates. -/
theorem majDir_apply {u v : Fin 16} (huv : u ≤ v) (z : ℂ) (i j : I32) :
    majDir u v z i j =
      if gSign i = 1 then
        (if gSign j = 1 then 0 else
          if (acoord i = u ∧ acoord j = v) ∨ (acoord i = v ∧ acoord j = u)
            then z else 0)
      else
        (if gSign j = 1 then
          (if (acoord j = u ∧ acoord i = v) ∨ (acoord j = v ∧ acoord i = u)
            then star z else 0)
          else 0) := by
  unfold majDir
  rw [adm32MatOf_apply, symMatOf_coordFn huv, symMatOf_coordFn huv]
  split_ifs with h1 h2 h3 h4 <;> simp_all

/-- A Majorana direction vanishes at any entry whose folded coordinate
    pair is not its own coordinate (in either order). -/
theorem majDir_eq_zero_of {u v : Fin 16} (huv : u ≤ v) (z : ℂ) {i j : I32}
    (h : ¬ ((acoord i = u ∧ acoord j = v) ∨ (acoord i = v ∧ acoord j = u))) :
    majDir u v z i j = 0 := by
  rw [majDir_apply huv]
  have h' : ¬ ((acoord j = u ∧ acoord i = v) ∨ (acoord j = v ∧ acoord i = u)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h (Or.inr ⟨h2, h1⟩)
    · exact h (Or.inl ⟨h2, h1⟩)
  split_ifs <;> simp_all

/-- Support of a Majorana direction: a nonzero entry has the folded
    coordinate pair of the direction. -/
theorem majDir_ne_zero {u v : Fin 16} (huv : u ≤ v) (z : ℂ) {i j : I32}
    (h : majDir u v z i j ≠ 0) :
    (acoord i = u ∧ acoord j = v) ∨ (acoord i = v ∧ acoord j = u) := by
  by_contra hc
  exact h (majDir_eq_zero_of huv z hc)

/-- Folded-coordinate characterization: `acoord i = a` iff the index is
    `a` or `a + 16`. -/
theorem acoord_eq_iff {i : I32} {a : Fin 16} :
    acoord i = a ↔ i.val = a.val ∨ i.val = a.val + 16 := by
  constructor
  · intro h
    have h2 : i.val % 16 = a.val := by
      have h3 := congrArg Fin.val h
      rwa [acoord_val] at h3
    omega
  · intro h
    apply Fin.ext
    rw [acoord_val]
    rcases h with h | h <;> omega


/-! ## Section 2. The generic order-one proof for Majorana directions

Throughout this section `u v : Fin 16` satisfy `hu : u.val = 8 or 9`
(the lepton-singlet folded rows) and `hv : 10 <= v.val <= 15` (the
right-handed folded columns), and `huv : u <= v`. The direction
`majDir u v z` is supported on the four entries with folded coordinate
pair `{u, v}`; every double commutator is killed by support
disjointness against the generator supports, plus the two diagonal
(`genC` / `genC`-opposite) factor checks. -/

/-- `genCVal` in if-form (unfolding the landed definition). -/
theorem genCVal_ite (x : I32) :
    genCVal x = if (8 ≤ x.val ∧ x.val < 16) ∨ x.val = 16 ∨ x.val = 17 ∨
        x.val = 24 ∨ x.val = 25 then Complex.I else 0 := by
  unfold genCVal
  by_cases h1 : (8 ≤ x.val ∧ x.val < 16)
  · rw [if_pos h1, if_pos (Or.inl h1)]
  · by_cases h2 : x.val = 16 ∨ x.val = 17 ∨ x.val = 24 ∨ x.val = 25
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]
    · rw [if_neg h1, if_neg h2, if_neg (fun hc => by
        rcases hc with (hc | hc | hc | hc | hc)
        · exact h1 hc
        · exact h2 (Or.inl hc)
        · exact h2 (Or.inr (Or.inl hc))
        · exact h2 (Or.inr (Or.inr (Or.inl hc)))
        · exact h2 (Or.inr (Or.inr (Or.inr hc))))]

theorem genCVal_eq_I_of {x : I32}
    (h : (8 ≤ x.val ∧ x.val < 16) ∨ x.val = 16 ∨ x.val = 17 ∨
      x.val = 24 ∨ x.val = 25) : genCVal x = Complex.I := by
  rw [genCVal_ite, if_pos h]

theorem genCVal_eq_zero_of {x : I32}
    (h : ¬ ((8 ≤ x.val ∧ x.val < 16) ∨ x.val = 16 ∨ x.val = 17 ∨
      x.val = 24 ∨ x.val = 25)) : genCVal x = 0 := by
  rw [genCVal_ite, if_neg h]

/-- `genCOpVal` is `genCVal` at the partner index (the landed
    definition, unfolded). -/
theorem genCOpVal_apply (x : I32) : genCOpVal x = genCVal (partner x) := rfl

/-- A nonzero Majorana entry joins indices of opposite grading sign. -/
theorem majDir_eq_zero_of_gSign_eq {u v : Fin 16} (huv : u ≤ v) (z : ℂ)
    {i j : I32} (h : gSign i = gSign j) : majDir u v z i j = 0 := by
  rw [majDir_apply huv]
  rcases gSign_eq_one_or_neg_one i with hi | hi
  · rw [if_pos hi, if_pos (h.symm.trans hi)]
  · have hi' : ¬ gSign i = 1 := by
      rw [hi]
      exact neg_one_ne_one_complex
    have hj' : ¬ gSign j = 1 := by
      rw [← h, hi]
      exact neg_one_ne_one_complex
    rw [if_neg hi', if_neg hj']

theorem majDir_ne_zero_gSign {u v : Fin 16} (huv : u ≤ v) (z : ℂ) {i j : I32}
    (h : majDir u v z i j ≠ 0) : gSign i ≠ gSign j :=
  fun hgj => h (majDir_eq_zero_of_gSign_eq huv z hgj)

/-- Triplet-mate relation: `x` lies in the same colour triplet as the
    index with value `n`. -/
def tripMate (n : Nat) (x : I32) : Prop :=
  ∃ t : Fin 4, ∃ p q : Fin 3,
    tripletOf n = some (t, p) ∧ tripletOf x.val = some (t, q)

theorem tripMate_val_range {n : Nat} {x : I32} (h : tripMate n x) :
    (18 ≤ x.val ∧ x.val < 24) ∨ (26 ≤ x.val ∧ x.val < 32) := by
  obtain ⟨t, p, q, -, hx⟩ := h
  have h2 := tripletOf_eig x.val x.isLt t q hx
  rcases h2 with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- If `n` is in the 26-31 triplet range and `x` is a triplet-mate of
    `n`, then `x` is also in the 26-31 range (the triplet label of a
    26-31 index is at least 2, and labels at least 2 live at 26-31). -/
theorem tripMate_val_ge {n : Nat} (hn : 26 ≤ n ∧ n < 32) {x : I32}
    (h : tripMate n x) : 26 ≤ x.val ∧ x.val < 32 := by
  obtain ⟨t, p, q, hn', hx⟩ := h
  have ht := tripletOf_eig n (by omega) t p hn'
  have hx2 := tripletOf_eig x.val x.isLt t q hx
  rcases ht with ⟨ht1, h1, h2⟩ | ⟨ht1, h1, h2⟩
  · omega
  · rcases hx2 with ⟨h3, -, -⟩ | ⟨-, h3, h4⟩
    · omega
    · exact ⟨h3, h4⟩

/-- Double-commutator vanishing from support confinement: if the
    commutator `C` has all its nonzero entries' column indices in `P`
    (in both positions) and `Y` has all its nonzero entries' column
    indices in `Q` (in both positions), with `Q` disjoint from `P`,
    then `[C, Y] = 0`. Assembled from the landed `disjoint_mul_zero`. -/
theorem dcomm_eq_zero_of_support {C Y : Matrix I32 I32 ℂ}
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
    entry of `C` joins indices of equal `genCOpVal`, then `C` commutes
    with `smGenOp 0`. -/
theorem comm_genOpC_eq_zero_of {C : Matrix I32 I32 ℂ}
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

/-- `gSign` at indices 24-31 is `1`. -/
theorem gSign_eq_one_of_ge_24 {x : I32} (hx : 24 ≤ x.val) : gSign x = 1 := by
  rw [gSign_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rfl

/-- If `gSign x` is not `1`, the index lies in the minus range 8-23. -/
theorem val_range_of_gSign_ne_one {x : I32} (h : gSign x ≠ 1) :
    8 ≤ x.val ∧ x.val < 24 := by
  by_cases h8 : x.val < 8
  · exfalso
    apply h
    rw [gSign_apply, if_pos h8]
  · by_cases h24 : 24 ≤ x.val
    · exfalso
      exact h (gSign_eq_one_of_ge_24 h24)
    · omega

/-- The `genCVal`/`genCOpVal` evaluation table at the four index
    values a Majorana direction at `(u, v)` can touch. -/
theorem genC_table {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 10 ≤ v.val ∧ v.val ≤ 15) {x : I32}
    (hx : x.val = u.val ∨ x.val = u.val + 16 ∨ x.val = v.val ∨
      x.val = v.val + 16) :
    (x.val = u.val ∧ genCVal x = Complex.I ∧ genCOpVal x = Complex.I) ∨
    (x.val = u.val + 16 ∧ genCVal x = Complex.I ∧ genCOpVal x = Complex.I) ∨
    (x.val = v.val ∧ genCVal x = Complex.I ∧ genCOpVal x = 0) ∨
    (x.val = v.val + 16 ∧ genCVal x = 0 ∧ genCOpVal x = Complex.I) := by
  rcases hx with hx | hx | hx | hx
  · refine Or.inl ⟨hx, genCVal_eq_I_of (by omega), ?_⟩
    rw [genCOpVal_apply]
    have hp : (partner x).val = u.val + 16 := by
      rw [partner_val_eq, if_pos (by omega), hx]
    exact genCVal_eq_I_of (by omega)
  · refine Or.inr (Or.inl ⟨hx, genCVal_eq_I_of (by omega), ?_⟩)
    rw [genCOpVal_apply]
    have hp : (partner x).val = u.val := by
      rw [partner_val_eq, if_neg (by omega)]
      omega
    exact genCVal_eq_I_of (by omega)
  · refine Or.inr (Or.inr (Or.inl ⟨hx, genCVal_eq_I_of (by omega), ?_⟩))
    rw [genCOpVal_apply]
    have hp : (partner x).val = v.val + 16 := by
      rw [partner_val_eq, if_pos (by omega), hx]
    exact genCVal_eq_zero_of (by omega)
  · refine Or.inr (Or.inr (Or.inr ⟨hx, genCVal_eq_zero_of (by omega), ?_⟩))
    rw [genCOpVal_apply]
    have hp : (partner x).val = v.val := by
      rw [partner_val_eq, if_neg (by omega)]
      omega
    exact genCVal_eq_I_of (by omega)

/-- Evaluation table at an index with folded coordinate `u`. -/
theorem genC_table_u {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 10 ≤ v.val ∧ v.val ≤ 15) {x : I32} (hx : acoord x = u) :
    genCVal x = Complex.I ∧ genCOpVal x = Complex.I := by
  rw [acoord_eq_iff] at hx
  rcases genC_table hu hv (x := x) (by omega) with
    ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h3, -, -⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · omega
  · omega

/-- Evaluation table at an index with folded coordinate `v`. -/
theorem genC_table_v {u v : Fin 16} (hu : u.val = 8 ∨ u.val = 9)
    (hv : 10 ≤ v.val ∧ v.val ≤ 15) {x : I32} (hx : acoord x = v) :
    (x.val = v.val ∧ genCVal x = Complex.I ∧ genCOpVal x = 0) ∨
    (x.val = v.val + 16 ∧ genCVal x = 0 ∧ genCOpVal x = Complex.I) := by
  rw [acoord_eq_iff] at hx
  rcases genC_table hu hv (x := x) (by omega) with
    ⟨h3, -, -⟩ | ⟨h3, -, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · omega
  · omega
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h1, h2, h3⟩

/-- The `(genC, genC°)` factor condition for a Majorana direction:
    at every support entry, one of the two charge-difference factors
    vanishes. -/
theorem majDir_factor_CC {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (i j : I32) (h : majDir u v z i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  have hcoord := majDir_ne_zero huv z h
  rcases hcoord with ⟨hai, haj⟩ | ⟨hai, haj⟩
  · obtain ⟨hCi, hOi⟩ := genC_table_u hu hv hai
    rcases genC_table_v hu hv haj with ⟨-, hCj, -⟩ | ⟨-, -, hOj⟩
    · rw [hCj, hCi, sub_self, zero_mul]
    · rw [hOj, hOi, sub_self, mul_zero]
  · obtain ⟨hCj, hOj⟩ := genC_table_u hu hv haj
    rcases genC_table_v hu hv hai with ⟨-, hCi, -⟩ | ⟨-, -, hOi⟩
    · rw [hCi, hCj, sub_self, zero_mul]
    · rw [hOi, hOj, sub_self, mul_zero]

/-- Support of the commutator `[D, genC]` of a Majorana direction:
    only the two entries `(v + 16, u)` and `(u, v + 16)` can be
    nonzero (the other two support entries have equal `genC` charges
    on both indices). -/
theorem majDir_comm_genC_support {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    {i j : I32}
    (h : (majDir u v z * genC - genC * majDir u v z) i j ≠ 0) :
    (i.val = v.val + 16 ∧ j.val = u.val) ∨
    (i.val = u.val ∧ j.val = v.val + 16) := by
  have h2 := comm_diag_entry (majDir u v z) genCVal genC
    (fun x y => genC_eq_diag x y) i j
  rw [h2] at h
  obtain ⟨hD, hC⟩ := mul_ne_zero_iff.mp h
  have hcoord := majDir_ne_zero huv z hD
  have hg := majDir_ne_zero_gSign huv z hD
  rcases hcoord with ⟨hai, haj⟩ | ⟨hai, haj⟩
  · obtain ⟨hCi, -⟩ := genC_table_u hu hv hai
    rcases genC_table_v hu hv haj with ⟨-, hCj, -⟩ | ⟨hvalj, hCj, -⟩
    · rw [hCj, hCi, sub_self] at hC
      exact absurd rfl hC
    · have hgj : gSign j = 1 := gSign_eq_one_of_ge_24 (by omega)
      have hgi : gSign i ≠ 1 := fun hh => hg (hh.trans hgj.symm)
      have hrange := val_range_of_gSign_ne_one hgi
      rw [acoord_eq_iff] at hai
      exact Or.inr ⟨by omega, hvalj⟩
  · obtain ⟨hCj, -⟩ := genC_table_u hu hv haj
    rcases genC_table_v hu hv hai with ⟨-, hCi, -⟩ | ⟨hvali, hCi, -⟩
    · rw [hCi, hCj, sub_self] at hC
      exact absurd rfl hC
    · have hgi : gSign i = 1 := gSign_eq_one_of_ge_24 (by omega)
      have hgj : gSign j ≠ 1 := fun hh => hg (hgi.trans hh.symm)
      have hrange := val_range_of_gSign_ne_one hgj
      rw [acoord_eq_iff] at haj
      exact Or.inl ⟨hvali, by omega⟩

/-- A nonzero entry of a matrix product has a nonzero path. -/
theorem mul_apply_ne_zero_extract {A B : Matrix I32 I32 ℂ} {i j : I32}
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

/-- Support of the commutator `[D, genM a]` of a Majorana direction:
    nonzero entries join the singlet index `u` to the colour triplet
    of `v + 16`. -/
theorem majDir_comm_genM_support {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) {i j : I32}
    (h : (majDir u v z * genM a - genM a * majDir u v z) i j ≠ 0) :
    (i.val = u.val ∧ tripMate (v.val + 16) j) ∨
    (tripMate (v.val + 16) i ∧ j.val = u.val) := by
  have hne : (majDir u v z * genM a) i j ≠ 0 ∨
      (genM a * majDir u v z) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [Matrix.sub_apply, hc.1, hc.2, sub_self])
  rcases hne with hDG | hGD
  · obtain ⟨l, hDl, hGl⟩ := mul_apply_ne_zero_extract hDG
    obtain ⟨t, p, q, hlt, hjt⟩ := genM_supp_triplet a l j hGl
    have hrange : (18 ≤ l.val ∧ l.val < 24) ∨ (26 ≤ l.val ∧ l.val < 32) :=
      (genM_supp a l j hGl).1
    have hcoord := majDir_ne_zero huv z hDl
    have hg := majDir_ne_zero_gSign huv z hDl
    have hlv : acoord l = v := by
      rcases hcoord with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact h2
      · exfalso
        rw [acoord_eq_iff] at h2
        rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> omega
    have hlval : l.val = v.val + 16 := by
      rw [acoord_eq_iff] at hlv
      rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> omega
    have hai : acoord i = u := by
      rcases hcoord with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso
        have huv' : u = v := h2.symm.trans hlv
        have h3 := congrArg Fin.val huv'
        omega
    have hgl : gSign l = 1 := gSign_eq_one_of_ge_24 (by omega)
    have hgi : gSign i ≠ 1 := fun hh => hg (hh.trans hgl.symm)
    have hrangei := val_range_of_gSign_ne_one hgi
    have hival : i.val = u.val := by
      rw [acoord_eq_iff] at hai
      omega
    exact Or.inl ⟨hival, t, p, q, by rwa [hlval] at hlt, hjt⟩
  · obtain ⟨l, hGl, hDl⟩ := mul_apply_ne_zero_extract hGD
    obtain ⟨t, p, q, hit, hlt⟩ := genM_supp_triplet a i l hGl
    have hrange : (18 ≤ l.val ∧ l.val < 24) ∨ (26 ≤ l.val ∧ l.val < 32) :=
      (genM_supp a i l hGl).2
    have hcoord := majDir_ne_zero huv z hDl
    have hg := majDir_ne_zero_gSign huv z hDl
    have hlv : acoord l = v := by
      rcases hcoord with ⟨h2, -⟩ | ⟨h2, -⟩
      · exfalso
        rw [acoord_eq_iff] at h2
        rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> omega
      · exact h2
    have hlval : l.val = v.val + 16 := by
      rw [acoord_eq_iff] at hlv
      rcases hrange with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;> omega
    have haj : acoord j = u := by
      rcases hcoord with ⟨h2, h1⟩ | ⟨-, h1⟩
      · exfalso
        have huv' : u = v := h2.symm.trans hlv
        have h3 := congrArg Fin.val huv'
        omega
      · exact h1
    have hgl : gSign l = 1 := gSign_eq_one_of_ge_24 (by omega)
    have hgj : gSign j ≠ 1 := fun hh => hg (hgl.trans hh.symm)
    have hrangej := val_range_of_gSign_ne_one hgj
    have hjval : j.val = u.val := by
      rw [acoord_eq_iff] at haj
      omega
    exact Or.inr ⟨⟨t, q, p, by rwa [hlval] at hlt, hit⟩, hjval⟩

/-- A Majorana direction commutes with every `genH k`: its support
    indices avoid the doublet range 0-7 entirely. -/
theorem majDir_comm_genH_eq_zero {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (k : Fin 3) :
    majDir u v z * genH k - genH k * majDir u v z = 0 := by
  have hDcol : ∀ i l, majDir u v z i l ≠ 0 → 8 ≤ l.val := by
    intro i l hl
    have hc := majDir_ne_zero huv z hl
    rcases hc with ⟨-, h2⟩ | ⟨-, h2⟩ <;>
      rw [acoord_eq_iff] at h2 <;> omega
  have hDrow : ∀ l j, majDir u v z l j ≠ 0 → 8 ≤ l.val := by
    intro l j hl
    have hc := majDir_ne_zero huv z hl
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rw [acoord_eq_iff] at h1 <;> omega
  have h1 : majDir u v z * genH k = 0 := by
    apply disjoint_mul_zero (fun x => 8 ≤ x.val)
    · exact hDcol
    · intro l j hlj
      have h2 := (genH_supp k l j hlj).1
      omega
  have h2 : genH k * majDir u v z = 0 := by
    apply disjoint_mul_zero (fun x => x.val < 8)
    · intro i l hil
      exact (genH_supp k i l hil).2
    · intro l j hlj
      have h3 := hDrow l j hlj
      omega
  rw [h1, h2, sub_self]

/-- `genCOpVal` at a 26-31 index is `Complex.I` (its partner is a
    right-handed particle index). -/
theorem genCOpVal_eq_I_of_ge_26 {x : I32} (hx : 26 ≤ x.val ∧ x.val < 32) :
    genCOpVal x = Complex.I := by
  rw [genCOpVal_apply]
  have hp : (partner x).val = x.val - 16 := by
    rw [partner_val_eq, if_neg (by omega)]
  exact genCVal_eq_I_of (by omega)

/-- Double commutators of `[D, genC]` against the `genH` opposites. -/
theorem majDir_dcomm_genC_genHOp {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (k : Fin 3) :
    (majDir u v z * genC - genC * majDir u v z) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ)
        * (majDir u v z * genC - genC * majDir u v z) = 0 := by
  apply dcomm_eq_zero_of_support
    (fun x => x.val = v.val + 16 ∨ x.val = u.val)
    (fun x => 16 ≤ x.val ∧ x.val < 24)
  · intro i k2 hik
    have hs := majDir_comm_genC_support huv hu hv z hik
    rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  · intro k2 j hkj
    have hs := majDir_comm_genC_support huv hu hv z hkj
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro i k2 hik
    have hs := UJ_genH_transpose_UJ_supp k i k2 hik
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · intro k2 j hkj
    have hs := UJ_genH_transpose_UJ_supp k k2 j hkj
    exact ⟨hs.1, hs.2.1⟩
  · intro k2 ⟨h1, h2⟩ h3
    rcases h3 with h3 | h3 <;> omega

/-- Double commutators of `[D, genC]` against the `genM` opposites. -/
theorem majDir_dcomm_genC_genMOp {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) :
    (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ)
        * (majDir u v z * genC - genC * majDir u v z) = 0 := by
  apply dcomm_eq_zero_of_support
    (fun x => x.val = v.val + 16 ∨ x.val = u.val)
    (fun x => (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16))
  · intro i k2 hik
    have hs := majDir_comm_genC_support huv hu hv z hik
    rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  · intro k2 j hkj
    have hs := majDir_comm_genC_support huv hu hv z hkj
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro i k2 hik
    have hs := UJ_genM_transpose_UJ_supp a i k2 hik
    exact hs.2
  · intro k2 j hkj
    have hs := UJ_genM_transpose_UJ_supp a k2 j hkj
    exact hs.1
  · intro k2 h1 h3
    rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h3 with h3 | h3 <;> omega

/-- All double commutators with first generator `genC`. -/
theorem majDir_oo_genC {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (g2 : Fin 12) :
    (majDir u v z * genC - genC * majDir u v z) * smGenOp g2
      - smGenOp g2 * (majDir u v z * genC - genC * majDir u v z) = 0 := by
  fin_cases g2
  · exact oo_C_C_of_factor _ (majDir_factor_CC huv hu hv z)
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genHOp huv hu hv z 0
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genHOp huv hu hv z 1
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genHOp huv hu hv z 2
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 0
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 1
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 2
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 3
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 4
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 5
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 6
  · show (majDir u v z * genC - genC * majDir u v z) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ)
          * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_dcomm_genC_genMOp huv hu hv z 7

/-- Double commutators of `[D, genM a]` against the `genH` opposites. -/
theorem majDir_dcomm_genM_genHOp {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) (k : Fin 3) :
    (majDir u v z * genM a - genM a * majDir u v z)
        * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ)
        * (majDir u v z * genM a - genM a * majDir u v z) = 0 := by
  apply dcomm_eq_zero_of_support
    (fun x => x.val = u.val ∨ tripMate (v.val + 16) x)
    (fun x => 16 ≤ x.val ∧ x.val < 24)
  · intro i k2 hik
    have hs := majDir_comm_genM_support huv hu hv z a hik
    rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  · intro k2 j hkj
    have hs := majDir_comm_genM_support huv hu hv z a hkj
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro i k2 hik
    have hs := UJ_genH_transpose_UJ_supp k i k2 hik
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · intro k2 j hkj
    have hs := UJ_genH_transpose_UJ_supp k k2 j hkj
    exact ⟨hs.1, hs.2.1⟩
  · intro k2 ⟨h1, h2⟩ h3
    rcases h3 with h3 | h3
    · omega
    · have h4 := tripMate_val_ge (n := v.val + 16) (by omega) h3
      omega

/-- Double commutators of `[D, genM a]` against the `genM` opposites. -/
theorem majDir_dcomm_genM_genMOp {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a b : Fin 8) :
    (majDir u v z * genM a - genM a * majDir u v z)
        * (UJ * (genM b).transpose * UJ)
      - (UJ * (genM b).transpose * UJ)
        * (majDir u v z * genM a - genM a * majDir u v z) = 0 := by
  apply dcomm_eq_zero_of_support
    (fun x => x.val = u.val ∨ tripMate (v.val + 16) x)
    (fun x => (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16))
  · intro i k2 hik
    have hs := majDir_comm_genM_support huv hu hv z a hik
    rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  · intro k2 j hkj
    have hs := majDir_comm_genM_support huv hu hv z a hkj
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro i k2 hik
    have hs := UJ_genM_transpose_UJ_supp b i k2 hik
    exact hs.2
  · intro k2 j hkj
    have hs := UJ_genM_transpose_UJ_supp b k2 j hkj
    exact hs.1
  · intro k2 h1 h3
    rcases h3 with h3 | h3
    · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have h4 := tripMate_val_range h3
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega

/-- All double commutators with first generator `genM a`. -/
theorem majDir_oo_genM {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ)
    (a : Fin 8) (g2 : Fin 12) :
    (majDir u v z * genM a - genM a * majDir u v z) * smGenOp g2
      - smGenOp g2 * (majDir u v z * genM a - genM a * majDir u v z) = 0 := by
  fin_cases g2
  · apply comm_genOpC_eq_zero_of
    intro i j hij
    have hs := majDir_comm_genM_support huv hu hv z a hij
    rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have h1 : genCOpVal i = Complex.I := by
        have h2 := (genC_table_u hu hv (x := i)
          (acoord_eq_iff.mpr (Or.inl hi))).2
        exact h2
      have h2 : genCOpVal j = Complex.I :=
        genCOpVal_eq_I_of_ge_26 (tripMate_val_ge (n := v.val + 16)
          (by omega) hj)
      rw [h1, h2]
    · have h1 : genCOpVal j = Complex.I :=
        (genC_table_u hu hv (x := j)
          (acoord_eq_iff.mpr (Or.inl hj))).2
      have h2 : genCOpVal i = Complex.I :=
        genCOpVal_eq_I_of_ge_26 (tripMate_val_ge (n := v.val + 16)
          (by omega) hi)
      rw [h1, h2]
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genHOp huv hu hv z a 0
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genHOp huv hu hv z a 1
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genHOp huv hu hv z a 2
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 0
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 1
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 2
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 3
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 4
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 5
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 6
  · show (majDir u v z * genM a - genM a * majDir u v z)
          * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ)
          * (majDir u v z * genM a - genM a * majDir u v z) = 0
    exact majDir_dcomm_genM_genMOp huv hu hv z a 7

/-- **The generic Majorana order-one theorem.** Every single-coordinate
    direction at a lepton-singlet row `u` (8 or 9) and a right-handed
    column `v` (10-15) satisfies the order-one condition. -/
theorem majDir_orderOne {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ) :
    OrderOneHolds (majDir u v z) := by
  intro g1 g2
  fin_cases g1
  · show (majDir u v z * genC - genC * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genC - genC * majDir u v z) = 0
    exact majDir_oo_genC huv hu hv z g2
  · show (majDir u v z * genH 0 - genH 0 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genH 0 - genH 0 * majDir u v z) = 0
    rw [majDir_comm_genH_eq_zero huv hu hv z 0, zero_mul, mul_zero, sub_zero]
  · show (majDir u v z * genH 1 - genH 1 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genH 1 - genH 1 * majDir u v z) = 0
    rw [majDir_comm_genH_eq_zero huv hu hv z 1, zero_mul, mul_zero, sub_zero]
  · show (majDir u v z * genH 2 - genH 2 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genH 2 - genH 2 * majDir u v z) = 0
    rw [majDir_comm_genH_eq_zero huv hu hv z 2, zero_mul, mul_zero, sub_zero]
  · show (majDir u v z * genM 0 - genM 0 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 0 - genM 0 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 0 g2
  · show (majDir u v z * genM 1 - genM 1 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 1 - genM 1 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 1 g2
  · show (majDir u v z * genM 2 - genM 2 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 2 - genM 2 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 2 g2
  · show (majDir u v z * genM 3 - genM 3 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 3 - genM 3 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 3 g2
  · show (majDir u v z * genM 4 - genM 4 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 4 - genM 4 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 4 g2
  · show (majDir u v z * genM 5 - genM 5 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 5 - genM 5 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 5 g2
  · show (majDir u v z * genM 6 - genM 6 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 6 - genM 6 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 6 g2
  · show (majDir u v z * genM 7 - genM 7 * majDir u v z) * smGenOp g2
        - smGenOp g2 * (majDir u v z * genM 7 - genM 7 * majDir u v z) = 0
    exact majDir_oo_genM huv hu hv z 7 g2

/-! ## Section 3. The 46-direction family and its membership -/

/-- Folded row coordinate of the `n`-th new Majorana direction:
    `8` for the first twelve (the `(8, v)` coordinates), `9` for the
    last twelve. -/
def newMajU (n : Nat) : Fin 16 := ⟨if n < 12 then 8 else 9, by split_ifs <;> omega⟩

/-- Folded column coordinate of the `n`-th new Majorana direction:
    `10 + (n % 12) / 2`, cycling through `10..15` in each dozen. -/
def newMajV (n : Nat) : Fin 16 :=
  ⟨10 + (n % 12) / 2, by
    have h := Nat.mod_lt n (show 0 < 12 by norm_num)
    omega⟩

/-- Phase of the `n`-th new Majorana direction: even `n` is the real
    part of its coordinate, odd `n` the imaginary part. -/
def newMajZ (n : Nat) : ℂ := if n % 2 = 0 then 1 else Complex.I

/-- The 24 new exotic Majorana directions, as a Nat-indexed family:
    (real, imaginary) pairs at the folded coordinates `(8, 10..15)`
    (indices 0-11) and `(9, 10..15)` (indices 12-23), each the
    single-coordinate direction `majDir (newMajU n) (newMajV n)
    (newMajZ n)`. -/
noncomputable def newMajAux (n : Nat) : Matrix I32 I32 ℂ :=
  majDir (newMajU n) (newMajV n) (newMajZ n)

theorem newMajU_val (n : Nat) : (newMajU n).val = if n < 12 then 8 else 9 :=
  rfl

theorem newMajV_val (n : Nat) : (newMajV n).val = 10 + (n % 12) / 2 :=
  rfl

theorem newMajU_le_newMajV (n : Nat) : newMajU n ≤ newMajV n := by
  rw [Fin.le_iff_val_le_val, newMajU_val, newMajV_val]
  split_ifs <;> omega

theorem newMajU_spec (n : Nat) :
    (newMajU n).val = 8 ∨ (newMajU n).val = 9 := by
  rw [newMajU_val]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem newMajV_spec (n : Nat) :
    10 ≤ (newMajV n).val ∧ (newMajV n).val ≤ 15 := by
  rw [newMajV_val]
  have h := Nat.mod_lt n (show 0 < 12 by norm_num)
  omega

/-- Membership of the new Majorana directions: admissibility is the
    landed `adm32MatOf_isAdm32`; order-one is the generic
    `majDir_orderOne`. -/
theorem newMajAux_mem (n : Nat) : newMajAux n ∈ Sol32 :=
  ⟨adm32MatOf_isAdm32 _,
    majDir_orderOne (newMajU_le_newMajV n) (newMajU_spec n)
      (newMajV_spec n) _⟩

/-- Every `IsW22` direction lies in the census space `Sol32`
    (drop the `cfMat` component of `IsW22`). -/
theorem mem_Sol32_of_isW22 {D : Matrix I32 I32 ℂ} (h : IsW22 D) :
    D ∈ Sol32 :=
  ⟨⟨h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩, h.1⟩

/-- The 46 census directions as plain matrices: indices 0-21 are the
    landed `dirs22` family (10 SM + 8 flipped + 4 exotic Majorana),
    indices 22-45 are the 24 new exotic Majorana directions. -/
noncomputable def dir46Mat (k : Fin 46) : Matrix I32 I32 ℂ :=
  if h : k.val < 22 then dirs22 ⟨k.val, h⟩ else newMajAux (k.val - 22)

theorem dir46Mat_of_lt {k : Fin 46} (h : k.val < 22) :
    dir46Mat k = dirs22 ⟨k.val, h⟩ :=
  dif_pos h

theorem dir46Mat_of_ge {k : Fin 46} (h : 22 ≤ k.val) :
    dir46Mat k = newMajAux (k.val - 22) :=
  dif_neg (by omega)

/-- **Membership (C96-2a headline 1).** Every one of the 46 directions
    lies in the one-generation census space
    `Sol32 = {D | IsAdm32 D /\ OrderOneHolds D}`. -/
theorem dir46Mat_mem (k : Fin 46) : dir46Mat k ∈ Sol32 := by
  by_cases h : k.val < 22
  · rw [dir46Mat_of_lt h]
    exact mem_Sol32_of_isW22 (dirs22_mem ⟨k.val, h⟩)
  · rw [dir46Mat_of_ge (by omega : 22 ≤ k.val)]
    exact newMajAux_mem (k.val - 22)

/-- **The 46 directions (C96-2a deliverable family).**
    `dir46 : Fin 46 -> Sol32`, organized as 10 SM (indices 0-9),
    8 flipped Yukawas (indices 10-17), 28 exotic Majorana
    (indices 18-45). -/
noncomputable def dir46 (k : Fin 46) : Sol32 :=
  ⟨dir46Mat k, dir46Mat_mem k⟩

theorem dir46_coe (k : Fin 46) : (dir46 k : Matrix I32 I32 ℂ) = dir46Mat k :=
  rfl

/-! ## Section 4. Linear independence by entry pivots -/

/-- Pivot extraction for the 46-family: if a pivot entry `(r, c)`
    sees only the pair `(a, b)` with values `1` and `Complex.I`, then
    a vanishing real-linear combination has `g a = 0` and `g b = 0`.
    (The `CFKernel22.pivot_extract` argument, for `dir46Mat`.) -/
theorem pivot_extract46 (r c : I32) (a b : Fin 46) (hab : a ≠ b)
    (hva : dir46Mat a r c = 1) (hvb : dir46Mat b r c = Complex.I)
    (hvan : ∀ i : Fin 46, i ≠ a → i ≠ b → dir46Mat i r c = 0)
    (g : Fin 46 → ℝ) (hg : ∑ i, g i • dir46Mat i = 0) :
    g a = 0 ∧ g b = 0 := by
  have hP : ∑ i : Fin 46, (g i • dir46Mat i) r c = 0 := by
    have h := congrFun (congrFun hg r) c
    rwa [Matrix.sum_apply] at h
  have hcollapse : ∑ i : Fin 46, (g i • dir46Mat i) r c
      = (g a • dir46Mat a) r c + (g b • dir46Mat b) r c := by
    have h1 : ∑ i : Fin 46, (g i • dir46Mat i) r c
        = ∑ i ∈ ({a, b} : Finset (Fin 46)), (g i • dir46Mat i) r c := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro x _ hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      have hx' := not_or.mp hx
      have hv := hvan x hx'.1 hx'.2
      show (g x) • ((dir46Mat x) r c) = 0
      rw [hv, smul_zero]
    have h2 : ∑ i ∈ ({a, b} : Finset (Fin 46)), (g i • dir46Mat i) r c
        = (g a • dir46Mat a) r c + (g b • dir46Mat b) r c :=
      Finset.sum_pair hab
    rw [h1, h2]
  rw [hcollapse] at hP
  have hP2 : (g a) • (dir46Mat a r c) + (g b) • (dir46Mat b r c) = 0 := hP
  rw [hva, hvb] at hP2
  have h' : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I = 0 := by
    have e1 : (g a) • (1:ℂ) = ((g a : ℝ) : ℂ) := by simp
    have e2 : (g b) • Complex.I = ((g b : ℝ) : ℂ) * Complex.I := by simp
    rw [e1, e2] at hP2
    simpa using hP2
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp at hre him
  exact ⟨hre, him⟩

/-- Index conversion for pivot side conditions: `i ≠ a` in `Fin 46`
    gives the corresponding inequality in `Fin 22`. -/
theorem fin22_ne_of_fin46_ne {i a : Fin 46} (hi : i.val < 22) (ha : i ≠ a)
    (ha22 : a.val < 22) : (⟨i.val, hi⟩ : Fin 22) ≠ ⟨a.val, ha22⟩ := by
  intro hcon
  have e := congrArg (@Fin.val 22) hcon
  exact ha (Fin.ext e)

/-- `gSign` at indices 8-23 is `-1`. -/
theorem gSign_eq_neg_one_of_range {x : I32} (h1 : 8 ≤ x.val)
    (h2 : x.val < 24) : gSign x = -1 := by
  rw [gSign_apply]
  split_ifs with ha hb hc <;> first | rfl | (exfalso; omega)

/-- The pivot entry of a Majorana direction: at `(u + 16, v)` the
    value is exactly the coordinate value `z`. -/
theorem majDir_pivot {u v : Fin 16} (huv : u ≤ v)
    (hu : u.val = 8 ∨ u.val = 9) (hv : 10 ≤ v.val ∧ v.val ≤ 15) (z : ℂ) :
    majDir u v z ⟨u.val + 16, by have h := u.isLt; omega⟩
        ⟨v.val, by have h := v.isLt; omega⟩ = z := by
  have hu16 := u.isLt
  have hv16 := v.isLt
  have hgi : gSign (⟨u.val + 16, by omega⟩ : I32) = 1 :=
    gSign_eq_one_of_ge_24 (by show 24 ≤ u.val + 16; omega)
  have hgj : ¬ gSign (⟨v.val, by omega⟩ : I32) = 1 := by
    have h2 : gSign (⟨v.val, by omega⟩ : I32) = -1 :=
      gSign_eq_neg_one_of_range (by show 8 ≤ v.val; omega)
        (by show v.val < 24; omega)
    rw [h2]
    exact neg_one_ne_one_complex
  have hai : acoord (⟨u.val + 16, by omega⟩ : I32) = u := by
    apply Fin.ext
    rw [acoord_val]
    show (u.val + 16) % 16 = u.val
    omega
  have haj : acoord (⟨v.val, by omega⟩ : I32) = v := by
    apply Fin.ext
    rw [acoord_val]
    show v.val % 16 = v.val
    omega
  rw [majDir_apply huv, if_pos hgi, if_neg hgj, if_pos (Or.inl ⟨hai, haj⟩)]

/-- The pivot entry of the `n`-th new Majorana direction is its
    phase `newMajZ n`. -/
theorem newMajAux_pivot (n : Nat) :
    newMajAux n ⟨(newMajU n).val + 16, by have h := (newMajU n).isLt; omega⟩
        ⟨(newMajV n).val, by have h := (newMajV n).isLt; omega⟩
      = newMajZ n :=
  majDir_pivot (newMajU_le_newMajV n) (newMajU_spec n) (newMajV_spec n) _

/-- Support of a new Majorana direction, in folded coordinates. -/
theorem newMajAux_ne_zero_coord (n : Nat) {r c : I32}
    (h : newMajAux n r c ≠ 0) :
    (acoord r = newMajU n ∧ acoord c = newMajV n) ∨
    (acoord r = newMajV n ∧ acoord c = newMajU n) :=
  majDir_ne_zero (newMajU_le_newMajV n) _ h

/-- Vanishing of new Majorana directions at entries whose folded
    coordinates cannot match any new coordinate: if in both orders,
    the pair of folded coordinates of `(r, c)` fails the
    (row in {8, 9}, column in 10..15) pattern, every new direction
    vanishes at `(r, c)`. -/
theorem newMajAux_eq_zero_of_vals (n : Nat) {r c : I32}
    (h : ¬ (((acoord r).val = 8 ∨ (acoord r).val = 9) ∧
          10 ≤ (acoord c).val ∧ (acoord c).val ≤ 15) ∧
        ¬ (((acoord c).val = 8 ∨ (acoord c).val = 9) ∧
          10 ≤ (acoord r).val ∧ (acoord r).val ≤ 15)) :
    newMajAux n r c = 0 := by
  apply majDir_eq_zero_of (newMajU_le_newMajV n)
  intro hc
  have hu := newMajU_spec n
  have hv := newMajV_spec n
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := congrArg Fin.val h1
    have e2 := congrArg Fin.val h2
    exact h.1 ⟨by omega, by omega, by omega⟩
  · have e1 := congrArg Fin.val h1
    have e2 := congrArg Fin.val h2
    exact h.2 ⟨by omega, by omega, by omega⟩

/-- `smDirac` vanishes off its support (the landed
    `smDirac_supp_aux` characterization, contrapositive form). -/
theorem smDirac_eq_zero_of_not_supp {yNu yE yU yD yR : ℂ} {r c : I32}
    (h : ¬ ((r.val < 8 ∧ c.val = r.val + 8) ∨
        (8 ≤ r.val ∧ r.val < 16 ∧ c.val = r.val - 8) ∨
        (16 ≤ r.val ∧ r.val < 24 ∧ c.val = r.val + 8) ∨
        (24 ≤ r.val ∧ r.val < 32 ∧ c.val = r.val - 8) ∨
        (r.val = 8 ∧ c.val = 24) ∨ (r.val = 24 ∧ c.val = 8))) :
    smDirac yNu yE yU yD yR r c = 0 := by
  by_contra hc
  exact h (smDirac_supp_aux _ _ _ _ _ _ _ hc)

/-- Every landed `dirs22` direction vanishes at a new Majorana pivot
    `(r, c)` (`r` in {24, 25}, `c` in 10..15): the SM directions by
    their support characterization, the Retarget exotics by their
    support lists. -/
theorem dirs22_eq_zero_of_newpivot {r c : I32} (hr : r.val = 24 ∨ r.val = 25)
    (hc : 10 ≤ c.val ∧ c.val ≤ 15) (i : Fin 22) : dirs22 i r c = 0 := by
  have hns : ¬ ((r.val < 8 ∧ c.val = r.val + 8) ∨
      (8 ≤ r.val ∧ r.val < 16 ∧ c.val = r.val - 8) ∨
      (16 ≤ r.val ∧ r.val < 24 ∧ c.val = r.val + 8) ∨
      (24 ≤ r.val ∧ r.val < 32 ∧ c.val = r.val - 8) ∨
      (r.val = 8 ∧ c.val = 24) ∨ (r.val = 24 ∧ c.val = 8)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  fin_cases i
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
  · exact smDirac_eq_zero_of_not_supp hns
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

/-! ### The eleven landed pivots, transported to `dir46Mat` -/

/-- Pivot value (real part) at `(0, 8)`. -/
theorem hva46_08 : dir46Mat 0 0 8 = 1 := by
  rw [dir46Mat_of_lt (by decide : (0 : Fin 46).val < 22)]
  exact hva_08

/-- Pivot value (imaginary part) at `(0, 8)`. -/
theorem hvb46_08 : dir46Mat 1 0 8 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (1 : Fin 46).val < 22)]
  exact hvb_08

/-- Vanishing at `(0, 8)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_08 (i : Fin 46) (ha : i ≠ 0) (hb : i ≠ 1) :
    dir46Mat i 0 8 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_08 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(1, 9)`. -/
theorem hva46_19 : dir46Mat 2 1 9 = 1 := by
  rw [dir46Mat_of_lt (by decide : (2 : Fin 46).val < 22)]
  exact hva_19

/-- Pivot value (imaginary part) at `(1, 9)`. -/
theorem hvb46_19 : dir46Mat 3 1 9 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (3 : Fin 46).val < 22)]
  exact hvb_19

/-- Vanishing at `(1, 9)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_19 (i : Fin 46) (ha : i ≠ 2) (hb : i ≠ 3) :
    dir46Mat i 1 9 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_19 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(2, 10)`. -/
theorem hva46_2_10 : dir46Mat 4 2 10 = 1 := by
  rw [dir46Mat_of_lt (by decide : (4 : Fin 46).val < 22)]
  exact hva_2_10

/-- Pivot value (imaginary part) at `(2, 10)`. -/
theorem hvb46_2_10 : dir46Mat 5 2 10 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (5 : Fin 46).val < 22)]
  exact hvb_2_10

/-- Vanishing at `(2, 10)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_2_10 (i : Fin 46) (ha : i ≠ 4) (hb : i ≠ 5) :
    dir46Mat i 2 10 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_2_10 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(3, 11)`. -/
theorem hva46_3_11 : dir46Mat 6 3 11 = 1 := by
  rw [dir46Mat_of_lt (by decide : (6 : Fin 46).val < 22)]
  exact hva_3_11

/-- Pivot value (imaginary part) at `(3, 11)`. -/
theorem hvb46_3_11 : dir46Mat 7 3 11 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (7 : Fin 46).val < 22)]
  exact hvb_3_11

/-- Vanishing at `(3, 11)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_3_11 (i : Fin 46) (ha : i ≠ 6) (hb : i ≠ 7) :
    dir46Mat i 3 11 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_3_11 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(24, 8)`. -/
theorem hva46_24_8 : dir46Mat 8 24 8 = 1 := by
  rw [dir46Mat_of_lt (by decide : (8 : Fin 46).val < 22)]
  exact hva_24_8

/-- Pivot value (imaginary part) at `(24, 8)`. -/
theorem hvb46_24_8 : dir46Mat 9 24 8 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (9 : Fin 46).val < 22)]
  exact hvb_24_8

/-- Vanishing at `(24, 8)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_24_8 (i : Fin 46) (ha : i ≠ 8) (hb : i ≠ 9) :
    dir46Mat i 24 8 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_24_8 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(0, 9)`. -/
theorem hva46_09 : dir46Mat 10 0 9 = 1 := by
  rw [dir46Mat_of_lt (by decide : (10 : Fin 46).val < 22)]
  exact hva_09

/-- Pivot value (imaginary part) at `(0, 9)`. -/
theorem hvb46_09 : dir46Mat 11 0 9 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (11 : Fin 46).val < 22)]
  exact hvb_09

/-- Vanishing at `(0, 9)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_09 (i : Fin 46) (ha : i ≠ 10) (hb : i ≠ 11) :
    dir46Mat i 0 9 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_09 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(1, 8)`. -/
theorem hva46_18 : dir46Mat 12 1 8 = 1 := by
  rw [dir46Mat_of_lt (by decide : (12 : Fin 46).val < 22)]
  exact hva_18

/-- Pivot value (imaginary part) at `(1, 8)`. -/
theorem hvb46_18 : dir46Mat 13 1 8 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (13 : Fin 46).val < 22)]
  exact hvb_18

/-- Vanishing at `(1, 8)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_18 (i : Fin 46) (ha : i ≠ 12) (hb : i ≠ 13) :
    dir46Mat i 1 8 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_18 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(2, 11)`. -/
theorem hva46_2_11 : dir46Mat 14 2 11 = 1 := by
  rw [dir46Mat_of_lt (by decide : (14 : Fin 46).val < 22)]
  exact hva_2_11

/-- Pivot value (imaginary part) at `(2, 11)`. -/
theorem hvb46_2_11 : dir46Mat 15 2 11 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (15 : Fin 46).val < 22)]
  exact hvb_2_11

/-- Vanishing at `(2, 11)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_2_11 (i : Fin 46) (ha : i ≠ 14) (hb : i ≠ 15) :
    dir46Mat i 2 11 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_2_11 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(3, 10)`. -/
theorem hva46_3_10 : dir46Mat 16 3 10 = 1 := by
  rw [dir46Mat_of_lt (by decide : (16 : Fin 46).val < 22)]
  exact hva_3_10

/-- Pivot value (imaginary part) at `(3, 10)`. -/
theorem hvb46_3_10 : dir46Mat 17 3 10 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (17 : Fin 46).val < 22)]
  exact hvb_3_10

/-- Vanishing at `(3, 10)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_3_10 (i : Fin 46) (ha : i ≠ 16) (hb : i ≠ 17) :
    dir46Mat i 3 10 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_3_10 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(8, 25)`. -/
theorem hva46_8_25 : dir46Mat 18 8 25 = 1 := by
  rw [dir46Mat_of_lt (by decide : (18 : Fin 46).val < 22)]
  exact hva_8_25

/-- Pivot value (imaginary part) at `(8, 25)`. -/
theorem hvb46_8_25 : dir46Mat 19 8 25 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (19 : Fin 46).val < 22)]
  exact hvb_8_25

/-- Vanishing at `(8, 25)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_8_25 (i : Fin 46) (ha : i ≠ 18) (hb : i ≠ 19) :
    dir46Mat i 8 25 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_8_25 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-- Pivot value (real part) at `(9, 25)`. -/
theorem hva46_9_25 : dir46Mat 20 9 25 = 1 := by
  rw [dir46Mat_of_lt (by decide : (20 : Fin 46).val < 22)]
  exact hva_9_25

/-- Pivot value (imaginary part) at `(9, 25)`. -/
theorem hvb46_9_25 : dir46Mat 21 9 25 = Complex.I := by
  rw [dir46Mat_of_lt (by decide : (21 : Fin 46).val < 22)]
  exact hvb_9_25

/-- Vanishing at `(9, 25)` off the pivot pair: landed directions
    by the `CFKernel22` vanishing lemma, new directions by
    `newMajAux_eq_zero_of_vals`. -/
theorem hvan46_9_25 (i : Fin 46) (ha : i ≠ 20) (hb : i ≠ 21) :
    dir46Mat i 9 25 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact hvan_9_25 ⟨i.val, hi⟩ (fin22_ne_of_fin46_ne hi ha (by decide))
      (fin22_ne_of_fin46_ne hi hb (by decide))
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    exact newMajAux_eq_zero_of_vals _ (by decide)

/-! ### The twelve new Majorana pivots -/

/-- Pivot value (real part) at `(24, 10)`: the pivot entry of
    `newMajAux 0`. -/
theorem hva46_24_10 : dir46Mat 22 24 10 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (22 : Fin 46).val)]
  exact newMajAux_pivot 0

/-- Pivot value (imaginary part) at `(24, 10)`: the pivot entry of
    `newMajAux 1`. -/
theorem hvb46_24_10 : dir46Mat 23 24 10 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (23 : Fin 46).val)]
  exact newMajAux_pivot 1

/-- Vanishing at `(24, 10)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_24_10 (i : Fin 46) (ha : i ≠ 22) (hb : i ≠ 23) :
    dir46Mat i 24 10 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 0 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 1 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (24 : I32) = newMajU 0 := by decide
    have hac : acoord (10 : I32) = newMajV 0 := by decide
    have hU0 := newMajU_spec 0
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 0, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 0, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(24, 11)`: the pivot entry of
    `newMajAux 2`. -/
theorem hva46_24_11 : dir46Mat 24 24 11 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (24 : Fin 46).val)]
  exact newMajAux_pivot 2

/-- Pivot value (imaginary part) at `(24, 11)`: the pivot entry of
    `newMajAux 3`. -/
theorem hvb46_24_11 : dir46Mat 25 24 11 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (25 : Fin 46).val)]
  exact newMajAux_pivot 3

/-- Vanishing at `(24, 11)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_24_11 (i : Fin 46) (ha : i ≠ 24) (hb : i ≠ 25) :
    dir46Mat i 24 11 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 2 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 3 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (24 : I32) = newMajU 2 := by decide
    have hac : acoord (11 : I32) = newMajV 2 := by decide
    have hU0 := newMajU_spec 2
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 2, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 2, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(24, 12)`: the pivot entry of
    `newMajAux 4`. -/
theorem hva46_24_12 : dir46Mat 26 24 12 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (26 : Fin 46).val)]
  exact newMajAux_pivot 4

/-- Pivot value (imaginary part) at `(24, 12)`: the pivot entry of
    `newMajAux 5`. -/
theorem hvb46_24_12 : dir46Mat 27 24 12 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (27 : Fin 46).val)]
  exact newMajAux_pivot 5

/-- Vanishing at `(24, 12)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_24_12 (i : Fin 46) (ha : i ≠ 26) (hb : i ≠ 27) :
    dir46Mat i 24 12 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 4 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 5 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (24 : I32) = newMajU 4 := by decide
    have hac : acoord (12 : I32) = newMajV 4 := by decide
    have hU0 := newMajU_spec 4
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 4, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 4, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(24, 13)`: the pivot entry of
    `newMajAux 6`. -/
theorem hva46_24_13 : dir46Mat 28 24 13 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (28 : Fin 46).val)]
  exact newMajAux_pivot 6

/-- Pivot value (imaginary part) at `(24, 13)`: the pivot entry of
    `newMajAux 7`. -/
theorem hvb46_24_13 : dir46Mat 29 24 13 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (29 : Fin 46).val)]
  exact newMajAux_pivot 7

/-- Vanishing at `(24, 13)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_24_13 (i : Fin 46) (ha : i ≠ 28) (hb : i ≠ 29) :
    dir46Mat i 24 13 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 6 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 7 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (24 : I32) = newMajU 6 := by decide
    have hac : acoord (13 : I32) = newMajV 6 := by decide
    have hU0 := newMajU_spec 6
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 6, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 6, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(24, 14)`: the pivot entry of
    `newMajAux 8`. -/
theorem hva46_24_14 : dir46Mat 30 24 14 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (30 : Fin 46).val)]
  exact newMajAux_pivot 8

/-- Pivot value (imaginary part) at `(24, 14)`: the pivot entry of
    `newMajAux 9`. -/
theorem hvb46_24_14 : dir46Mat 31 24 14 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (31 : Fin 46).val)]
  exact newMajAux_pivot 9

/-- Vanishing at `(24, 14)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_24_14 (i : Fin 46) (ha : i ≠ 30) (hb : i ≠ 31) :
    dir46Mat i 24 14 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 8 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 9 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (24 : I32) = newMajU 8 := by decide
    have hac : acoord (14 : I32) = newMajV 8 := by decide
    have hU0 := newMajU_spec 8
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 8, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 8, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(24, 15)`: the pivot entry of
    `newMajAux 10`. -/
theorem hva46_24_15 : dir46Mat 32 24 15 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (32 : Fin 46).val)]
  exact newMajAux_pivot 10

/-- Pivot value (imaginary part) at `(24, 15)`: the pivot entry of
    `newMajAux 11`. -/
theorem hvb46_24_15 : dir46Mat 33 24 15 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (33 : Fin 46).val)]
  exact newMajAux_pivot 11

/-- Vanishing at `(24, 15)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_24_15 (i : Fin 46) (ha : i ≠ 32) (hb : i ≠ 33) :
    dir46Mat i 24 15 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 10 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 11 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (24 : I32) = newMajU 10 := by decide
    have hac : acoord (15 : I32) = newMajV 10 := by decide
    have hU0 := newMajU_spec 10
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 10, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 10, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(25, 10)`: the pivot entry of
    `newMajAux 12`. -/
theorem hva46_25_10 : dir46Mat 34 25 10 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (34 : Fin 46).val)]
  exact newMajAux_pivot 12

/-- Pivot value (imaginary part) at `(25, 10)`: the pivot entry of
    `newMajAux 13`. -/
theorem hvb46_25_10 : dir46Mat 35 25 10 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (35 : Fin 46).val)]
  exact newMajAux_pivot 13

/-- Vanishing at `(25, 10)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_25_10 (i : Fin 46) (ha : i ≠ 34) (hb : i ≠ 35) :
    dir46Mat i 25 10 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 12 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 13 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (25 : I32) = newMajU 12 := by decide
    have hac : acoord (10 : I32) = newMajV 12 := by decide
    have hU0 := newMajU_spec 12
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 12, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 12, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(25, 11)`: the pivot entry of
    `newMajAux 14`. -/
theorem hva46_25_11 : dir46Mat 36 25 11 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (36 : Fin 46).val)]
  exact newMajAux_pivot 14

/-- Pivot value (imaginary part) at `(25, 11)`: the pivot entry of
    `newMajAux 15`. -/
theorem hvb46_25_11 : dir46Mat 37 25 11 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (37 : Fin 46).val)]
  exact newMajAux_pivot 15

/-- Vanishing at `(25, 11)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_25_11 (i : Fin 46) (ha : i ≠ 36) (hb : i ≠ 37) :
    dir46Mat i 25 11 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 14 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 15 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (25 : I32) = newMajU 14 := by decide
    have hac : acoord (11 : I32) = newMajV 14 := by decide
    have hU0 := newMajU_spec 14
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 14, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 14, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(25, 12)`: the pivot entry of
    `newMajAux 16`. -/
theorem hva46_25_12 : dir46Mat 38 25 12 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (38 : Fin 46).val)]
  exact newMajAux_pivot 16

/-- Pivot value (imaginary part) at `(25, 12)`: the pivot entry of
    `newMajAux 17`. -/
theorem hvb46_25_12 : dir46Mat 39 25 12 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (39 : Fin 46).val)]
  exact newMajAux_pivot 17

/-- Vanishing at `(25, 12)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_25_12 (i : Fin 46) (ha : i ≠ 38) (hb : i ≠ 39) :
    dir46Mat i 25 12 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 16 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 17 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (25 : I32) = newMajU 16 := by decide
    have hac : acoord (12 : I32) = newMajV 16 := by decide
    have hU0 := newMajU_spec 16
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 16, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 16, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(25, 13)`: the pivot entry of
    `newMajAux 18`. -/
theorem hva46_25_13 : dir46Mat 40 25 13 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (40 : Fin 46).val)]
  exact newMajAux_pivot 18

/-- Pivot value (imaginary part) at `(25, 13)`: the pivot entry of
    `newMajAux 19`. -/
theorem hvb46_25_13 : dir46Mat 41 25 13 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (41 : Fin 46).val)]
  exact newMajAux_pivot 19

/-- Vanishing at `(25, 13)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_25_13 (i : Fin 46) (ha : i ≠ 40) (hb : i ≠ 41) :
    dir46Mat i 25 13 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 18 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 19 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (25 : I32) = newMajU 18 := by decide
    have hac : acoord (13 : I32) = newMajV 18 := by decide
    have hU0 := newMajU_spec 18
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 18, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 18, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(25, 14)`: the pivot entry of
    `newMajAux 20`. -/
theorem hva46_25_14 : dir46Mat 42 25 14 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (42 : Fin 46).val)]
  exact newMajAux_pivot 20

/-- Pivot value (imaginary part) at `(25, 14)`: the pivot entry of
    `newMajAux 21`. -/
theorem hvb46_25_14 : dir46Mat 43 25 14 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (43 : Fin 46).val)]
  exact newMajAux_pivot 21

/-- Vanishing at `(25, 14)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_25_14 (i : Fin 46) (ha : i ≠ 42) (hb : i ≠ 43) :
    dir46Mat i 25 14 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 20 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 21 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (25 : I32) = newMajU 20 := by decide
    have hac : acoord (14 : I32) = newMajV 20 := by decide
    have hU0 := newMajU_spec 20
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 20, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 20, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- Pivot value (real part) at `(25, 15)`: the pivot entry of
    `newMajAux 22`. -/
theorem hva46_25_15 : dir46Mat 44 25 15 = 1 := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (44 : Fin 46).val)]
  exact newMajAux_pivot 22

/-- Pivot value (imaginary part) at `(25, 15)`: the pivot entry of
    `newMajAux 23`. -/
theorem hvb46_25_15 : dir46Mat 45 25 15 = Complex.I := by
  rw [dir46Mat_of_ge (by decide : 22 ≤ (45 : Fin 46).val)]
  exact newMajAux_pivot 23

/-- Vanishing at `(25, 15)` off the pivot pair: landed directions
    by `dirs22_eq_zero_of_newpivot`; other new directions because a
    nonzero entry there would force the same folded coordinate. -/
theorem hvan46_25_15 (i : Fin 46) (ha : i ≠ 44) (hb : i ≠ 45) :
    dir46Mat i 25 15 = 0 := by
  by_cases hi : i.val < 22
  · rw [dir46Mat_of_lt hi]
    exact dirs22_eq_zero_of_newpivot (by decide) (by decide) ⟨i.val, hi⟩
  · rw [dir46Mat_of_ge (by omega : 22 ≤ i.val)]
    by_contra hne
    have hna : i.val - 22 ≠ 22 := by
      intro hh
      exact ha (Fin.ext (by omega))
    have hnb : i.val - 22 ≠ 23 := by
      intro hh
      exact hb (Fin.ext (by omega))
    have hcoord := newMajAux_ne_zero_coord (i.val - 22) hne
    have har : acoord (25 : I32) = newMajU 22 := by decide
    have hac : acoord (15 : I32) = newMajV 22 := by decide
    have hU0 := newMajU_spec 22
    have hVn := newMajV_spec (i.val - 22)
    rcases hcoord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1
      rw [har, newMajU_val 22, newMajU_val (i.val - 22)] at e1
      have e2 := congrArg Fin.val h2
      rw [hac, newMajV_val 22, newMajV_val (i.val - 22)] at e2
      split_ifs at e1 <;> omega
    · have e1 := congrArg Fin.val h1
      rw [har] at e1
      have e2 := congrArg Fin.val h2
      rw [hac] at e2
      omega

/-- **The 46 directions are linearly independent over ℝ** (as
    matrices): every pivot pair of §4 kills its two coefficients in
    any vanishing real-linear combination. -/
theorem dir46Mat_independent : LinearIndependent ℝ dir46Mat := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · exact (pivot_extract46 0 8 0 1 (by decide) hva46_08 hvb46_08 hvan46_08 g hg).1
  · exact (pivot_extract46 0 8 0 1 (by decide) hva46_08 hvb46_08 hvan46_08 g hg).2
  · exact (pivot_extract46 1 9 2 3 (by decide) hva46_19 hvb46_19 hvan46_19 g hg).1
  · exact (pivot_extract46 1 9 2 3 (by decide) hva46_19 hvb46_19 hvan46_19 g hg).2
  · exact (pivot_extract46 2 10 4 5 (by decide) hva46_2_10 hvb46_2_10 hvan46_2_10 g hg).1
  · exact (pivot_extract46 2 10 4 5 (by decide) hva46_2_10 hvb46_2_10 hvan46_2_10 g hg).2
  · exact (pivot_extract46 3 11 6 7 (by decide) hva46_3_11 hvb46_3_11 hvan46_3_11 g hg).1
  · exact (pivot_extract46 3 11 6 7 (by decide) hva46_3_11 hvb46_3_11 hvan46_3_11 g hg).2
  · exact (pivot_extract46 24 8 8 9 (by decide) hva46_24_8 hvb46_24_8 hvan46_24_8 g hg).1
  · exact (pivot_extract46 24 8 8 9 (by decide) hva46_24_8 hvb46_24_8 hvan46_24_8 g hg).2
  · exact (pivot_extract46 0 9 10 11 (by decide) hva46_09 hvb46_09 hvan46_09 g hg).1
  · exact (pivot_extract46 0 9 10 11 (by decide) hva46_09 hvb46_09 hvan46_09 g hg).2
  · exact (pivot_extract46 1 8 12 13 (by decide) hva46_18 hvb46_18 hvan46_18 g hg).1
  · exact (pivot_extract46 1 8 12 13 (by decide) hva46_18 hvb46_18 hvan46_18 g hg).2
  · exact (pivot_extract46 2 11 14 15 (by decide) hva46_2_11 hvb46_2_11 hvan46_2_11 g hg).1
  · exact (pivot_extract46 2 11 14 15 (by decide) hva46_2_11 hvb46_2_11 hvan46_2_11 g hg).2
  · exact (pivot_extract46 3 10 16 17 (by decide) hva46_3_10 hvb46_3_10 hvan46_3_10 g hg).1
  · exact (pivot_extract46 3 10 16 17 (by decide) hva46_3_10 hvb46_3_10 hvan46_3_10 g hg).2
  · exact (pivot_extract46 8 25 18 19 (by decide) hva46_8_25 hvb46_8_25 hvan46_8_25 g hg).1
  · exact (pivot_extract46 8 25 18 19 (by decide) hva46_8_25 hvb46_8_25 hvan46_8_25 g hg).2
  · exact (pivot_extract46 9 25 20 21 (by decide) hva46_9_25 hvb46_9_25 hvan46_9_25 g hg).1
  · exact (pivot_extract46 9 25 20 21 (by decide) hva46_9_25 hvb46_9_25 hvan46_9_25 g hg).2
  · exact (pivot_extract46 24 10 22 23 (by decide) hva46_24_10 hvb46_24_10 hvan46_24_10 g hg).1
  · exact (pivot_extract46 24 10 22 23 (by decide) hva46_24_10 hvb46_24_10 hvan46_24_10 g hg).2
  · exact (pivot_extract46 24 11 24 25 (by decide) hva46_24_11 hvb46_24_11 hvan46_24_11 g hg).1
  · exact (pivot_extract46 24 11 24 25 (by decide) hva46_24_11 hvb46_24_11 hvan46_24_11 g hg).2
  · exact (pivot_extract46 24 12 26 27 (by decide) hva46_24_12 hvb46_24_12 hvan46_24_12 g hg).1
  · exact (pivot_extract46 24 12 26 27 (by decide) hva46_24_12 hvb46_24_12 hvan46_24_12 g hg).2
  · exact (pivot_extract46 24 13 28 29 (by decide) hva46_24_13 hvb46_24_13 hvan46_24_13 g hg).1
  · exact (pivot_extract46 24 13 28 29 (by decide) hva46_24_13 hvb46_24_13 hvan46_24_13 g hg).2
  · exact (pivot_extract46 24 14 30 31 (by decide) hva46_24_14 hvb46_24_14 hvan46_24_14 g hg).1
  · exact (pivot_extract46 24 14 30 31 (by decide) hva46_24_14 hvb46_24_14 hvan46_24_14 g hg).2
  · exact (pivot_extract46 24 15 32 33 (by decide) hva46_24_15 hvb46_24_15 hvan46_24_15 g hg).1
  · exact (pivot_extract46 24 15 32 33 (by decide) hva46_24_15 hvb46_24_15 hvan46_24_15 g hg).2
  · exact (pivot_extract46 25 10 34 35 (by decide) hva46_25_10 hvb46_25_10 hvan46_25_10 g hg).1
  · exact (pivot_extract46 25 10 34 35 (by decide) hva46_25_10 hvb46_25_10 hvan46_25_10 g hg).2
  · exact (pivot_extract46 25 11 36 37 (by decide) hva46_25_11 hvb46_25_11 hvan46_25_11 g hg).1
  · exact (pivot_extract46 25 11 36 37 (by decide) hva46_25_11 hvb46_25_11 hvan46_25_11 g hg).2
  · exact (pivot_extract46 25 12 38 39 (by decide) hva46_25_12 hvb46_25_12 hvan46_25_12 g hg).1
  · exact (pivot_extract46 25 12 38 39 (by decide) hva46_25_12 hvb46_25_12 hvan46_25_12 g hg).2
  · exact (pivot_extract46 25 13 40 41 (by decide) hva46_25_13 hvb46_25_13 hvan46_25_13 g hg).1
  · exact (pivot_extract46 25 13 40 41 (by decide) hva46_25_13 hvb46_25_13 hvan46_25_13 g hg).2
  · exact (pivot_extract46 25 14 42 43 (by decide) hva46_25_14 hvb46_25_14 hvan46_25_14 g hg).1
  · exact (pivot_extract46 25 14 42 43 (by decide) hva46_25_14 hvb46_25_14 hvan46_25_14 g hg).2
  · exact (pivot_extract46 25 15 44 45 (by decide) hva46_25_15 hvb46_25_15 hvan46_25_15 g hg).1
  · exact (pivot_extract46 25 15 44 45 (by decide) hva46_25_15 hvb46_25_15 hvan46_25_15 g hg).2

/-- **C96-2a headline: the 46 census directions are linearly
    independent over ℝ in `Sol32`.** Together with `dir46Mat_mem`
    (each direction lies in `{D ∈ 𝒜₁ | OrderOneHolds D}`), this is
    the membership + independence half of the one-generation census
    count. The matching upper bound (`finrank = 46`) is C96-2b, not
    stated here. -/
theorem dir46_independent : LinearIndependent ℝ dir46 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg2 : ∑ j, g j • dir46Mat j = 0 := by
    have h := congrArg (Sol32.subtype) hg
    simp only [map_sum, map_smul, map_zero, Submodule.subtype_apply,
      dir46_coe] at h
    exact h
  exact Fintype.linearIndependent_iff.mp dir46Mat_independent g hg2 i

end ThetLogos
