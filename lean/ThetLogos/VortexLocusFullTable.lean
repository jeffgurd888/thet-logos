import ThetLogos.VortexLocusPin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Vortex-locus full table (VL-4a): the γ-split multiplicity table of D_F(y₀)²

Governing texts: the VL scoping memo §(i)/§VL-4
(`routeb-general-scratch/scoping-vortex-locus-2026-10-30.md`) and the
Step-0 probe registered as BR1-027 (`routeb-general-scratch/vl4-probe.py`,
run record `routeb-general-scratch/vl4-probe-out.txt`).  BRIDGE-1
discipline: the probe's values are the registered TARGET — everything
below is proved from the landed block structure of `smDirac`; the probe
is never cited as a hypothesis.  NO CLAIM on this module's face; the
K-VORTEX fences of the memo §5 are inherited: nothing below asserts
that a Yukawa block "is" a circulation flux, and "vortex" is Jeff's T5
vocabulary carried by the inherited module names only.

**Seat (T2 chosen inputs, stated on the face).**  Seat B:
`y₀ = (yNu, yE, yU, yD, yR) = (1, 2, 3, 5, 7)` and
`K0 = (smDirac 1 2 3 5 7)^2` — the landed name/form from
`VortexLocusPin.lean`, cited, never redefined.  The grading is
`gammaF = diag(+I₈, −I₈, −I₈, +I₈)` (`Scaffold32.lean`): its `+1`
coordinate sector is the flat index set `{0..7} ∪ {24..31}` (blocks 0
and 3 in the `blkIdx` decomposition) and its `−1` sector is `{8..23}`
(blocks 1 and 2).  `gammaPlusSub` / `gammaMinusSub` below are exactly
those two coordinate submodules: the spans of the standard basis
vectors at the + / − indices.

**Registered table (BR1-027), landed in full — the pre-registered
PARTIAL seam did not trigger.**  With `M := K0`:
- annihilating polynomial `(M − 4)(M − 9)(M − 25)(M² − 51M + 1) = 0`
  as matrices, each factor individually nonzero;
- total eigenspace finranks: `μ = 4 → 4`, `μ = 9 → 12`, `μ = 25 → 12`,
  and the quadratic factor's joint kernel `ker (M² − 51M + 1) → 4`;
- γ-splits (finranks of the intersections with the two sector
  submodules): `μ = 4 → (2, 2)`, `μ = 9 → (6, 6)`, `μ = 25 → (6, 6)`,
  joint quadratic `→ (2, 2)`.

The irrational roots of `μ² − 51μ + 1` are never named as numbers: the
quadratic factor itself is the statement, and its split is carried at
the registered joint level (2, 2); no per-root split is asserted.

**Proof route.**  In the `blkIdx` decomposition `K0` is diagonal
(`dval`) except for the Majorana coupling `cval i = 7` on the
`aOf i = 0` seats, which pairs each index `i` with its block partner
`pIdx i` (blocks 0 ↔ 3, 1 ↔ 2) in a 2×2 block annihilated by
`μ² − 51μ + 1` (on coupled seats: `dval i + dval (pIdx i) = 51`,
`dval i * dval (pIdx i) = 50`, `cval i ^ 2 = 49`).  Eigenspaces are
identified with coordinate ranges by the 2×2 determinant
`μ² − 51μ + 1 ≠ 0` at `μ ∈ {4, 9, 25}` (`eig_eq_range_of`), and the
finranks are read off the parametrizations.  No `sorry`, no
`native_decide`; no scoped heartbeat raises were used.
-/

namespace ThetLogos

open Matrix

/-- Block index of `i : I32` (the `Fin 4` component). -/
def bOf (i : I32) : Fin 4 := ⟨i.val / 8, by have h := i.isLt; omega⟩

/-- Within-block index of `i : I32` (the `Fin 8` component). -/
def aOf (i : I32) : Fin 8 := ⟨i.val % 8, by have h := i.isLt; omega⟩

theorem blkIdx_bOf (b : Fin 4) (a : Fin 8) : bOf (blkIdx b a) = b := by
  apply Fin.ext
  show (a.val + b.val * 8) / 8 = b.val
  have ha := a.isLt; have hb := b.isLt; omega

theorem blkIdx_aOf (b : Fin 4) (a : Fin 8) : aOf (blkIdx b a) = a := by
  apply Fin.ext
  show (a.val + b.val * 8) % 8 = a.val
  have ha := a.isLt; have hb := b.isLt; omega

theorem eq_blkIdx (i : I32) : blkIdx (bOf i) (aOf i) = i := by
  apply Fin.ext
  show i.val % 8 + (i.val / 8) * 8 = i.val
  have h := Nat.div_add_mod i.val 8
  omega

theorem blkIdx_inj {b b' : Fin 4} {a a' : Fin 8}
    (h : blkIdx b a = blkIdx b' a') : b = b' ∧ a = a' := by
  constructor
  · have h1 := congrArg bOf h
    rwa [blkIdx_bOf, blkIdx_bOf] at h1
  · have h2 := congrArg aOf h
    rwa [blkIdx_aOf, blkIdx_aOf] at h2

/-- The block-partner involution on `Fin 4`: `0 ↔ 3`, `1 ↔ 2`. -/
def pb : Fin 4 → Fin 4 := ![3, 2, 1, 0]

theorem pb_involutive (b : Fin 4) : pb (pb b) = b := by
  fin_cases b <;> rfl

theorem pb_ne_self (b : Fin 4) : pb b ≠ b := by
  fin_cases b <;> decide

/-- The squared-Yukawa diagonal on blocks `0, 2`. -/
def wvec : Fin 8 → ℂ := ![1, 4, 9, 25, 9, 25, 9, 25]

/-- The squared-Yukawa diagonal on blocks `1, 3` (Majorana `49` added at `a = 0`). -/
def wvec' : Fin 8 → ℂ := ![50, 4, 9, 25, 9, 25, 9, 25]

/-- Diagonal value of `K0` at index `i`. -/
def dval (i : I32) : ℂ := if bOf i = 1 ∨ bOf i = 3 then wvec' (aOf i) else wvec (aOf i)

/-- Coupling value of `K0` at index `i`: `7` on the Majorana path seats, else `0`. -/
def cval (i : I32) : ℂ := if aOf i = 0 then 7 else 0

/-- Coupling partner of `i`: same within-block index, partner block. -/
def pIdx (i : I32) : I32 := blkIdx (pb (bOf i)) (aOf i)

theorem dval_blk (b : Fin 4) (a : Fin 8) :
    dval (blkIdx b a) = if b = 1 ∨ b = 3 then wvec' a else wvec a := by
  rw [dval, blkIdx_bOf, blkIdx_aOf]

theorem cval_blk (b : Fin 4) (a : Fin 8) :
    cval (blkIdx b a) = if a = 0 then 7 else 0 := by
  rw [cval, blkIdx_aOf]

theorem pIdx_blk (b : Fin 4) (a : Fin 8) :
    pIdx (blkIdx b a) = blkIdx (pb b) a := by
  rw [pIdx, blkIdx_bOf, blkIdx_aOf]

theorem pIdx_involutive (i : I32) : pIdx (pIdx i) = i := by
  conv_lhs => rw [← eq_blkIdx i]
  rw [pIdx_blk, pIdx_blk, pb_involutive, eq_blkIdx]

theorem aOf_pIdx (i : I32) : aOf (pIdx i) = aOf i := by
  conv_lhs => rw [← eq_blkIdx i]
  rw [pIdx_blk, blkIdx_aOf]

theorem cval_pIdx (i : I32) : cval (pIdx i) = cval i := by
  unfold cval
  rw [aOf_pIdx]

theorem bOf_pIdx (i : I32) : bOf (pIdx i) = pb (bOf i) := by
  conv_lhs => rw [← eq_blkIdx i]
  rw [pIdx_blk, blkIdx_bOf]

theorem pIdx_ne_self (i : I32) : pIdx i ≠ i := by
  intro h
  have h2 := congrArg bOf h
  rw [bOf_pIdx] at h2
  exact pb_ne_self _ h2

/-- The seat identities. -/
theorem seat_identities (i : I32) :
    (cval i ≠ 0 → dval i + dval (pIdx i) = 51)
    ∧ (cval i ≠ 0 → dval i * dval (pIdx i) = 50)
    ∧ (cval i ≠ 0 → cval i ^ 2 = 49)
    ∧ (cval i ≠ 0 → dval i ^ 2 + cval i ^ 2 - 51 * dval i + 1 = 0)
    ∧ (cval i = 0 → dval i = 4 ∨ dval i = 9 ∨ dval i = 25)
    ∧ (cval i = 0 → dval i ^ 2 - 51 * dval i + 1 ≠ 0) := by
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  fin_cases b <;> fin_cases a <;>
    simp only [dval_blk, cval_blk, pIdx_blk] <;>
    norm_num [wvec, wvec', pb]

theorem dval_blk0 (a : Fin 8) : dval (blkIdx 0 a) = wvec a := by
  rw [dval_blk]; exact ite_eq_right (by decide)

theorem dval_blk1 (a : Fin 8) : dval (blkIdx 1 a) = wvec' a := by
  rw [dval_blk]; exact ite_eq_left (Or.inl rfl)

theorem dval_blk2 (a : Fin 8) : dval (blkIdx 2 a) = wvec a := by
  rw [dval_blk]; exact ite_eq_right (by decide)

theorem dval_blk3 (a : Fin 8) : dval (blkIdx 3 a) = wvec' a := by
  rw [dval_blk]; exact ite_eq_left (Or.inr rfl)


theorem cvec_apply (a : Fin 8) :
    (![7, 0, 0, 0, 0, 0, 0, 0] : Fin 8 → ℂ) a = if a = 0 then 7 else 0 := by
  fin_cases a <;> norm_num

/-! K0 block entries -/

private theorem K0_eq : K0 = (buildDirac (yukawaBlock 1 2 3 5)
    ((yukawaBlock 1 2 3 5).map (starRingEnd ℂ)) 0 (majoranaBlock 7)) ^ 2 := rfl

theorem wvec_eq : wvec = ![1, 4, 9, 25, 9, 25, 9, 25] := rfl

theorem wvec'_eq : wvec' = ![50, 4, 9, 25, 9, 25, 9, 25] := rfl

theorem K0_diag_block0 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 0 a₁) (blkIdx 0 a₂) = if a₁ = a₂ then dval (blkIdx 0 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_00, seatAA, Matrix.diagonal_apply, dval_blk0, wvec_eq]

theorem K0_diag_block1 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 1 a₁) (blkIdx 1 a₂) = if a₁ = a₂ then dval (blkIdx 1 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_11, seat11, Matrix.diagonal_apply, dval_blk1, wvec'_eq]

theorem K0_diag_block2 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 2 a₁) (blkIdx 2 a₂) = if a₁ = a₂ then dval (blkIdx 2 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_22, seatBB, Matrix.diagonal_apply, dval_blk2, wvec_eq]

theorem K0_diag_block3 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 3 a₁) (blkIdx 3 a₂) = if a₁ = a₂ then dval (blkIdx 3 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_33, seat33, Matrix.diagonal_apply, dval_blk3, wvec'_eq]

theorem fin4_cases (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  revert x; decide

theorem K0_diag_block (b : Fin 4) (a₁ a₂ : Fin 8) :
    K0 (blkIdx b a₁) (blkIdx b a₂) = if a₁ = a₂ then dval (blkIdx b a₁) else 0 := by
  rcases fin4_cases b with rfl | rfl | rfl | rfl
  · exact K0_diag_block0 a₁ a₂
  · exact K0_diag_block1 a₁ a₂
  · exact K0_diag_block2 a₁ a₂
  · exact K0_diag_block3 a₁ a₂

theorem K0_coup_block03 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 0 a₁) (blkIdx 3 a₂) = if a₁ = a₂ then cval (blkIdx 0 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_03, seatAE, Matrix.diagonal_apply, cval_blk, cvec_apply]

theorem K0_coup_block12 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 1 a₁) (blkIdx 2 a₂) = if a₁ = a₂ then cval (blkIdx 1 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_12, seatEB, Matrix.diagonal_apply, cval_blk, cvec_apply]

theorem K0_coup_block21 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 2 a₁) (blkIdx 1 a₂) = if a₁ = a₂ then cval (blkIdx 2 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_21, seatBE, Matrix.diagonal_apply, cval_blk, cvec_apply]

theorem K0_coup_block30 (a₁ a₂ : Fin 8) :
    K0 (blkIdx 3 a₁) (blkIdx 0 a₂) = if a₁ = a₂ then cval (blkIdx 3 a₁) else 0 := by
  rw [K0_eq, pow2_buildDirac_blk_30, seatEA, Matrix.diagonal_apply, cval_blk, cvec_apply]

theorem pb_zero : pb 0 = 3 := rfl
theorem pb_one : pb 1 = 2 := rfl
theorem pb_two : pb 2 = 1 := rfl
theorem pb_three : pb 3 = 0 := rfl

theorem K0_coup_block (b : Fin 4) (a₁ a₂ : Fin 8) :
    K0 (blkIdx b a₁) (blkIdx (pb b) a₂) = if a₁ = a₂ then cval (blkIdx b a₁) else 0 := by
  rcases fin4_cases b with rfl | rfl | rfl | rfl
  · rw [pb_zero]; exact K0_coup_block03 a₁ a₂
  · rw [pb_one]; exact K0_coup_block12 a₁ a₂
  · rw [pb_two]; exact K0_coup_block21 a₁ a₂
  · rw [pb_three]; exact K0_coup_block30 a₁ a₂

theorem K0_zero_block {b b' : Fin 4} (hb : b' ≠ b) (hb2 : b' ≠ pb b) (a₁ a₂ : Fin 8) :
    K0 (blkIdx b a₁) (blkIdx b' a₂) = 0 := by
  rcases fin4_cases b with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases b' with rfl | rfl | rfl | rfl <;>
    simp only [pb_zero, pb_one, pb_two, pb_three] at hb2 <;>
    first
      | (exfalso; exact hb rfl)
      | (exfalso; exact hb2 rfl)
      | rw [K0_eq, pow2_buildDirac_blk_01_zero]
      | rw [K0_eq, pow2_buildDirac_blk_02_zero]
      | rw [K0_eq, pow2_buildDirac_blk_10_zero]
      | rw [K0_eq, pow2_buildDirac_blk_13_zero]
      | rw [K0_eq, pow2_buildDirac_blk_20_zero]
      | rw [K0_eq, pow2_buildDirac_blk_23_zero]
      | rw [K0_eq, pow2_buildDirac_blk_31_zero]
      | rw [K0_eq, pow2_buildDirac_blk_32_zero]

/-- The entry formula for `K0`. -/
theorem K0_apply (i k : I32) :
    K0 i k = if k = i then dval i else if k = pIdx i then cval i else 0 := by
  conv_lhs => rw [← eq_blkIdx i, ← eq_blkIdx k]
  by_cases h1 : bOf k = bOf i
  · rw [h1, K0_diag_block]
    by_cases h2 : aOf k = aOf i
    · have hki : k = i := by rw [← eq_blkIdx k, h1, h2, eq_blkIdx]
      rw [ite_eq_left h2.symm, ite_eq_left hki, eq_blkIdx]
    · have hki : k ≠ i := by
        intro hcon
        exact h2 (by rw [hcon])
      have hkp : k ≠ pIdx i := by
        intro hcon
        have h3 := congrArg bOf hcon
        rw [bOf_pIdx, h1] at h3
        exact pb_ne_self _ h3.symm
      rw [ite_eq_right (fun h => h2 h.symm), ite_eq_right hki, ite_eq_right hkp]
  · by_cases h2 : bOf k = pb (bOf i)
    · rw [h2, K0_coup_block]
      by_cases h3 : aOf k = aOf i
      · have hkp : k = pIdx i := by
          rw [← eq_blkIdx k, h2, h3, ← pIdx_blk, eq_blkIdx]
        have hki : k ≠ i := by
          intro hcon
          exact h1 (by rw [hcon])
        rw [ite_eq_left h3.symm, ite_eq_right hki, ite_eq_left hkp, eq_blkIdx]
      · have hki : k ≠ i := by
          intro hcon
          exact h1 (by rw [hcon])
        have hkp : k ≠ pIdx i := by
          intro hcon
          have e1 : aOf k = aOf (pIdx i) := congrArg aOf hcon
          rw [aOf_pIdx] at e1
          exact h3 e1
        rw [ite_eq_right (fun h => h3 h.symm), ite_eq_right hki, ite_eq_right hkp]
    · have hz : K0 (blkIdx (bOf i) (aOf i)) (blkIdx (bOf k) (aOf k)) = 0 :=
        K0_zero_block h1 h2 _ _
      rw [hz]
      have hki : k ≠ i := by
        intro hcon
        exact h1 (by rw [hcon])
      have hkp : k ≠ pIdx i := by
        intro hcon
        have h3 := congrArg bOf hcon
        rw [bOf_pIdx] at h3
        exact h2 h3
      rw [ite_eq_right hki, ite_eq_right hkp]

/-! ## mulVec formulas -/

theorem K0_mulVec_apply (v : I32 → ℂ) (i : I32) :
    (K0 *ᵥ v) i = dval i * v i + cval i * v (pIdx i) := by
  have hsum : (K0 *ᵥ v) i = ∑ k : I32, K0 i k * v k :=
    Matrix.mulVec_apply_eq_sum K0 v i
  rw [hsum]
  have hsub : (∑ k : I32, K0 i k * v k)
      = ∑ k ∈ ({i, pIdx i} : Finset I32), K0 i k * v k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    rw [K0_apply, ite_eq_right hk.2, ite_eq_right hk.1, zero_mul]
  rw [hsub, Finset.sum_pair (pIdx_ne_self i).symm]
  rw [K0_apply, K0_apply, ite_eq_left rfl, ite_eq_right (pIdx_ne_self i),
    ite_eq_left rfl]

theorem quad_mulVec_apply (v : I32 → ℂ) (i : I32) :
    ((K0 ^ 2 - 51 • K0 + 1) *ᵥ v) i
      = (dval i ^ 2 + cval i ^ 2 - 51 * dval i + 1) * v i
        + cval i * (dval i + dval (pIdx i) - 51) * v (pIdx i) := by
  have h1 : ((K0 ^ 2 - 51 • K0 + 1) *ᵥ v)
      = K0 *ᵥ (K0 *ᵥ v) - 51 • (K0 *ᵥ v) + v := by
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, pow_two, Matrix.mulVec_mulVec]
  rw [h1]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [K0_mulVec_apply, K0_mulVec_apply, K0_mulVec_apply, cval_pIdx,
    pIdx_involutive]
  ring

theorem factor_mulVec_apply (μ : ℂ) (v : I32 → ℂ) (i : I32) :
    ((K0 - μ • 1) *ᵥ v) i = (dval i - μ) * v i + cval i * v (pIdx i) := by
  have h1 : ((K0 - μ • 1) *ᵥ v) i = (K0 *ᵥ v) i - μ * v i := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, K0_mulVec_apply]
  ring

/-! ## Coordinate embeddings -/

/-- The coordinate embedding along `f : ι → I32`: `w ↦ ∑ j, w j • e_{f j}`. -/
def coordEmb {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → I32) :
    (ι → ℂ) →ₗ[ℂ] (I32 → ℂ) where
  toFun w i := ∑ j, if f j = i then w j else 0
  map_add' x y := by
    funext i
    show (∑ j, if f j = i then (x + y) j else 0)
        = (∑ j, if f j = i then x j else 0) + ∑ j, if f j = i then y j else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : f j = i <;> simp [h, Pi.add_apply]
  map_smul' c x := by
    funext i
    show (∑ j, if f j = i then (c • x) j else 0)
        = c • (∑ j, if f j = i then x j else 0)
    rw [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : f j = i <;> simp [h, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coordEmb_apply_at {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → I32}
    (hf : Function.Injective f) (w : ι → ℂ) (j : ι) :
    coordEmb f w (f j) = w j := by
  show (∑ j', if f j' = f j then w j' else 0) = w j
  have hcong : (∑ j', if f j' = f j then w j' else 0)
      = ∑ j', if j = j' then w j' else 0 := by
    apply Finset.sum_congr rfl
    intro j' _
    by_cases h : j' = j
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right (fun hh : j = j' => h hh.symm),
        ite_eq_right (fun h' => h (hf h'))]
  rw [hcong, Finset.sum_ite_eq]
  exact ite_eq_left (Finset.mem_univ j)

theorem coordEmb_apply_of_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → I32}
    (w : ι → ℂ) {i : I32} (hi : i ∉ Set.range f) :
    coordEmb f w i = 0 := by
  show (∑ j, if f j = i then w j else 0) = 0
  apply Finset.sum_eq_zero
  intro j _
  rw [ite_eq_right (fun h => hi ⟨j, h⟩)]

theorem coordEmb_injective {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → I32}
    (hf : Function.Injective f) : Function.Injective (coordEmb f) := by
  intro x y h
  funext j
  rw [← coordEmb_apply_at hf x j, ← coordEmb_apply_at hf y j, h]

theorem mem_coordEmb_range {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → I32}
    (hf : Function.Injective f) (v : I32 → ℂ) :
    v ∈ LinearMap.range (coordEmb f) ↔ ∀ i ∉ Set.range f, v i = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ i hi
    exact coordEmb_apply_of_not_mem w hi
  · intro hv
    refine ⟨fun j => v (f j), ?_⟩
    funext i
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, hj⟩ := hi
      subst hj
      rw [coordEmb_apply_at hf]
    · rw [coordEmb_apply_of_not_mem _ hi, hv i hi]

theorem finrank_coordEmb_range {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → I32}
    (hf : Function.Injective f) :
    Module.finrank ℂ (LinearMap.range (coordEmb f)) = Fintype.card ι := by
  rw [LinearMap.finrank_range_of_inj (coordEmb_injective hf),
    Module.finrank_fintype_fun_eq_card]


/-! ## Parametrizations and range characterizations -/

def a9 : Fin 3 → Fin 8 := ![2, 4, 6]
def a25 : Fin 3 → Fin 8 := ![3, 5, 7]
def bPlus : Fin 2 → Fin 4 := ![0, 3]
def bMinus : Fin 2 → Fin 4 := ![1, 2]

def f4 : Fin 4 → I32 := fun b => blkIdx b 1
def f9 : Fin 4 × Fin 3 → I32 := fun p => blkIdx p.1 (a9 p.2)
def f25 : Fin 4 × Fin 3 → I32 := fun p => blkIdx p.1 (a25 p.2)
def fQ : Fin 4 → I32 := fun b => blkIdx b 0
def fPlus : Fin 2 × Fin 8 → I32 := fun p => blkIdx (bPlus p.1) p.2
def fMinus : Fin 2 × Fin 8 → I32 := fun p => blkIdx (bMinus p.1) p.2
def f4p : Fin 2 → I32 := fun t => blkIdx (bPlus t) 1
def f4m : Fin 2 → I32 := fun t => blkIdx (bMinus t) 1
def f9p : Fin 2 × Fin 3 → I32 := fun p => blkIdx (bPlus p.1) (a9 p.2)
def f9m : Fin 2 × Fin 3 → I32 := fun p => blkIdx (bMinus p.1) (a9 p.2)
def f25p : Fin 2 × Fin 3 → I32 := fun p => blkIdx (bPlus p.1) (a25 p.2)
def f25m : Fin 2 × Fin 3 → I32 := fun p => blkIdx (bMinus p.1) (a25 p.2)
def fQp : Fin 2 → I32 := fun t => blkIdx (bPlus t) 0
def fQm : Fin 2 → I32 := fun t => blkIdx (bMinus t) 0

def gammaPlusSub : Submodule ℂ (I32 → ℂ) := LinearMap.range (coordEmb fPlus)
def gammaMinusSub : Submodule ℂ (I32 → ℂ) := LinearMap.range (coordEmb fMinus)

theorem a9_val (t : Fin 3) : (a9 t).val = 2 ∨ (a9 t).val = 4 ∨ (a9 t).val = 6 := by
  fin_cases t <;> norm_num [a9]

theorem a25_val (t : Fin 3) : (a25 t).val = 3 ∨ (a25 t).val = 5 ∨ (a25 t).val = 7 := by
  fin_cases t <;> norm_num [a25]

theorem a9_0 : a9 0 = (2 : Fin 8) := by norm_num [a9]
theorem a9_1 : a9 1 = (4 : Fin 8) := by norm_num [a9]
theorem a9_2 : a9 2 = (6 : Fin 8) := by norm_num [a9]

theorem a9_surj : ∀ a : Fin 8, a.val = 2 ∨ a.val = 4 ∨ a.val = 6 → ∃ t, a9 t = a := by
  intro a h
  rcases h with h | h | h
  · exact ⟨0, by rw [a9_0]; exact Fin.ext h.symm⟩
  · exact ⟨1, by rw [a9_1]; exact Fin.ext h.symm⟩
  · exact ⟨2, by rw [a9_2]; exact Fin.ext h.symm⟩

theorem a25_0 : a25 0 = (3 : Fin 8) := by norm_num [a25]
theorem a25_1 : a25 1 = (5 : Fin 8) := by norm_num [a25]
theorem a25_2 : a25 2 = (7 : Fin 8) := by norm_num [a25]

theorem a25_surj : ∀ a : Fin 8, a.val = 3 ∨ a.val = 5 ∨ a.val = 7 → ∃ t, a25 t = a := by
  intro a h
  rcases h with h | h | h
  · exact ⟨0, by rw [a25_0]; exact Fin.ext h.symm⟩
  · exact ⟨1, by rw [a25_1]; exact Fin.ext h.symm⟩
  · exact ⟨2, by rw [a25_2]; exact Fin.ext h.symm⟩

theorem bPlus_val (t : Fin 2) : (bPlus t).val = 0 ∨ (bPlus t).val = 3 := by
  fin_cases t <;> norm_num [bPlus]

theorem bMinus_val (t : Fin 2) : (bMinus t).val = 1 ∨ (bMinus t).val = 2 := by
  fin_cases t <;> norm_num [bMinus]

theorem bPlus_0 : bPlus 0 = (0 : Fin 4) := by norm_num [bPlus]
theorem bPlus_1 : bPlus 1 = (3 : Fin 4) := by norm_num [bPlus]

theorem bPlus_surj : ∀ b : Fin 4, b.val = 0 ∨ b.val = 3 → ∃ t, bPlus t = b := by
  intro b h
  rcases h with h | h
  · exact ⟨0, by rw [bPlus_0]; exact Fin.ext h.symm⟩
  · exact ⟨1, by rw [bPlus_1]; exact Fin.ext h.symm⟩

theorem bMinus_0 : bMinus 0 = (1 : Fin 4) := by norm_num [bMinus]
theorem bMinus_1 : bMinus 1 = (2 : Fin 4) := by norm_num [bMinus]

theorem bMinus_surj : ∀ b : Fin 4, b.val = 1 ∨ b.val = 2 → ∃ t, bMinus t = b := by
  intro b h
  rcases h with h | h
  · exact ⟨0, by rw [bMinus_0]; exact Fin.ext h.symm⟩
  · exact ⟨1, by rw [bMinus_1]; exact Fin.ext h.symm⟩

theorem blkIdx_eq_of_aOf {i : I32} {a : Fin 8} (h : aOf i = a) : blkIdx (bOf i) a = i := by
  conv_rhs => rw [← eq_blkIdx i]
  rw [h]

theorem blkIdx_eq_of_bOf {i : I32} {b : Fin 4} (h : bOf i = b) : blkIdx b (aOf i) = i := by
  conv_rhs => rw [← eq_blkIdx i]
  rw [h]

theorem range_f4_aOf (i : I32) : i ∈ Set.range f4 ↔ (aOf i).val = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    show (aOf (blkIdx b 1)).val = 1
    rw [blkIdx_aOf, Fin.val_one]
  · intro h
    exact ⟨bOf i, blkIdx_eq_of_aOf (Fin.ext h)⟩

theorem range_f9_aOf (i : I32) :
    i ∈ Set.range f9 ↔ (aOf i).val = 2 ∨ (aOf i).val = 4 ∨ (aOf i).val = 6 := by
  constructor
  · rintro ⟨⟨b, t⟩, rfl⟩
    show (aOf (blkIdx b (a9 t))).val = 2 ∨ (aOf (blkIdx b (a9 t))).val = 4
      ∨ (aOf (blkIdx b (a9 t))).val = 6
    rw [blkIdx_aOf]
    exact a9_val t
  · intro h
    obtain ⟨t, ht⟩ := a9_surj (aOf i) h
    exact ⟨(bOf i, t), by show blkIdx (bOf i) (a9 t) = i; rw [ht]; exact eq_blkIdx i⟩

theorem range_f25_aOf (i : I32) :
    i ∈ Set.range f25 ↔ (aOf i).val = 3 ∨ (aOf i).val = 5 ∨ (aOf i).val = 7 := by
  constructor
  · rintro ⟨⟨b, t⟩, rfl⟩
    show (aOf (blkIdx b (a25 t))).val = 3 ∨ (aOf (blkIdx b (a25 t))).val = 5
      ∨ (aOf (blkIdx b (a25 t))).val = 7
    rw [blkIdx_aOf]
    exact a25_val t
  · intro h
    obtain ⟨t, ht⟩ := a25_surj (aOf i) h
    exact ⟨(bOf i, t), by show blkIdx (bOf i) (a25 t) = i; rw [ht]; exact eq_blkIdx i⟩

theorem range_fQ_aOf (i : I32) : i ∈ Set.range fQ ↔ (aOf i).val = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    show (aOf (blkIdx b 0)).val = 0
    rw [blkIdx_aOf, Fin.val_zero]
  · intro h
    exact ⟨bOf i, blkIdx_eq_of_aOf (Fin.ext h)⟩

theorem range_fPlus_bOf (i : I32) :
    i ∈ Set.range fPlus ↔ (bOf i).val = 0 ∨ (bOf i).val = 3 := by
  constructor
  · rintro ⟨⟨t, a⟩, rfl⟩
    show (bOf (blkIdx (bPlus t) a)).val = 0 ∨ (bOf (blkIdx (bPlus t) a)).val = 3
    rw [blkIdx_bOf]
    exact bPlus_val t
  · intro h
    obtain ⟨t, ht⟩ := bPlus_surj (bOf i) h
    exact ⟨(t, aOf i), by show blkIdx (bPlus t) (aOf i) = i; rw [ht]; exact eq_blkIdx i⟩

theorem range_fMinus_bOf (i : I32) :
    i ∈ Set.range fMinus ↔ (bOf i).val = 1 ∨ (bOf i).val = 2 := by
  constructor
  · rintro ⟨⟨t, a⟩, rfl⟩
    show (bOf (blkIdx (bMinus t) a)).val = 1 ∨ (bOf (blkIdx (bMinus t) a)).val = 2
    rw [blkIdx_bOf]
    exact bMinus_val t
  · intro h
    obtain ⟨t, ht⟩ := bMinus_surj (bOf i) h
    exact ⟨(t, aOf i), by show blkIdx (bMinus t) (aOf i) = i; rw [ht]; exact eq_blkIdx i⟩

theorem range_f4_char (i : I32) : i ∈ Set.range f4 ↔ cval i = 0 ∧ dval i = 4 := by
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [range_f4_aOf, blkIdx_aOf, cval_blk, dval_blk]
  fin_cases b <;> fin_cases a <;> norm_num [wvec, wvec']

theorem range_f9_char (i : I32) : i ∈ Set.range f9 ↔ cval i = 0 ∧ dval i = 9 := by
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [range_f9_aOf, blkIdx_aOf, cval_blk, dval_blk]
  fin_cases b <;> fin_cases a <;> norm_num [wvec, wvec']

theorem range_f25_char (i : I32) : i ∈ Set.range f25 ↔ cval i = 0 ∧ dval i = 25 := by
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [range_f25_aOf, blkIdx_aOf, cval_blk, dval_blk]
  fin_cases b <;> fin_cases a <;> norm_num [wvec, wvec']

theorem range_fQ_char (i : I32) : i ∈ Set.range fQ ↔ cval i ≠ 0 := by
  obtain ⟨b, a, rfl⟩ : ∃ b a, i = blkIdx b a := ⟨bOf i, aOf i, (eq_blkIdx i).symm⟩
  rw [range_fQ_aOf, blkIdx_aOf, cval_blk]
  fin_cases a <;> norm_num


/-! ## Injectivity of the parametrizations -/

theorem bPlus_inj : Function.Injective bPlus := by decide

theorem bMinus_inj : Function.Injective bMinus := by decide

theorem a9_inj : Function.Injective a9 := by decide

theorem a25_inj : Function.Injective a25 := by decide

theorem f4_inj : Function.Injective f4 := by
  intro b b' h
  exact (blkIdx_inj h).1

theorem fQ_inj : Function.Injective fQ := by
  intro b b' h
  exact (blkIdx_inj h).1

theorem f9_inj : Function.Injective f9 := by
  rintro ⟨b, t⟩ ⟨b', t'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  refine Prod.ext hb ?_
  exact a9_inj ha

theorem f25_inj : Function.Injective f25 := by
  rintro ⟨b, t⟩ ⟨b', t'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  refine Prod.ext hb ?_
  exact a25_inj ha

theorem fPlus_inj : Function.Injective fPlus := by
  rintro ⟨s, a⟩ ⟨s', a'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  exact Prod.ext (bPlus_inj hb) ha

theorem fMinus_inj : Function.Injective fMinus := by
  rintro ⟨s, a⟩ ⟨s', a'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  exact Prod.ext (bMinus_inj hb) ha

theorem f4p_inj : Function.Injective f4p := by
  intro s s' h
  exact bPlus_inj (blkIdx_inj h).1

theorem f4m_inj : Function.Injective f4m := by
  intro s s' h
  exact bMinus_inj (blkIdx_inj h).1

theorem fQp_inj : Function.Injective fQp := by
  intro s s' h
  exact bPlus_inj (blkIdx_inj h).1

theorem fQm_inj : Function.Injective fQm := by
  intro s s' h
  exact bMinus_inj (blkIdx_inj h).1

theorem f9p_inj : Function.Injective f9p := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  refine Prod.ext (bPlus_inj hb) ?_
  exact a9_inj ha

theorem f9m_inj : Function.Injective f9m := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  refine Prod.ext (bMinus_inj hb) ?_
  exact a9_inj ha

theorem f25p_inj : Function.Injective f25p := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  refine Prod.ext (bPlus_inj hb) ?_
  exact a25_inj ha

theorem f25m_inj : Function.Injective f25m := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  obtain ⟨hb, ha⟩ := blkIdx_inj h
  refine Prod.ext (bMinus_inj hb) ?_
  exact a25_inj ha

/-! ## Eigenspaces and the joint quadratic kernel -/

def eigSub (μ : ℂ) : Submodule ℂ (I32 → ℂ) :=
  Module.End.eigenspace (Matrix.toLin' K0) μ

theorem mem_eigSub {μ : ℂ} {v : I32 → ℂ} :
    v ∈ eigSub μ ↔ K0 *ᵥ v = μ • v := by
  rw [eigSub, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

def quadKer : Submodule ℂ (I32 → ℂ) :=
  LinearMap.ker (Matrix.toLin' (K0 ^ 2 - 51 • K0 + 1))

theorem mem_quadKer {v : I32 → ℂ} :
    v ∈ quadKer ↔ (K0 ^ 2 - 51 • K0 + 1) *ᵥ v = 0 := by
  rw [quadKer, LinearMap.mem_ker, Matrix.toLin'_apply]

/-! ## The generic eigenspace identification (2x2 determinant argument) -/

theorem eig_eq_range_of {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → I32}
    (hf : Function.Injective f) {μ : ℂ}
    (hrange : ∀ i, i ∈ Set.range f ↔ cval i = 0 ∧ dval i = μ)
    (hdet : μ ^ 2 - 51 * μ + 1 ≠ 0) :
    eigSub μ = LinearMap.range (coordEmb f) := by
  ext v
  rw [mem_eigSub, mem_coordEmb_range hf]
  constructor
  · intro hv i hi
    have eq_i : dval i * v i + cval i * v (pIdx i) = μ * v i := by
      have h := congrFun hv i
      rwa [K0_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h
    have eq_p : dval (pIdx i) * v (pIdx i) + cval i * v i = μ * v (pIdx i) := by
      have h := congrFun hv (pIdx i)
      rwa [K0_mulVec_apply, cval_pIdx, pIdx_involutive, Pi.smul_apply, smul_eq_mul] at h
    by_cases hc : cval i = 0
    · have hd : dval i ≠ μ := fun hcon => hi ((hrange i).mpr ⟨hc, hcon⟩)
      have hz : (dval i - μ) * v i = 0 := by
        rw [hc] at eq_i
        linear_combination eq_i
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (sub_ne_zero.mpr hd)
      · exact h
    · have hsum := (seat_identities i).1 hc
      have hprod := (seat_identities i).2.1 hc
      have hc2 := (seat_identities i).2.2.1 hc
      have hprod' : dval i * dval (pIdx i) - cval i ^ 2 = 1 := by
        linear_combination hprod - hc2
      have h1' : (dval i - μ) * v i + cval i * v (pIdx i) = 0 := by
        linear_combination eq_i
      have h2' : cval i * v i + (dval (pIdx i) - μ) * v (pIdx i) = 0 := by
        linear_combination eq_p
      have key : (μ ^ 2 - 51 * μ + 1) * v i = 0 := by
        linear_combination (dval (pIdx i) - μ) * h1' - cval i * h2'
          - v i * hprod' + μ * v i * hsum
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hdet
      · exact h
  · intro hv
    funext i
    rw [K0_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : cval i = 0
    · by_cases hd : dval i = μ
      · rw [hd, hc]; simp
      · have hvi : v i = 0 :=
          hv i (fun hi => hd ((hrange i).mp hi).2)
        rw [hvi, hc]; simp
    · have hvi : v i = 0 :=
        hv i (fun hi => hc ((hrange i).mp hi).1)
      have hvp : v (pIdx i) = 0 :=
        hv (pIdx i) (fun hi => hc (by
          rw [← cval_pIdx]; exact ((hrange (pIdx i)).mp hi).1))
      rw [hvi, hvp]; simp

theorem quadKer_eq_range : quadKer = LinearMap.range (coordEmb fQ) := by
  ext v
  rw [mem_quadKer, mem_coordEmb_range fQ_inj]
  constructor
  · intro hv i hi
    have hc : cval i = 0 := by
      by_contra hcon
      exact hi ((range_fQ_char i).mpr hcon)
    have h := congrFun hv i
    rw [quad_mulVec_apply, hc, Pi.zero_apply] at h
    have h2 : (dval i ^ 2 - 51 * dval i + 1) * v i = 0 := by
      linear_combination h
    have hne : dval i ^ 2 - 51 * dval i + 1 ≠ 0 :=
      (seat_identities i).2.2.2.2.2 hc
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hne
    · exact h3
  · intro hv
    funext i
    rw [quad_mulVec_apply]
    by_cases hc : cval i = 0
    · have hvi : v i = 0 :=
        hv i (fun hi => ((range_fQ_char i).mp hi) hc)
      rw [hc, hvi]; simp
    · have hD := (seat_identities i).2.2.2.1 hc
      have hsum := (seat_identities i).1 hc
      have h20 : dval i + dval (pIdx i) - 51 = 0 := by linear_combination hsum
      rw [show dval i ^ 2 + cval i ^ 2 - 51 * dval i + 1 = 0 from hD, h20]
      simp

theorem eig_four_eq_range : eigSub 4 = LinearMap.range (coordEmb f4) :=
  eig_eq_range_of f4_inj range_f4_char (by norm_num)

theorem eig_nine_eq_range : eigSub 9 = LinearMap.range (coordEmb f9) :=
  eig_eq_range_of f9_inj range_f9_char (by norm_num)

theorem eig_twentyfive_eq_range : eigSub 25 = LinearMap.range (coordEmb f25) :=
  eig_eq_range_of f25_inj range_f25_char (by norm_num)


/-! ## Split range characterizations -/

theorem range_f4p_aux (i : I32) :
    i ∈ Set.range f4p ↔ (aOf i).val = 1 ∧ ((bOf i).val = 0 ∨ (bOf i).val = 3) := by
  constructor
  · rintro ⟨t, rfl⟩
    show (aOf (blkIdx (bPlus t) 1)).val = 1
      ∧ ((bOf (blkIdx (bPlus t) 1)).val = 0 ∨ (bOf (blkIdx (bPlus t) 1)).val = 3)
    rw [blkIdx_aOf, blkIdx_bOf, Fin.val_one]
    exact ⟨rfl, bPlus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht⟩ := bPlus_surj (bOf i) h2
    refine ⟨t, ?_⟩
    show blkIdx (bPlus t) 1 = i
    rw [ht, show (1 : Fin 8) = aOf i from Fin.ext h1.symm]
    exact eq_blkIdx i

theorem range_f4m_aux (i : I32) :
    i ∈ Set.range f4m ↔ (aOf i).val = 1 ∧ ((bOf i).val = 1 ∨ (bOf i).val = 2) := by
  constructor
  · rintro ⟨t, rfl⟩
    show (aOf (blkIdx (bMinus t) 1)).val = 1
      ∧ ((bOf (blkIdx (bMinus t) 1)).val = 1 ∨ (bOf (blkIdx (bMinus t) 1)).val = 2)
    rw [blkIdx_aOf, blkIdx_bOf, Fin.val_one]
    exact ⟨rfl, bMinus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht⟩ := bMinus_surj (bOf i) h2
    refine ⟨t, ?_⟩
    show blkIdx (bMinus t) 1 = i
    rw [ht, show (1 : Fin 8) = aOf i from Fin.ext h1.symm]
    exact eq_blkIdx i

theorem range_f9p_aux (i : I32) :
    i ∈ Set.range f9p ↔ ((aOf i).val = 2 ∨ (aOf i).val = 4 ∨ (aOf i).val = 6)
      ∧ ((bOf i).val = 0 ∨ (bOf i).val = 3) := by
  constructor
  · rintro ⟨⟨t, s⟩, rfl⟩
    show ((aOf (blkIdx (bPlus t) (a9 s))).val = 2 ∨ (aOf (blkIdx (bPlus t) (a9 s))).val = 4
      ∨ (aOf (blkIdx (bPlus t) (a9 s))).val = 6)
      ∧ ((bOf (blkIdx (bPlus t) (a9 s))).val = 0 ∨ (bOf (blkIdx (bPlus t) (a9 s))).val = 3)
    rw [blkIdx_aOf, blkIdx_bOf]
    exact ⟨a9_val s, bPlus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := a9_surj (aOf i) h1
    obtain ⟨t, ht⟩ := bPlus_surj (bOf i) h2
    refine ⟨(t, s), ?_⟩
    show blkIdx (bPlus t) (a9 s) = i
    rw [ht, hs]
    exact eq_blkIdx i

theorem range_f9m_aux (i : I32) :
    i ∈ Set.range f9m ↔ ((aOf i).val = 2 ∨ (aOf i).val = 4 ∨ (aOf i).val = 6)
      ∧ ((bOf i).val = 1 ∨ (bOf i).val = 2) := by
  constructor
  · rintro ⟨⟨t, s⟩, rfl⟩
    show ((aOf (blkIdx (bMinus t) (a9 s))).val = 2 ∨ (aOf (blkIdx (bMinus t) (a9 s))).val = 4
      ∨ (aOf (blkIdx (bMinus t) (a9 s))).val = 6)
      ∧ ((bOf (blkIdx (bMinus t) (a9 s))).val = 1 ∨ (bOf (blkIdx (bMinus t) (a9 s))).val = 2)
    rw [blkIdx_aOf, blkIdx_bOf]
    exact ⟨a9_val s, bMinus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := a9_surj (aOf i) h1
    obtain ⟨t, ht⟩ := bMinus_surj (bOf i) h2
    refine ⟨(t, s), ?_⟩
    show blkIdx (bMinus t) (a9 s) = i
    rw [ht, hs]
    exact eq_blkIdx i

theorem range_f25p_aux (i : I32) :
    i ∈ Set.range f25p ↔ ((aOf i).val = 3 ∨ (aOf i).val = 5 ∨ (aOf i).val = 7)
      ∧ ((bOf i).val = 0 ∨ (bOf i).val = 3) := by
  constructor
  · rintro ⟨⟨t, s⟩, rfl⟩
    show ((aOf (blkIdx (bPlus t) (a25 s))).val = 3 ∨ (aOf (blkIdx (bPlus t) (a25 s))).val = 5
      ∨ (aOf (blkIdx (bPlus t) (a25 s))).val = 7)
      ∧ ((bOf (blkIdx (bPlus t) (a25 s))).val = 0 ∨ (bOf (blkIdx (bPlus t) (a25 s))).val = 3)
    rw [blkIdx_aOf, blkIdx_bOf]
    exact ⟨a25_val s, bPlus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := a25_surj (aOf i) h1
    obtain ⟨t, ht⟩ := bPlus_surj (bOf i) h2
    refine ⟨(t, s), ?_⟩
    show blkIdx (bPlus t) (a25 s) = i
    rw [ht, hs]
    exact eq_blkIdx i

theorem range_f25m_aux (i : I32) :
    i ∈ Set.range f25m ↔ ((aOf i).val = 3 ∨ (aOf i).val = 5 ∨ (aOf i).val = 7)
      ∧ ((bOf i).val = 1 ∨ (bOf i).val = 2) := by
  constructor
  · rintro ⟨⟨t, s⟩, rfl⟩
    show ((aOf (blkIdx (bMinus t) (a25 s))).val = 3 ∨ (aOf (blkIdx (bMinus t) (a25 s))).val = 5
      ∨ (aOf (blkIdx (bMinus t) (a25 s))).val = 7)
      ∧ ((bOf (blkIdx (bMinus t) (a25 s))).val = 1 ∨ (bOf (blkIdx (bMinus t) (a25 s))).val = 2)
    rw [blkIdx_aOf, blkIdx_bOf]
    exact ⟨a25_val s, bMinus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := a25_surj (aOf i) h1
    obtain ⟨t, ht⟩ := bMinus_surj (bOf i) h2
    refine ⟨(t, s), ?_⟩
    show blkIdx (bMinus t) (a25 s) = i
    rw [ht, hs]
    exact eq_blkIdx i

theorem range_fQp_aux (i : I32) :
    i ∈ Set.range fQp ↔ (aOf i).val = 0 ∧ ((bOf i).val = 0 ∨ (bOf i).val = 3) := by
  constructor
  · rintro ⟨t, rfl⟩
    show (aOf (blkIdx (bPlus t) 0)).val = 0
      ∧ ((bOf (blkIdx (bPlus t) 0)).val = 0 ∨ (bOf (blkIdx (bPlus t) 0)).val = 3)
    rw [blkIdx_aOf, blkIdx_bOf, Fin.val_zero]
    exact ⟨rfl, bPlus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht⟩ := bPlus_surj (bOf i) h2
    refine ⟨t, ?_⟩
    show blkIdx (bPlus t) 0 = i
    rw [ht, show (0 : Fin 8) = aOf i from Fin.ext h1.symm]
    exact eq_blkIdx i

theorem range_fQm_aux (i : I32) :
    i ∈ Set.range fQm ↔ (aOf i).val = 0 ∧ ((bOf i).val = 1 ∨ (bOf i).val = 2) := by
  constructor
  · rintro ⟨t, rfl⟩
    show (aOf (blkIdx (bMinus t) 0)).val = 0
      ∧ ((bOf (blkIdx (bMinus t) 0)).val = 1 ∨ (bOf (blkIdx (bMinus t) 0)).val = 2)
    rw [blkIdx_aOf, blkIdx_bOf, Fin.val_zero]
    exact ⟨rfl, bMinus_val t⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht⟩ := bMinus_surj (bOf i) h2
    refine ⟨t, ?_⟩
    show blkIdx (bMinus t) 0 = i
    rw [ht, show (0 : Fin 8) = aOf i from Fin.ext h1.symm]
    exact eq_blkIdx i

theorem range_f4p_char (i : I32) :
    i ∈ Set.range f4p ↔ i ∈ Set.range f4 ∧ i ∈ Set.range fPlus := by
  rw [range_f4p_aux, range_f4_aOf, range_fPlus_bOf]

theorem range_f4m_char (i : I32) :
    i ∈ Set.range f4m ↔ i ∈ Set.range f4 ∧ i ∈ Set.range fMinus := by
  rw [range_f4m_aux, range_f4_aOf, range_fMinus_bOf]

theorem range_f9p_char (i : I32) :
    i ∈ Set.range f9p ↔ i ∈ Set.range f9 ∧ i ∈ Set.range fPlus := by
  rw [range_f9p_aux, range_f9_aOf, range_fPlus_bOf]

theorem range_f9m_char (i : I32) :
    i ∈ Set.range f9m ↔ i ∈ Set.range f9 ∧ i ∈ Set.range fMinus := by
  rw [range_f9m_aux, range_f9_aOf, range_fMinus_bOf]

theorem range_f25p_char (i : I32) :
    i ∈ Set.range f25p ↔ i ∈ Set.range f25 ∧ i ∈ Set.range fPlus := by
  rw [range_f25p_aux, range_f25_aOf, range_fPlus_bOf]

theorem range_f25m_char (i : I32) :
    i ∈ Set.range f25m ↔ i ∈ Set.range f25 ∧ i ∈ Set.range fMinus := by
  rw [range_f25m_aux, range_f25_aOf, range_fMinus_bOf]

theorem range_fQp_char (i : I32) :
    i ∈ Set.range fQp ↔ i ∈ Set.range fQ ∧ i ∈ Set.range fPlus := by
  rw [range_fQp_aux, range_fQ_aOf, range_fPlus_bOf]

theorem range_fQm_char (i : I32) :
    i ∈ Set.range fQm ↔ i ∈ Set.range fQ ∧ i ∈ Set.range fMinus := by
  rw [range_fQm_aux, range_fQ_aOf, range_fMinus_bOf]

/-! ## The generic split identification -/

theorem split_eq_range_of {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {f : ι → I32} {fp : ι' → I32}
    {S : Submodule ℂ (I32 → ℂ)} {G : Submodule ℂ (I32 → ℂ)} {g : (Fin 2 × Fin 8) → I32}
    (hf : Function.Injective f) (hfp : Function.Injective fp) (hg : Function.Injective g)
    (hS : S = LinearMap.range (coordEmb f))
    (hG : G = LinearMap.range (coordEmb g))
    (hrange : ∀ i, i ∈ Set.range fp ↔ i ∈ Set.range f ∧ i ∈ Set.range g) :
    S ⊓ G = LinearMap.range (coordEmb fp) := by
  rw [hS, hG]
  ext v
  simp only [Submodule.mem_inf, mem_coordEmb_range hf, mem_coordEmb_range hg,
    mem_coordEmb_range hfp]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    by_cases hfi : i ∈ Set.range f
    · by_cases hgi : i ∈ Set.range g
      · exact (hi ((hrange i).mpr ⟨hfi, hgi⟩)).elim
      · exact h2 i hgi
    · exact h1 i hfi
  · intro hv
    exact ⟨fun i hi => hv i (fun hifp => hi ((hrange i).mp hifp).1),
      fun i hi => hv i (fun hifp => hi ((hrange i).mp hifp).2)⟩

theorem eig_four_split_plus :
    eigSub 4 ⊓ gammaPlusSub = LinearMap.range (coordEmb f4p) :=
  split_eq_range_of f4_inj f4p_inj fPlus_inj eig_four_eq_range rfl range_f4p_char

theorem eig_four_split_minus :
    eigSub 4 ⊓ gammaMinusSub = LinearMap.range (coordEmb f4m) :=
  split_eq_range_of f4_inj f4m_inj fMinus_inj eig_four_eq_range rfl range_f4m_char

theorem eig_nine_split_plus :
    eigSub 9 ⊓ gammaPlusSub = LinearMap.range (coordEmb f9p) :=
  split_eq_range_of f9_inj f9p_inj fPlus_inj eig_nine_eq_range rfl range_f9p_char

theorem eig_nine_split_minus :
    eigSub 9 ⊓ gammaMinusSub = LinearMap.range (coordEmb f9m) :=
  split_eq_range_of f9_inj f9m_inj fMinus_inj eig_nine_eq_range rfl range_f9m_char

theorem eig_twentyfive_split_plus :
    eigSub 25 ⊓ gammaPlusSub = LinearMap.range (coordEmb f25p) :=
  split_eq_range_of f25_inj f25p_inj fPlus_inj eig_twentyfive_eq_range rfl range_f25p_char

theorem eig_twentyfive_split_minus :
    eigSub 25 ⊓ gammaMinusSub = LinearMap.range (coordEmb f25m) :=
  split_eq_range_of f25_inj f25m_inj fMinus_inj eig_twentyfive_eq_range rfl range_f25m_char

theorem quad_split_plus :
    quadKer ⊓ gammaPlusSub = LinearMap.range (coordEmb fQp) :=
  split_eq_range_of fQ_inj fQp_inj fPlus_inj quadKer_eq_range rfl range_fQp_char

theorem quad_split_minus :
    quadKer ⊓ gammaMinusSub = LinearMap.range (coordEmb fQm) :=
  split_eq_range_of fQ_inj fQm_inj fMinus_inj quadKer_eq_range rfl range_fQm_char

/-! ## Finrank headlines: totals -/

theorem finrank_eig_four : Module.finrank ℂ (eigSub 4) = 4 := by
  rw [eig_four_eq_range, finrank_coordEmb_range f4_inj, Fintype.card_fin]

theorem finrank_eig_nine : Module.finrank ℂ (eigSub 9) = 12 := by
  rw [eig_nine_eq_range, finrank_coordEmb_range f9_inj]
  simp

theorem finrank_eig_twentyfive : Module.finrank ℂ (eigSub 25) = 12 := by
  rw [eig_twentyfive_eq_range, finrank_coordEmb_range f25_inj]
  simp

theorem finrank_quadKer : Module.finrank ℂ quadKer = 4 := by
  rw [quadKer_eq_range, finrank_coordEmb_range fQ_inj, Fintype.card_fin]

/-! ## Finrank headlines: γ-splits -/

theorem finrank_eig_four_split :
    Module.finrank ℂ ↥(eigSub 4 ⊓ gammaPlusSub) = 2
    ∧ Module.finrank ℂ ↥(eigSub 4 ⊓ gammaMinusSub) = 2 := by
  refine ⟨?_, ?_⟩
  · rw [eig_four_split_plus, finrank_coordEmb_range f4p_inj, Fintype.card_fin]
  · rw [eig_four_split_minus, finrank_coordEmb_range f4m_inj, Fintype.card_fin]

theorem finrank_eig_nine_split :
    Module.finrank ℂ ↥(eigSub 9 ⊓ gammaPlusSub) = 6
    ∧ Module.finrank ℂ ↥(eigSub 9 ⊓ gammaMinusSub) = 6 := by
  refine ⟨?_, ?_⟩
  · rw [eig_nine_split_plus, finrank_coordEmb_range f9p_inj]; simp
  · rw [eig_nine_split_minus, finrank_coordEmb_range f9m_inj]; simp

theorem finrank_eig_twentyfive_split :
    Module.finrank ℂ ↥(eigSub 25 ⊓ gammaPlusSub) = 6
    ∧ Module.finrank ℂ ↥(eigSub 25 ⊓ gammaMinusSub) = 6 := by
  refine ⟨?_, ?_⟩
  · rw [eig_twentyfive_split_plus, finrank_coordEmb_range f25p_inj]; simp
  · rw [eig_twentyfive_split_minus, finrank_coordEmb_range f25m_inj]; simp

theorem finrank_quad_split :
    Module.finrank ℂ ↥(quadKer ⊓ gammaPlusSub) = 2
    ∧ Module.finrank ℂ ↥(quadKer ⊓ gammaMinusSub) = 2 := by
  refine ⟨?_, ?_⟩
  · rw [quad_split_plus, finrank_coordEmb_range fQp_inj, Fintype.card_fin]
  · rw [quad_split_minus, finrank_coordEmb_range fQm_inj, Fintype.card_fin]


/-! ## Annihilation and factor nontriviality -/

theorem h10_eq : (10 : I32) = blkIdx 1 2 := by decide

theorem h1_eq : (1 : I32) = blkIdx 0 1 := by decide

theorem dval10 : dval (10 : I32) = 9 := by
  rw [h10_eq, dval_blk]; norm_num [wvec', wvec]

theorem cval10 : cval (10 : I32) = 0 := by
  rw [h10_eq, cval_blk]; norm_num

theorem dval1 : dval (1 : I32) = 4 := by
  rw [h1_eq, dval_blk]; norm_num [wvec, wvec']

theorem cval1 : cval (1 : I32) = 0 := by
  rw [h1_eq, cval_blk]; norm_num

theorem annihilating_polynomial :
    (K0 - (4 : ℂ) • 1) * (K0 - (9 : ℂ) • 1) * (K0 - (25 : ℂ) • 1) * (K0 ^ 2 - 51 • K0 + 1) = 0 := by
  have step : ∀ (μ : ℂ) (w : I32 → ℂ), (∀ i, cval i ≠ 0 → w i = 0) →
      (∀ i, cval i ≠ 0 → ((K0 - μ • 1) *ᵥ w) i = 0)
      ∧ (∀ i, cval i = 0 → ((K0 - μ • 1) *ᵥ w) i = (dval i - μ) * w i) := by
    intro μ w hw
    constructor
    · intro i hi
      rw [factor_mulVec_apply, hw i hi, hw (pIdx i) (by rwa [cval_pIdx])]
      simp
    · intro i hi
      rw [factor_mulVec_apply, hi]
      simp
  have hquad : ∀ (v : I32 → ℂ) (i : I32), cval i ≠ 0 →
      ((K0 ^ 2 - 51 • K0 + 1) *ᵥ v) i = 0 := by
    intro v i hi
    rw [quad_mulVec_apply, (seat_identities i).2.2.2.1 hi,
      show dval i + dval (pIdx i) - 51 = 0 by
        linear_combination (seat_identities i).1 hi]
    simp
  have hquad0 : ∀ (v : I32 → ℂ) (i : I32), cval i = 0 →
      ((K0 ^ 2 - 51 • K0 + 1) *ᵥ v) i = (dval i ^ 2 - 51 * dval i + 1) * v i := by
    intro v i hi
    rw [quad_mulVec_apply, hi]
    ring
  have key : ∀ v : I32 → ℂ,
      ((K0 - (4 : ℂ) • 1) * (K0 - (9 : ℂ) • 1) * (K0 - (25 : ℂ) • 1) * (K0 ^ 2 - 51 • K0 + 1)) *ᵥ v = 0 := by
    intro v
    simp only [← Matrix.mulVec_mulVec]
    set u0 := (K0 ^ 2 - 51 • K0 + 1) *ᵥ v with hu0
    set u1 := (K0 - (25 : ℂ) • 1) *ᵥ u0 with hu1
    set u2 := (K0 - (9 : ℂ) • 1) *ᵥ u1 with hu2
    funext i
    simp only [Pi.zero_apply]
    have hu0c : ∀ i, cval i ≠ 0 → u0 i = 0 := fun i hi => hquad v i hi
    have hu1c : ∀ i, cval i ≠ 0 → u1 i = 0 := (step 25 u0 hu0c).1
    have hu2c : ∀ i, cval i ≠ 0 → u2 i = 0 := (step 9 u1 hu1c).1
    by_cases hc : cval i = 0
    · have e3 : ((K0 - (4 : ℂ) • 1) *ᵥ u2) i = (dval i - 4) * u2 i := (step 4 u2 hu2c).2 i hc
      have e2 : u2 i = (dval i - 9) * u1 i := (step 9 u1 hu1c).2 i hc
      have e1 : u1 i = (dval i - 25) * u0 i := (step 25 u0 hu0c).2 i hc
      have e0 : u0 i = (dval i ^ 2 - 51 * dval i + 1) * v i := hquad0 v i hc
      rw [e3, e2, e1, e0]
      rcases (seat_identities i).2.2.2.2.1 hc with h | h | h <;> rw [h] <;> norm_num
    · exact (step 4 u2 hu2c).1 i hc
  ext i j
  have h := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h

theorem factors_nonzero :
    (K0 - (4 : ℂ) • 1) ≠ 0 ∧ (K0 - (9 : ℂ) • 1) ≠ 0 ∧ (K0 - (25 : ℂ) • 1) ≠ 0
    ∧ (K0 ^ 2 - 51 • K0 + 1) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h2 : ((K0 - (4 : ℂ) • 1) *ᵥ Pi.single 10 (1 : ℂ)) 10 = 0 := by
      rw [h]; simp
    rw [factor_mulVec_apply, Pi.single_eq_same, dval10, cval10] at h2
    norm_num at h2
  · intro h
    have h2 : ((K0 - (9 : ℂ) • 1) *ᵥ Pi.single 1 (1 : ℂ)) 1 = 0 := by
      rw [h]; simp
    rw [factor_mulVec_apply, Pi.single_eq_same, dval1, cval1] at h2
    norm_num at h2
  · intro h
    have h2 : ((K0 - (25 : ℂ) • 1) *ᵥ Pi.single 1 (1 : ℂ)) 1 = 0 := by
      rw [h]; simp
    rw [factor_mulVec_apply, Pi.single_eq_same, dval1, cval1] at h2
    norm_num at h2
  · intro h
    have h2 : ((K0 ^ 2 - 51 • K0 + 1) *ᵥ Pi.single 10 (1 : ℂ)) 10 = 0 := by
      rw [h]; simp
    rw [quad_mulVec_apply, Pi.single_eq_same, dval10, cval10] at h2
    norm_num at h2

/-! ## The assembled VL-4a table -/

theorem vortex_locus_full_table :
    (K0 - (4 : ℂ) • 1) * (K0 - (9 : ℂ) • 1) * (K0 - (25 : ℂ) • 1) * (K0 ^ 2 - 51 • K0 + 1) = 0
    ∧ (K0 - (4 : ℂ) • 1) ≠ 0 ∧ (K0 - (9 : ℂ) • 1) ≠ 0 ∧ (K0 - (25 : ℂ) • 1) ≠ 0
    ∧ (K0 ^ 2 - 51 • K0 + 1) ≠ 0
    ∧ Module.finrank ℂ (eigSub 4) = 4
    ∧ Module.finrank ℂ (eigSub 9) = 12
    ∧ Module.finrank ℂ (eigSub 25) = 12
    ∧ Module.finrank ℂ quadKer = 4
    ∧ Module.finrank ℂ ↥(eigSub 4 ⊓ gammaPlusSub) = 2
    ∧ Module.finrank ℂ ↥(eigSub 4 ⊓ gammaMinusSub) = 2
    ∧ Module.finrank ℂ ↥(eigSub 9 ⊓ gammaPlusSub) = 6
    ∧ Module.finrank ℂ ↥(eigSub 9 ⊓ gammaMinusSub) = 6
    ∧ Module.finrank ℂ ↥(eigSub 25 ⊓ gammaPlusSub) = 6
    ∧ Module.finrank ℂ ↥(eigSub 25 ⊓ gammaMinusSub) = 6
    ∧ Module.finrank ℂ ↥(quadKer ⊓ gammaPlusSub) = 2
    ∧ Module.finrank ℂ ↥(quadKer ⊓ gammaMinusSub) = 2 :=
  ⟨annihilating_polynomial, factors_nonzero.1, factors_nonzero.2.1, factors_nonzero.2.2.1,
    factors_nonzero.2.2.2, finrank_eig_four, finrank_eig_nine, finrank_eig_twentyfive,
    finrank_quadKer, finrank_eig_four_split.1, finrank_eig_four_split.2,
    finrank_eig_nine_split.1, finrank_eig_nine_split.2, finrank_eig_twentyfive_split.1,
    finrank_eig_twentyfive_split.2, finrank_quad_split.1, finrank_quad_split.2⟩

end ThetLogos
