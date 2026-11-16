import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjAmend
import ThetLogos.DialOneGradeRConj
import ThetLogos.DialOneGradeRConjReadback
import ThetLogos.DialOnePiUFamily
import ThetLogos.DialOnePiAntiPackage
import ThetLogos.DialOneSwapOrbitBase
import ThetLogos.DialOneShapeBIdentification
import ThetLogos.DialOnePresSweep

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneConjugationCounterexample
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneSwapOrbitBase
open ThetLogos.DialOneAntiparticleChapter

namespace ThetLogos.Q1PresSweep

/-!
# ThetLogos.Q1PresSweep — Q1P-1: the preservation sweep at the new class members M1, M2

Governing texts: the Q1P-0 hull computation
(`q1p0-hull-computation-2026-11-14.md`) and the WP0 pricing
(`q1-pair-pricing-wp0-2026-11-14.md`). **NO CLAIM. Dials 0/4;
Dial 1 = 0 on every outcome.**

## Why this module exists

Q1P-0 computed the amended class's linear hull exactly: it is
**40-dimensional over ℚ**, not `span{1, conjU}` — the class
`RealCentralizingClass` is infinite (a 12-dimensional real
variety inside the hull), and the Q1P-2 finite-check road does
not open. Q1P-0 exhibited two explicit new members, in the
`(P, Q)` parametrization `U(P,Q)` of the hull:

* **M1 = U(R, 0)** — block-diagonal; in each 8-block the
  `(3/5, 4/5)` rotation on the local seat pair `(2, 4)`
  (seat pairs `(2,4), (10,12), (18,20), (26,28)`), fixing the
  other 24 seats.
* **M2 = U(0, Qswap)** — the off-block permutation: only the
  `(B0,B3), (B1,B2), (B2,B1), (B3,B0)` blocks are nonzero, each
  equal to `Qswap` (the local `2 ↔ 4` swap).

This module lands their membership in the amended class at T1
and runs the P-C sweep machinery (the pulled clauses of
`DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled`)
at the exhibited strengthened points against them. **One
pulled-clause failure at either member refutes
`PreservationQReal` at T1** — the pre-registered kill
**K-Q1-PRES-NEWU**. A clean sweep at a point is the
`PreservationQReal` instance at that pair and nothing more:
the class is infinite, and no finite sweep decides it.

## Brick map

Brick 1 (split along declaration seams, reported as such):
1a M1 tables/mates · 1b M1 products, unitarity, reality ·
1c M1 membership · 1d M2 machinery, unitarity, reality ·
1e M2 membership. Then one brick per sweep point:
(M1, pi1), (M1, piAnti), (M1, piU), (M2, pi1), (M2, piAnti),
(M2, piU) — stopping the moment a failure converts the
campaign into the refutation.

## Fences

NO CLAIM. Dial 1 = 0: a family-membership decision derives no
measured number. No `axiom` declarations; no sorrys; no
`native_decide`.
-/

/-! ## §1a. M1: the pair seat, the tables, the entry lemmas -/

/-- The within-block `2 ↔ 4` pair seat of M1: swaps the seat
pairs `(2,4), (10,12), (18,20), (26,28)` — the local `2 ↔ 4`
swap inside each 8-block — and fixes the other 24 seats. -/
def pairSeat (i : Fin 32) : Fin 32 :=
  if i.val = 2 then ⟨4, by norm_num⟩
  else if i.val = 4 then ⟨2, by norm_num⟩
  else if i.val = 10 then ⟨12, by norm_num⟩
  else if i.val = 12 then ⟨10, by norm_num⟩
  else if i.val = 18 then ⟨20, by norm_num⟩
  else if i.val = 20 then ⟨18, by norm_num⟩
  else if i.val = 26 then ⟨28, by norm_num⟩
  else if i.val = 28 then ⟨26, by norm_num⟩
  else i

/-- The diagonal table of M1: `3/5` on the eight rotated
seats, else `1`. -/
noncomputable def rotD (i : Fin 32) : ℂ :=
  if i.val = 2 ∨ i.val = 4 ∨ i.val = 10 ∨ i.val = 12
      ∨ i.val = 18 ∨ i.val = 20 ∨ i.val = 26 ∨ i.val = 28
    then ((3 / 5 : ℝ) : ℂ) else 1

/-- The pair table of M1: `M1 i (pairSeat i) = rotO i` —
`−4/5` at the local-2 seats `{2, 10, 18, 26}`, `+4/5` at the
local-4 seats `{4, 12, 20, 28}`, else `0`. -/
noncomputable def rotO (i : Fin 32) : ℂ :=
  if i.val = 2 ∨ i.val = 10 ∨ i.val = 18 ∨ i.val = 26
    then (-(4 / 5 : ℝ) : ℂ)
  else if i.val = 4 ∨ i.val = 12 ∨ i.val = 20 ∨ i.val = 28
    then ((4 / 5 : ℝ) : ℂ) else 0

/-- **M1 = U(R, 0)** of the Q1P-0 parametrization:
block-diagonal over the four 8-blocks; in each block the
`(3/5, 4/5)` rotation on the local seat pair `(2, 4)`,
fixing the other seats. -/
noncomputable def M1 : Matrix (Fin 32) (Fin 32) ℂ := fun i j =>
  if j = i then rotD i
  else if j = pairSeat i then rotO i
  else 0

theorem pairSeat_involutive (i : Fin 32) : pairSeat (pairSeat i) = i := by
  fin_cases i <;> rfl

theorem pairSeat_rotD (i : Fin 32) : rotD (pairSeat i) = rotD i := by
  fin_cases i <;> rfl

theorem pairSeat_rotO (i : Fin 32) : rotO (pairSeat i) = -rotO i := by
  fin_cases i <;> simp [pairSeat, rotO] <;> norm_num

/-- At a pair-fixed seat, M1 is the identity row:
`rotD = 1`, `rotO = 0`. -/
theorem pairSeat_eq_self_rot (i : Fin 32) (h : pairSeat i = i) :
    rotD i = 1 ∧ rotO i = 0 := by
  fin_cases i <;> simp_all [pairSeat, rotD, rotO]

theorem rotD_sq_add_rotO_sq (i : Fin 32) :
    rotD i * rotD i + rotO i * rotO i = 1 := by
  fin_cases i <;> simp [rotD, rotO] <;> norm_num

theorem M1_apply_diag (i : Fin 32) : M1 i i = rotD i := by
  unfold M1
  rw [if_pos rfl]

theorem M1_apply_pair (i : Fin 32) (h : pairSeat i ≠ i) :
    M1 i (pairSeat i) = rotO i := by
  unfold M1
  rw [if_neg h, if_pos rfl]

theorem M1_apply_of_ne (i k : Fin 32) (h1 : k ≠ i) (h2 : k ≠ pairSeat i) :
    M1 i k = 0 := by
  unfold M1
  rw [if_neg h1, if_neg h2]

theorem pairSeat_injective : Function.Injective pairSeat :=
  Function.Involutive.injective pairSeat_involutive

/-! ## §1b. M1: products, unitarity, reality -/

/-- `M1` times a matrix, entrywise — `conjU_mul_apply`'s
shape with the pair seat in place of the mate seat. -/
theorem M1_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M1 * M) i j
      = rotD i * M i j + rotO i * M (pairSeat i) j := by
  rw [Matrix.mul_apply]
  by_cases hm : pairSeat i = i
  · have hdc : rotD i = 1 ∧ rotO i = 0 := pairSeat_eq_self_rot i hm
    rw [Finset.sum_eq_single i]
    · simp [M1_apply_diag, hdc.1, hdc.2, hm]
    · intro k _ hk
      have hk2 : k ≠ pairSeat i := by rw [hm]; exact hk
      rw [M1_apply_of_ne i k hk hk2, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  · have hsum : (∑ k : Fin 32, M1 i k * M k j)
        = ∑ k ∈ ({i, pairSeat i} : Finset (Fin 32)), M1 i k * M k j :=
      (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        push_neg at hk
        rw [M1_apply_of_ne i k hk.1 hk.2, zero_mul])).symm
    rw [hsum, Finset.sum_insert (by rw [Finset.mem_singleton]; exact Ne.symm hm),
      Finset.sum_singleton, M1_apply_diag, M1_apply_pair i hm]

/-- A matrix times `M1`, entrywise — `mul_conjU_apply`'s
shape. -/
theorem mul_M1_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M * M1) i j
      = M i j * rotD j + M i (pairSeat j) * rotO (pairSeat j) := by
  rw [Matrix.mul_apply]
  by_cases hm : pairSeat j = j
  · have hdc : rotD j = 1 ∧ rotO j = 0 := pairSeat_eq_self_rot j hm
    rw [Finset.sum_eq_single j]
    · rw [hm, M1_apply_diag, hdc.1, hdc.2]
      simp
    · intro k _ hk
      have hkj : M1 k j = 0 := by
        apply M1_apply_of_ne k j (Ne.symm hk)
        intro hcon
        have h2 : pairSeat j = k := by
          have h3 : pairSeat j = pairSeat (pairSeat k) := congrArg pairSeat hcon
          rwa [pairSeat_involutive] at h3
        rw [hm] at h2
        exact hk h2.symm
      rw [hkj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  · have hsum : (∑ k : Fin 32, M i k * M1 k j)
        = ∑ k ∈ ({j, pairSeat j} : Finset (Fin 32)), M i k * M1 k j :=
      (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        push_neg at hk
        have hkj : M1 k j = 0 := by
          apply M1_apply_of_ne k j (Ne.symm hk.1)
          intro hcon
          have h2 : pairSeat j = k := by
            have h3 : pairSeat j = pairSeat (pairSeat k) :=
              congrArg pairSeat hcon
            rwa [pairSeat_involutive] at h3
          exact hk.2 h2.symm
        rw [hkj, mul_zero])).symm
    rw [hsum, Finset.sum_insert (by rw [Finset.mem_singleton]; exact Ne.symm hm),
      Finset.sum_singleton, M1_apply_diag]
    have hmj : M1 (pairSeat j) j = rotO (pairSeat j) := by
      unfold M1
      rw [if_neg (Ne.symm hm), if_pos (pairSeat_involutive j).symm]
    rw [hmj]

/-- `M1ᵀ` at a pair seat: the transpose carries the pair
table of the paired seat. -/
theorem M1_transpose_pair (i : Fin 32) (h : pairSeat i ≠ i) :
    M1ᵀ i (pairSeat i) = rotO (pairSeat i) := by
  rw [Matrix.transpose_apply]
  unfold M1
  rw [if_neg (Ne.symm h), if_pos (pairSeat_involutive i).symm]

/-- `M1ᵀ` off the diagonal and the pair: zero. -/
theorem M1_transpose_of_ne (i j : Fin 32) (h1 : j ≠ i)
    (h2 : j ≠ pairSeat i) :
    M1ᵀ i j = 0 := by
  rw [Matrix.transpose_apply]
  apply M1_apply_of_ne j i (Ne.symm h1)
  intro hcon
  have h3 : pairSeat i = pairSeat (pairSeat j) := congrArg pairSeat hcon
  rw [pairSeat_involutive] at h3
  exact h2 h3.symm

/-- **M1 is transpose-unitary, left form.** -/
theorem M1_mul_transpose : M1 * M1ᵀ = 1 := by
  ext i j
  rw [M1_mul_apply]
  by_cases hij : j = i
  · rw [← hij, Matrix.transpose_apply, M1_apply_diag, Matrix.one_apply_eq]
    by_cases hm : pairSeat j = j
    · have hdc := pairSeat_eq_self_rot j hm
      rw [Matrix.transpose_apply, hm, M1_apply_diag, hdc.1, hdc.2]
      norm_num
    · rw [Matrix.transpose_apply, M1_apply_pair j hm]
      exact rotD_sq_add_rotO_sq j
  · by_cases hjm : j = pairSeat i
    · subst hjm
      have hm : pairSeat i ≠ i := hij
      rw [Matrix.one_apply_ne (Ne.symm hm), M1_transpose_pair i hm,
        Matrix.transpose_apply, M1_apply_diag, pairSeat_rotD,
        pairSeat_rotO]
      ring
    · rw [Matrix.one_apply_ne (Ne.symm hij), M1_transpose_of_ne i j hij hjm]
      have h3 : M1ᵀ (pairSeat i) j = 0 := by
        apply M1_transpose_of_ne (pairSeat i) j hjm
        intro hcon
        have h4 : pairSeat j = pairSeat i := by
          have h5 : pairSeat j = pairSeat (pairSeat (pairSeat i)) :=
            congrArg pairSeat hcon
          rwa [pairSeat_involutive] at h5
        exact hij (pairSeat_injective h4)
      rw [h3]
      ring

/-- **M1 is transpose-unitary, right form.** -/
theorem M1_transpose_mul : M1ᵀ * M1 = 1 := by
  have h := M1_mul_transpose
  rwa [mul_eq_one_comm] at h

theorem star_rotD (i : Fin 32) : star (rotD i) = rotD i := by
  unfold rotD
  split_ifs <;> simp

theorem star_rotO (i : Fin 32) : star (rotO i) = rotO i := by
  unfold rotO
  split_ifs <;> simp

/-- **M1 is real**: `M1ᴴ = M1ᵀ`, entrywise — the
`IsRealMat` clause of the amended class. -/
theorem M1_conjTranspose : M1ᴴ = M1ᵀ := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  by_cases h1 : i = j
  · rw [h1, M1_apply_diag, star_rotD]
  · by_cases h2 : i = pairSeat j
    · have hval : M1 j i = rotO j := by
        unfold M1
        rw [if_neg h1, if_pos h2]
      rw [hval, star_rotO]
    · rw [M1_apply_of_ne j i h1 h2]
      simp

/-! ## §1c. M1: membership in the amended class -/

/-- The pair seat commutes with the partner seat: the two
act on independent coordinates (block vs within-block). -/
theorem pairSeat_partner (i : Fin 32) :
    pairSeat (partner i) = partner (pairSeat i) := by
  fin_cases i <;> rfl

theorem partner_rotD (i : Fin 32) : rotD (partner i) = rotD i := by
  fin_cases i <;> rfl

theorem partner_rotO (i : Fin 32) : rotO (partner i) = rotO i := by
  fin_cases i <;> rfl

/-- Clause (b) for M1: `piOp M1 = M1ᵀ` — the
`piOp_conjU` proof with the pair seat in place of the
mate seat; the partner seat preserves the tables and
commutes with the pair seat. -/
theorem piOp_M1 : piOp M1 = M1ᵀ := by
  ext i j
  rw [piOp_apply, Matrix.transpose_apply]
  by_cases hij : j = i
  · subst hij
    rw [M1_apply_diag, M1_apply_diag, partner_rotD]
  · by_cases hjm : j = pairSeat i
    · subst hjm
      have hpi : partner i ≠ partner (pairSeat i) := by
        intro hcon
        have h3 := congrArg partner hcon
        rw [partner_involutive, partner_involutive] at h3
        exact hij h3.symm
      have hmate : partner i = pairSeat (partner (pairSeat i)) := by
        rw [pairSeat_partner, pairSeat_involutive]
      have hL : M1 (partner (pairSeat i)) (partner i)
          = rotO (partner (pairSeat i)) := by
        conv_lhs => rw [hmate]
        exact M1_apply_pair _ (by rw [← hmate]; exact hpi)
      have hR : M1 (pairSeat i) i = rotO (pairSeat i) := by
        have h := M1_transpose_pair i hij
        rwa [Matrix.transpose_apply] at h
      rw [hL, hR, partner_rotO]
    · have h1 : M1 (partner j) (partner i) = 0 := by
        apply M1_apply_of_ne
        · intro hcon
          exact hij (Function.Involutive.injective partner_involutive hcon.symm)
        · intro hcon
          apply hjm
          have h3 : i = pairSeat j := by
            have h4 : partner i = partner (pairSeat j) := by
              rw [hcon, pairSeat_partner]
            exact Function.Involutive.injective partner_involutive h4
          have h5 : pairSeat i = j := by
            have h6 : pairSeat i = pairSeat (pairSeat j) :=
              congrArg pairSeat h3
            rwa [pairSeat_involutive] at h6
          exact h5.symm
      have hne2 : i ≠ pairSeat j := by
        intro hh
        have h3 : pairSeat i = pairSeat (pairSeat j) := congrArg pairSeat hh
        rw [pairSeat_involutive] at h3
        exact hjm h3.symm
      rw [h1, M1_apply_of_ne j i (Ne.symm hij) hne2]

/-- `gammaF` is constant on pair seats (the pair is
within-block; `gammaF` is blockwise). -/
theorem gammaF_pairSeat (i : Fin 32) :
    gammaF (pairSeat i) (pairSeat i) = gammaF i i := by
  fin_cases i <;> rfl

/-- Clause (a) for M1: `gammaF * M1 = M1 * gammaF`. -/
theorem M1_gamma_comm : gammaF * M1 = M1 * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : j = i
  · rw [h1]; ring
  · by_cases h2 : j = pairSeat i
    · rw [h2, gammaF_pairSeat]; ring
    · rw [M1_apply_of_ne i j h1 h2]; simp

/-- Clause (c) for M1: M1 commutes with `DF_oneGen` at
all real Yukawas — the `conjU_df_comm` proof with the
pair seat in place of the mate seat. The load-bearing
facts: the pair seat commutes with `dparSeat`, both
tables are `dparSeat`-invariant, and `dcoef` is
pair-invariant (the swap is inside the `u` type class:
local seats 2 and 4 both carry `Yu`). -/
theorem M1_df_comm (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd * M1 = M1 * DF_oneGen Ynu Ye Yu Yd := by
  have hps : ∀ i : Fin 32, pairSeat (dparSeat i) = dparSeat (pairSeat i) :=
    fun i => by fin_cases i <;> rfl
  have hrotD : ∀ i : Fin 32, rotD (dparSeat i) = rotD i :=
    fun i => by fin_cases i <;> rfl
  have hrotO : ∀ i : Fin 32, rotO (dparSeat i) = rotO i :=
    fun i => by fin_cases i <;> rfl
  have hdcoef : ∀ i : Fin 32,
      dcoef Ynu Ye Yu Yd (pairSeat i) = dcoef Ynu Ye Yu Yd i :=
    fun i => by fin_cases i <;> rfl
  ext i j
  rw [mul_M1_apply, M1_mul_apply]
  have hC : (j = dparSeat (pairSeat i)) ↔ (pairSeat j = dparSeat i) := by
    constructor
    · intro hh
      have h2 : pairSeat j = pairSeat (dparSeat (pairSeat i)) :=
        congrArg pairSeat hh
      rwa [hps, pairSeat_involutive] at h2
    · intro hh
      have h2 : pairSeat (pairSeat j) = pairSeat (dparSeat i) :=
        congrArg pairSeat hh
      rwa [pairSeat_involutive, hps] at h2
  by_cases hA : j = dparSeat i
  · by_cases hB : pairSeat j = dparSeat i
    · have hdj : rotD j = rotD i := by rw [hA]; exact hrotD i
      have hpoj : pairSeat j = j := by rw [hB, ← hA]
      have hoc : rotO (pairSeat j) = rotO i := by
        rw [hpoj, hA]; exact hrotO i
      have hdc : dcoef Ynu Ye Yu Yd (pairSeat i) = dcoef Ynu Ye Yu Yd i :=
        hdcoef i
      rw [df_entry, if_pos hA, df_entry, if_pos hB, df_entry,
        if_pos (hC.mpr hB), hdj, hoc, hdc]
      ring
    · have hdj : rotD j = rotD i := by rw [hA]; exact hrotD i
      rw [df_entry, if_pos hA, df_entry, if_neg hB, df_entry,
        if_neg (fun hh => hB (hC.mp hh)), hdj]
      ring
  · by_cases hB : pairSeat j = dparSeat i
    · have hoc : rotO (pairSeat j) = rotO i := by
        rw [hB]; exact hrotO i
      have hdc : dcoef Ynu Ye Yu Yd (pairSeat i) = dcoef Ynu Ye Yu Yd i :=
        hdcoef i
      rw [df_entry, if_neg hA, df_entry, if_pos hB, df_entry,
        if_pos (hC.mpr hB), hoc, hdc]
      ring
    · rw [df_entry, if_neg hA, df_entry, if_neg hB, df_entry,
        if_neg (fun hh => hB (hC.mp hh))]
      ring

/-- **M1 belongs to the centralizing class** — assembled
from the landed components: transpose-unitarity (§1b),
(a) `M1_gamma_comm`, (b) `piOp_M1`, (c) `M1_df_comm`. -/
theorem M1_centralizing : CentralizingClass M1 :=
  ⟨M1_mul_transpose, M1_transpose_mul, M1_gamma_comm, piOp_M1,
   fun Ynu Ye Yu Yd => M1_df_comm Ynu Ye Yu Yd⟩

/-- **M1 belongs to the AMENDED class** — the first new
member of `RealCentralizingClass` landed since `conjU`:
the Q1P-0 probe's M1, now at T1. -/
theorem M1_realCentralizing :
    ThetLogos.DialOneGradeRConjAmend.RealCentralizingClass M1 :=
  ⟨M1_centralizing, M1_conjTranspose⟩

/-! ## §1d. M2: the seat involution, products, unitarity, reality -/

/-- The local `2 ↔ 4` swap on seat indices. -/
def swap24 (l : ℕ) : ℕ := if l = 2 then 4 else if l = 4 then 2 else l

/-- The M2 seat involution: block `r ↦ 3 − r` with the
local `2 ↔ 4` swap — row `i` of M2 carries its single `1`
at column `m2Seat i`. -/
def m2Seat (i : Fin 32) : Fin 32 :=
  ⟨(3 - i.val / 8) * 8 + swap24 (i.val % 8), by
    have h := i.isLt
    have h1 : i.val / 8 ≤ 3 := by omega
    have h2 : swap24 (i.val % 8) ≤ 7 := by
      unfold swap24; split_ifs <;> omega
    omega⟩

/-- **M2 = U(0, Qswap)** of the Q1P-0 parametrization: the
permutation matrix of `m2Seat` — only the blocks
`(B0,B3), (B1,B2), (B2,B1), (B3,B0)` are nonzero, each
equal to `Qswap`. -/
def M2 : Matrix (Fin 32) (Fin 32) ℂ := fun i j =>
  if j = m2Seat i then 1 else 0

theorem m2Seat_involutive (i : Fin 32) : m2Seat (m2Seat i) = i := by
  fin_cases i <;> rfl

theorem m2Seat_injective : Function.Injective m2Seat :=
  Function.Involutive.injective m2Seat_involutive

/-- `M2` times a matrix, entrywise: a permutation action
on rows. -/
theorem M2_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M2 * M) i j = M (m2Seat i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (m2Seat i)]
  · unfold M2; rw [if_pos rfl, one_mul]
  · intro k _ hk
    unfold M2
    rw [if_neg hk, zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ (m2Seat i)) hcon

/-- A matrix times `M2`, entrywise: a permutation action
on columns (the involution makes the column form
symmetric). -/
theorem mul_M2_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M * M2) i j = M i (m2Seat j) := by
  have hkey : ∀ k : Fin 32, M2 k j = if k = m2Seat j then 1 else 0 := by
    intro k
    unfold M2
    by_cases h : j = m2Seat k
    · have hk : k = m2Seat j := by
        have h3 : m2Seat j = m2Seat (m2Seat k) := congrArg m2Seat h
        rw [m2Seat_involutive] at h3
        exact h3.symm
      rw [if_pos h, if_pos hk]
    · have hk : k ≠ m2Seat j := by
        intro hcon
        apply h
        rw [hcon, m2Seat_involutive]
      rw [if_neg h, if_neg hk]
  rw [Matrix.mul_apply]
  simp only [hkey]
  rw [Finset.sum_eq_single (m2Seat j)]
  · rw [if_pos rfl, mul_one]
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ (m2Seat j)) hcon

/-- **M2 is transpose-unitary, left form** (a permutation
matrix of an involution). -/
theorem M2_mul_transpose : M2 * M2ᵀ = 1 := by
  ext i j
  rw [M2_mul_apply, Matrix.transpose_apply]
  by_cases hij : i = j
  · rw [hij, Matrix.one_apply_eq]
    unfold M2; rw [if_pos rfl]
  · rw [Matrix.one_apply_ne hij]
    unfold M2
    rw [if_neg (fun h => hij (m2Seat_injective h))]

/-- **M2 is transpose-unitary, right form.** -/
theorem M2_transpose_mul : M2ᵀ * M2 = 1 := by
  have h := M2_mul_transpose
  rwa [mul_eq_one_comm] at h

/-- **M2 is real**: entries in `{0, 1}`, so
`M2ᴴ = M2ᵀ` entrywise. -/
theorem M2_conjTranspose : M2ᴴ = M2ᵀ := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  unfold M2
  split_ifs <;> simp

/-! ## §1e. M2: membership in the amended class -/

/-- `gammaF` is constant on M2 seats: the block map
`r ↦ 3 − r` preserves the `gammaF` sign pattern
`(+1, −1, −1, +1)`, and the local swap is within-block. -/
theorem gammaF_m2Seat (i : Fin 32) :
    gammaF (m2Seat i) (m2Seat i) = gammaF i i := by
  fin_cases i <;> rfl

/-- Clause (a) for M2: `gammaF * M2 = M2 * gammaF`. -/
theorem M2_gamma_comm : gammaF * M2 = M2 * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : j = m2Seat i
  · rw [h, gammaF_m2Seat]; ring
  · unfold M2; rw [if_neg h]; simp

/-- The M2 seat commutes with the partner seat (block
vs local/partner coordinates are independent). -/
theorem m2Seat_partner (i : Fin 32) :
    m2Seat (partner i) = partner (m2Seat i) := by
  fin_cases i <;> rfl

/-- Clause (b) for M2: `piOp M2 = M2ᵀ` — the partner
seat commutes with the M2 seat, so the partner-reflected
permutation is its own transpose. -/
theorem piOp_M2 : piOp M2 = M2ᵀ := by
  ext i j
  rw [piOp_apply, Matrix.transpose_apply]
  by_cases h : i = m2Seat j
  · have h2 : partner i = m2Seat (partner j) := by
      rw [m2Seat_partner, h]
    unfold M2
    rw [if_pos h, if_pos h2]
  · have h2 : partner i ≠ m2Seat (partner j) := by
      intro hcon
      apply h
      have h3 : partner i = partner (m2Seat j) := by
        rwa [m2Seat_partner] at hcon
      exact Function.Involutive.injective partner_involutive h3
    unfold M2
    rw [if_neg h, if_neg h2]

/-- Clause (c) for M2: M2 commutes with `DF_oneGen` at
all real Yukawas. The load-bearing facts: `dparSeat`
commutes with the M2 seat (block maps `r ↦ 3 − r` and
`r ↦ r ± 1` commute; both preserve the local seat up to
the same swap), and `dcoef` is M2-invariant (the local
swap sits inside the `u` type class). -/
theorem M2_df_comm (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd * M2 = M2 * DF_oneGen Ynu Ye Yu Yd := by
  have hcomm : ∀ i : Fin 32, dparSeat (m2Seat i) = m2Seat (dparSeat i) :=
    fun i => by fin_cases i <;> rfl
  have hdcoef : ∀ i : Fin 32,
      dcoef Ynu Ye Yu Yd (m2Seat i) = dcoef Ynu Ye Yu Yd i :=
    fun i => by fin_cases i <;> rfl
  ext i j
  rw [mul_M2_apply, M2_mul_apply, df_entry, df_entry]
  by_cases h : m2Seat j = dparSeat i
  · have h2 : j = dparSeat (m2Seat i) := by
      rw [hcomm]
      have h3 : m2Seat (m2Seat j) = m2Seat (dparSeat i) :=
        congrArg m2Seat h
      rwa [m2Seat_involutive] at h3
    rw [if_pos h, if_pos h2, hdcoef]
  · have h2 : j ≠ dparSeat (m2Seat i) := by
      intro hh
      apply h
      rw [hcomm] at hh
      have h3 : m2Seat j = m2Seat (m2Seat (dparSeat i)) :=
        congrArg m2Seat hh
      rwa [m2Seat_involutive] at h3
    rw [if_neg h, if_neg h2]

/-- **M2 belongs to the centralizing class** — assembled
from the landed components. -/
theorem M2_centralizing : CentralizingClass M2 :=
  ⟨M2_mul_transpose, M2_transpose_mul, M2_gamma_comm, piOp_M2,
   fun Ynu Ye Yu Yd => M2_df_comm Ynu Ye Yu Yd⟩

/-- **M2 belongs to the AMENDED class** — the Q1P-0
probe's second new member, now at T1. Its sweep verdict
is a separate question (the pi1 brick): membership is
what turns a pulled-clause failure at M2 into a
refutation of `PreservationQReal`. -/
theorem M2_realCentralizing :
    ThetLogos.DialOneGradeRConjAmend.RealCentralizingClass M2 :=
  ⟨M2_centralizing, M2_conjTranspose⟩

/-! ## §2a. The (M1, pi1) pulled machinery: diagonal formula and ℤ shadow -/

/-- `M1ᵀ` times a matrix, entrywise — the transpose
trick of `conjUT_mul_apply` with the pair tables. -/
theorem M1T_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M1ᵀ * M) i j
      = rotD i * M i j + rotO (pairSeat i) * M (pairSeat i) j := by
  have h : (M1ᵀ * M) i j = (Mᵀ * M1) j i := by
    have e : (Mᵀ * M1)ᵀ = M1ᵀ * M := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← e]
    rfl
  rw [h, mul_M1_apply]
  simp only [Matrix.transpose_apply]
  ring

/-- The diagonal of an M1-conjugated diagonal matrix:
the `rotD²`/`rotO²` mixture at the seat and its pair —
`conjT_diag_conjU_diag`'s shape. -/
theorem M1T_diag_M1_diag (d : Fin 32 → ℂ) (i : Fin 32) :
    (M1ᵀ * Matrix.diagonal d * M1) i i
      = rotD i * rotD i * d i
        + rotO (pairSeat i) * rotO (pairSeat i) * d (pairSeat i) := by
  rw [Matrix.mul_assoc, M1T_mul_apply, mul_M1_apply, mul_M1_apply]
  by_cases hm : pairSeat i = i
  · have hdc := pairSeat_eq_self_rot i hm
    rw [hm, hdc.1, hdc.2]
    simp only [Matrix.diagonal_apply_eq]
    ring
  · rw [Matrix.diagonal_apply_ne _
      (fun hh : i = pairSeat i => hm hh.symm),
      Matrix.diagonal_apply_ne _ hm]
    simp only [Matrix.diagonal_apply_eq]
    ring

/-- The ℤ shadow of `rotD` at denominator 5: `3` on the
rotated seats (local 2/4), else `5`. -/
def rotDZ (i : Fin 32) : ℤ :=
  if i.val % 8 = 2 ∨ i.val % 8 = 4 then 3 else 5

/-- The ℤ shadow of `rotO` at denominator 5: `−4` at
local-2 seats, `+4` at local-4 seats, else `0`. -/
def rotOZ (i : Fin 32) : ℤ :=
  if i.val % 8 = 2 then -4 else if i.val % 8 = 4 then 4 else 0

/-- The γ-weighted pulled weight of M1 at seat `i`, as an
integer at denominator `25` — `dpWZ`'s analogue for the
pair pull. -/
def pulWZ (ind : ℕ → ℤ) (i : Fin 32) : ℤ :=
  gammaVal i.val * (rotDZ i * rotDZ i * ind i.val
    + rotOZ (pairSeat i) * rotOZ (pairSeat i) * ind (pairSeat i).val)

theorem rotD_eq (i : Fin 32) : rotD i = ((rotDZ i : ℂ) / 5) := by
  fin_cases i <;> simp [rotD, rotDZ] <;> norm_num

theorem rotO_eq (i : Fin 32) : rotO i = ((rotOZ i : ℂ) / 5) := by
  fin_cases i <;> simp [rotO, rotOZ] <;> norm_num

/-- **The M1-pulled diagonal of a projector, entrywise:**
the `(gammaF * (M1ᵀ * P * M1))` diagonal is the integer
shadow `pulWZ ind s` over `25`. -/
theorem pulled_diag_M1 (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (s : Fin 32) :
    (gammaF * (M1ᵀ * P * M1)) s s
      = ((pulWZ ind s : ℤ) : ℂ) / 25 := by
  rw [ThetLogos.DialOnePresSweep.gammaF_mul_entry_diag, hP,
    M1T_diag_M1_diag, rotD_eq, rotO_eq (pairSeat s)]
  unfold pulWZ
  push_cast
  ring

/-! ## §2b. The (M1, pi1) shadow sums and the pulled trace -/

/-- The γ-weighted A-shadow sum of the M1-pulled lepton
indicator vanishes — the integer content of the pulled
lep clause at (M1, pi1). -/
theorem pulWZ_sum_A_lep :
    ∑ i : Fin 32, pulWZ lepInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the M1-pulled lepton
indicator vanishes. -/
theorem pulWZ_sum_B_lep :
    ∑ i : Fin 32, pulWZ lepInd i * pi1BVal i.val = 0 := by decide

/-- The γ-weighted A-shadow sum of the M1-pulled colour
indicator vanishes, at every colour. -/
theorem pulWZ_sum_A_col (c : Fin 3) :
    ∑ i : Fin 32, pulWZ (colInd c) i * pi1AVal i.val = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted B-shadow sum of the M1-pulled colour
indicator vanishes, at every colour. -/
theorem pulWZ_sum_B_col (c : Fin 3) :
    ∑ i : Fin 32, pulWZ (colInd c) i * pi1BVal i.val = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted A-shadow sum of the M1-pulled `e_R`
indicator vanishes. -/
theorem pulWZ_sum_A_eR :
    ∑ i : Fin 32, pulWZ eRInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the M1-pulled `e_R`
indicator vanishes. -/
theorem pulWZ_sum_B_eR :
    ∑ i : Fin 32, pulWZ eRInd i * pi1BVal i.val = 0 := by decide

/-- **The pulled trace at (M1, pi1) vanishes** whenever
the two shadow sums do — the `pulled_trace_piU` closing
pattern run directly on `pi1`'s diagonal form. -/
theorem pulled_trace_M1_pi1 (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (hA : ∑ i : Fin 32, pulWZ ind i * pi1AVal i.val = 0)
    (hB : ∑ i : Fin 32, pulWZ ind i * pi1BVal i.val = 0)
    (α β : ℤ) :
    Matrix.trace (gammaF * (M1ᵀ * P * M1) * pi1 (u1Gen α β))
      = 0 := by
  rw [ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal,
    ThetLogos.DialOnePiUFamily.trace_mul_diagonal]
  have hterm : ∀ i : Fin 32,
      (gammaF * (M1ᵀ * P * M1)) i i
          * (Complex.I
            * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ))
        = Complex.I / 25
          * ((pulWZ ind i
              * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [pulled_diag_M1 P ind hP]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, pulWZ ind i
        * (pi1AVal i.val * α + pi1BVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, pulWZ ind i
          * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (pulWZ ind i * pi1AVal i.val) * α
          + (pulWZ ind i * pi1BVal i.val) * β :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      hA, hB]
    simp
  rw [hsum]
  simp

/-! ## §2c. The pulled clauses at (M1, pi1) and the capstone instance -/

/-- **The pulled lepton clause at (M1, pi1) — PROVED**
(hypothesis `hlep` of the amended capstone at this
pair). -/
theorem pulled_lep_M1_pi1 :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M1ᵀ * lepProj * M1)
        * pi1 (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_M1_pi1 lepProj lepInd
    ThetLogos.DialOnePiUFamily.lepProj_eq_diag
    pulWZ_sum_A_lep pulWZ_sum_B_lep α β

/-- **The pulled colour clause at (M1, pi1) — PROVED**
(the capstone's `hcol` at this pair). -/
theorem pulled_col_M1_pi1 :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (M1ᵀ * colProj c * M1)
        * pi1 (u1Gen α β)) = 0 :=
  fun c α β => pulled_trace_M1_pi1 (colProj c) (colInd c)
    (ThetLogos.DialOnePiUFamily.colProj_eq_diag c)
    (pulWZ_sum_A_col c) (pulWZ_sum_B_col c) α β

/-- **The pulled e_R clause at (M1, pi1) — PROVED**
(the capstone's `heR` at this pair). -/
theorem pulled_eR_M1_pi1 :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M1ᵀ * eRProj * M1)
        * pi1 (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_M1_pi1 eRProj eRInd
    ThetLogos.DialOnePiUFamily.eRProj_eq_diag
    pulWZ_sum_A_eR pulWZ_sum_B_eR α β

/-- **Preservation at the pair (M1, pi1)** — the amended
capstone fires with M1's amended membership (§1c),
`pi1`'s landed strengthened membership, and the three
pulled clauses above. The `PreservationQReal` instance
at this pair; the class-level statement remains open
(the class is infinite). -/
theorem strengthened_conjRep_M1_pi1 :
    DialOneStrengthenedFam (conjRep M1 pi1) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    M1_realCentralizing pi1
    ThetLogos.DialOneGammaFamilyChecks.strengthened_pi1
    pulled_lep_M1_pi1 pulled_col_M1_pi1 pulled_eR_M1_pi1

/-! ## §3. The sweep point (M1, piAnti): the flip -/

/-- **The pulled lepton clause at (M1, piAnti) —
PROVED**: `piAnti` at `(α, β)` is `pi1` at `(α, −β)`
(`piAnti_flip_u1Gen`), so the (M1, pi1) clause at the
flipped direction closes it. -/
theorem pulled_lep_M1_piAnti :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M1ᵀ * lepProj * M1)
        * piAnti (u1Gen α β)) = 0 := by
  intro α β
  rw [ThetLogos.DialOnePiAntiPackage.piAnti_flip_u1Gen]
  exact pulled_lep_M1_pi1 α (-β)

/-- **The pulled colour clause at (M1, piAnti) —
PROVED**, same flip. -/
theorem pulled_col_M1_piAnti :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (M1ᵀ * colProj c * M1)
        * piAnti (u1Gen α β)) = 0 := by
  intro c α β
  rw [ThetLogos.DialOnePiAntiPackage.piAnti_flip_u1Gen]
  exact pulled_col_M1_pi1 c α (-β)

/-- **The pulled e_R clause at (M1, piAnti) — PROVED**,
same flip. -/
theorem pulled_eR_M1_piAnti :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M1ᵀ * eRProj * M1)
        * piAnti (u1Gen α β)) = 0 := by
  intro α β
  rw [ThetLogos.DialOnePiAntiPackage.piAnti_flip_u1Gen]
  exact pulled_eR_M1_pi1 α (-β)

/-- **Preservation at the pair (M1, piAnti)** — the
amended capstone fires with M1's membership, `piAnti`'s
landed strengthened membership
(`DialOneAntiparticleBase.strengthenedFam_piAnti`), and
the three flipped clauses. The `PreservationQReal`
instance at this pair. -/
theorem strengthened_conjRep_M1_piAnti :
    DialOneStrengthenedFam (conjRep M1 piAnti) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    M1_realCentralizing piAnti
    ThetLogos.DialOneAntiparticleBase.strengthenedFam_piAnti
    pulled_lep_M1_piAnti pulled_col_M1_piAnti pulled_eR_M1_piAnti

/-! ## §4a. The (M1, piU) double pull: the Y-diagonal and its shadow -/

/-- At a mate-moved seat, the pair seat never reaches
the mate seat: `pairSeat` stays inside the 8-block,
`mateSeat` leaves it. (At mate-fixed seats both fix the
seat and the claim is false — the hypothesis is the
true form.) -/
theorem pairSeat_ne_mateSeat (a : Fin 32) (h : mateSeat a ≠ a) :
    pairSeat a ≠ mateSeat a := by
  fin_cases a <;> simp_all [pairSeat, mateSeat]

/-- At a mate-moved seat, the pair of the mate is never
the seat itself, same block reason. -/
theorem pairSeat_mateSeat_ne (a : Fin 32) (h : mateSeat a ≠ a) :
    pairSeat (mateSeat a) ≠ a := by
  fin_cases a <;> simp_all [pairSeat, mateSeat]

/-- The M1-conjugated diagonal has zero entries at the
mate pair: M1 is block-diagonal and the mate seat is in
another block. -/
theorem M1T_diag_M1_mate_off (d : Fin 32 → ℂ) (a : Fin 32)
    (h : mateSeat a ≠ a) :
    (M1ᵀ * Matrix.diagonal d * M1) a (mateSeat a) = 0
    ∧ (M1ᵀ * Matrix.diagonal d * M1) (mateSeat a) a = 0 := by
  constructor
  · rw [Matrix.mul_assoc, M1T_mul_apply, Matrix.diagonal_mul,
      Matrix.diagonal_mul,
      M1_apply_of_ne a (mateSeat a) h (Ne.symm (pairSeat_ne_mateSeat a h)),
      M1_apply_of_ne (pairSeat a) (mateSeat a)
        (Ne.symm (pairSeat_ne_mateSeat a h))
        (by rw [pairSeat_involutive]; exact h)]
    simp
  · rw [Matrix.mul_assoc, M1T_mul_apply, Matrix.diagonal_mul,
      Matrix.diagonal_mul,
      M1_apply_of_ne (mateSeat a) a (Ne.symm h)
        (Ne.symm (pairSeat_mateSeat_ne a h)),
      M1_apply_of_ne (pairSeat (mateSeat a)) a
        (Ne.symm (pairSeat_mateSeat_ne a h))
        (by rw [pairSeat_involutive]; exact Ne.symm h)]
    simp

/-- **The Y-diagonal for the piU pull at M1**: with
`W = gammaF * (M1ᵀ * P * M1)`, the diagonal of
`conjUᵀ * W * conjU` is the `diagC²`/`offC²` mixture of
`W`'s diagonal at the seat and its mate — the cross
terms vanish because `W` is block-diagonal
(`M1T_diag_M1_mate_off`) and `offC` vanishes at
mate-fixed seats. -/
theorem conjT_gammaM1_conjU_diag (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (i : Fin 32) :
    (conjUᵀ * (gammaF * (M1ᵀ * P * M1)) * conjU) i i
      = diagC i * diagC i * (gammaF * (M1ᵀ * P * M1)) i i
        + offC (mateSeat i) * offC (mateSeat i)
          * (gammaF * (M1ᵀ * P * M1)) (mateSeat i) (mateSeat i) := by
  have e1 : (conjUᵀ * (gammaF * (M1ᵀ * P * M1)) * conjU) i i
      = (conjUᵀ * (gammaF * (M1ᵀ * P * M1))) i i * diagC i
        + (conjUᵀ * (gammaF * (M1ᵀ * P * M1))) i (mateSeat i)
          * offC (mateSeat i) :=
    mul_conjU_apply _ _ _
  rw [e1, ThetLogos.DialOnePiUFamily.conjUT_mul_apply,
    ThetLogos.DialOnePiUFamily.conjUT_mul_apply]
  by_cases hm : mateSeat i = i
  · have hdc := mateSeat_eq_self_diagC i hm
    rw [hm, hdc.2]
    ring
  · have hX := M1T_diag_M1_mate_off (fun i => (ind i.val : ℂ)) i hm
    have hW1 : (gammaF * (M1ᵀ * P * M1)) i (mateSeat i) = 0 := by
      rw [gammaF_mul_apply, hP, hX.1, mul_zero]
    have hW2 : (gammaF * (M1ᵀ * P * M1)) (mateSeat i) i = 0 := by
      rw [gammaF_mul_apply, hP, hX.2, mul_zero]
    rw [hW1, hW2]
    ring

/-- The ℤ shadow of `offC` at denominator 5: `+4` at
local-2 seats, `−4` at local-4 seats, else `0` (the
signs are `offC`'s own; only its square enters the
double pull). -/
def offCZ (i : Fin 32) : ℤ :=
  if i.val % 8 = 2 then 4 else if i.val % 8 = 4 then -4 else 0

/-- `diagC`'s table is `rotD`'s table, so its ℤ shadow
at denominator 5 is `rotDZ`. -/
theorem diagC_eq (i : Fin 32) : diagC i = ((rotDZ i : ℂ) / 5) := by
  fin_cases i <;> simp [diagC, rotDZ] <;> norm_num

theorem offC_eq (i : Fin 32) : offC i = ((offCZ i : ℂ) / 5) := by
  fin_cases i <;> simp [offC, offCZ] <;> norm_num

/-- The double-pulled γ-weighted weight at (M1, piU),
as an integer shadow at denominator `625`: the
`diagC²`-weighted M1-pull at the seat plus the
`offC²`-weighted M1-pull at its mate. -/
def dpulWZ (ind : ℕ → ℤ) (i : Fin 32) : ℤ :=
  rotDZ i * rotDZ i * pulWZ ind i
    + offCZ (mateSeat i) * offCZ (mateSeat i) * pulWZ ind (mateSeat i)

/-- **The double-pulled diagonal at (M1, piU)** is the
shadow weight `dpulWZ ind s / 625` in `ℂ`. -/
theorem pulled_diag_M1_piU (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (s : Fin 32) :
    (conjUᵀ * (gammaF * (M1ᵀ * P * M1)) * conjU) s s
      = ((dpulWZ ind s : ℤ) : ℂ) / 625 := by
  rw [conjT_gammaM1_conjU_diag P ind hP, pulled_diag_M1 P ind hP s,
    pulled_diag_M1 P ind hP (mateSeat s), diagC_eq,
    offC_eq (mateSeat s)]
  unfold dpulWZ
  push_cast
  ring

/-! ## §4b. The (M1, piU) shadow sums and the pulled trace -/

/-- The γ-weighted A-shadow sum of the double-pulled
(M1, piU) lepton weights vanishes. -/
theorem dpulWZ_sum_A_lep :
    ∑ i : Fin 32, dpulWZ lepInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the double-pulled
(M1, piU) lepton weights vanishes. -/
theorem dpulWZ_sum_B_lep :
    ∑ i : Fin 32, dpulWZ lepInd i * pi1BVal i.val = 0 := by decide

/-- The γ-weighted A-shadow sum of the double-pulled
(M1, piU) colour weights vanishes, at every colour. -/
theorem dpulWZ_sum_A_col (c : Fin 3) :
    ∑ i : Fin 32, dpulWZ (colInd c) i * pi1AVal i.val = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted B-shadow sum of the double-pulled
(M1, piU) colour weights vanishes, at every colour. -/
theorem dpulWZ_sum_B_col (c : Fin 3) :
    ∑ i : Fin 32, dpulWZ (colInd c) i * pi1BVal i.val = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted A-shadow sum of the double-pulled
(M1, piU) `e_R` weights vanishes. -/
theorem dpulWZ_sum_A_eR :
    ∑ i : Fin 32, dpulWZ eRInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the double-pulled
(M1, piU) `e_R` weights vanishes. -/
theorem dpulWZ_sum_B_eR :
    ∑ i : Fin 32, dpulWZ eRInd i * pi1BVal i.val = 0 := by decide

/-- **The pulled trace at (M1, piU) vanishes** whenever
the two double-pulled shadow sums do — the front end is
the landed `trace_gammaF_proj_piU` (the `piU` sandwich
read back to `pi1` against the conjugated γ-weighted
M1-pull), the closing pattern is §2b's. -/
theorem pulled_trace_M1_piU (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (hA : ∑ i : Fin 32, dpulWZ ind i * pi1AVal i.val = 0)
    (hB : ∑ i : Fin 32, dpulWZ ind i * pi1BVal i.val = 0)
    (α β : ℤ) :
    Matrix.trace (gammaF * (M1ᵀ * P * M1) * piU (u1Gen α β))
      = 0 := by
  rw [ThetLogos.DialOnePiUFamily.trace_gammaF_proj_piU,
    ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal,
    ThetLogos.DialOnePiUFamily.trace_mul_diagonal]
  have hterm : ∀ i : Fin 32,
      (conjUᵀ * (gammaF * (M1ᵀ * P * M1)) * conjU) i i
          * (Complex.I
            * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ))
        = Complex.I / 625
          * ((dpulWZ ind i
              * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [pulled_diag_M1_piU P ind hP]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, dpulWZ ind i
        * (pi1AVal i.val * α + pi1BVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, dpulWZ ind i
          * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (dpulWZ ind i * pi1AVal i.val) * α
          + (dpulWZ ind i * pi1BVal i.val) * β :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      hA, hB]
    simp
  rw [hsum]
  simp

/-! ## §4c. The pulled clauses at (M1, piU) and the capstone instance -/

/-- **The pulled lepton clause at (M1, piU) — PROVED**
(the capstone's `hlep` at this pair). -/
theorem pulled_lep_M1_piU :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M1ᵀ * lepProj * M1)
        * piU (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_M1_piU lepProj lepInd
    ThetLogos.DialOnePiUFamily.lepProj_eq_diag
    dpulWZ_sum_A_lep dpulWZ_sum_B_lep α β

/-- **The pulled colour clause at (M1, piU) — PROVED**
(the capstone's `hcol` at this pair). -/
theorem pulled_col_M1_piU :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (M1ᵀ * colProj c * M1)
        * piU (u1Gen α β)) = 0 :=
  fun c α β => pulled_trace_M1_piU (colProj c) (colInd c)
    (ThetLogos.DialOnePiUFamily.colProj_eq_diag c)
    (dpulWZ_sum_A_col c) (dpulWZ_sum_B_col c) α β

/-- **The pulled e_R clause at (M1, piU) — PROVED**
(the capstone's `heR` at this pair). -/
theorem pulled_eR_M1_piU :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M1ᵀ * eRProj * M1)
        * piU (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_M1_piU eRProj eRInd
    ThetLogos.DialOnePiUFamily.eRProj_eq_diag
    dpulWZ_sum_A_eR dpulWZ_sum_B_eR α β

/-- **Preservation at the pair (M1, piU)** — the amended
capstone fires with M1's membership, `piU`'s landed
strengthened membership, and the three pulled clauses.
The `PreservationQReal` instance at this pair. **M1's
sweep row is complete: pi1, piAnti, piU all clean.** -/
theorem strengthened_conjRep_M1_piU :
    DialOneStrengthenedFam (conjRep M1 piU) :=
  ThetLogos.DialOneGradeRConjAmend.strengthened_preserved_of_real_pulled
    M1_realCentralizing piU
    ThetLogos.DialOnePiUFamily.strengthened_piU
    pulled_lep_M1_piU pulled_col_M1_piU pulled_eR_M1_piU

/-! ## §5a. The (M2, pi1) pulled machinery and shadow sums -/

/-- `M2ᵀ` times a matrix, entrywise: the row-permutation
form (the transpose trick, as `M1T_mul_apply`). -/
theorem M2T_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (M2ᵀ * M) i j = M (m2Seat i) j := by
  have h : (M2ᵀ * M) i j = (Mᵀ * M2) j i := by
    have e : (Mᵀ * M2)ᵀ = M2ᵀ * M := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← e]
    rfl
  rw [h, mul_M2_apply, Matrix.transpose_apply]

/-- The M2-conjugated diagonal is diagonal: a permutation
conjugation re-seats the diagonal. -/
theorem M2T_diag_M2_diag (d : Fin 32 → ℂ) (i : Fin 32) :
    (M2ᵀ * Matrix.diagonal d * M2) i i = d (m2Seat i) := by
  rw [Matrix.mul_assoc, M2T_mul_apply, mul_M2_apply,
    Matrix.diagonal_apply_eq]

/-- The γ-weighted pulled weight of M2 at seat `i` — an
integer (no denominator: a permutation pull). -/
def pulWZ2 (ind : ℕ → ℤ) (i : Fin 32) : ℤ :=
  gammaVal i.val * ind (m2Seat i).val

/-- **The M2-pulled diagonal of a projector, entrywise:**
the `(gammaF * (M2ᵀ * P * M2))` diagonal is the integer
`pulWZ2 ind s` in `ℂ`. -/
theorem pulled_diag_M2 (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (s : Fin 32) :
    (gammaF * (M2ᵀ * P * M2)) s s
      = ((pulWZ2 ind s : ℤ) : ℂ) := by
  rw [ThetLogos.DialOnePresSweep.gammaF_mul_entry_diag, hP,
    M2T_diag_M2_diag]
  unfold pulWZ2
  push_cast
  ring

/-- The γ-weighted A-shadow sum of the M2-pulled lepton
weights vanishes. -/
theorem pulWZ2_sum_A_lep :
    ∑ i : Fin 32, pulWZ2 lepInd i * pi1AVal i.val = 0 := by decide

/-- The γ-weighted B-shadow sum of the M2-pulled lepton
weights vanishes. -/
theorem pulWZ2_sum_B_lep :
    ∑ i : Fin 32, pulWZ2 lepInd i * pi1BVal i.val = 0 := by decide

/-- The γ-weighted A-shadow sum of the M2-pulled colour
weights vanishes, at every colour. -/
theorem pulWZ2_sum_A_col (c : Fin 3) :
    ∑ i : Fin 32, pulWZ2 (colInd c) i * pi1AVal i.val = 0 := by
  fin_cases c <;> decide

/-- The γ-weighted B-shadow sum of the M2-pulled colour
weights vanishes, at every colour. -/
theorem pulWZ2_sum_B_col (c : Fin 3) :
    ∑ i : Fin 32, pulWZ2 (colInd c) i * pi1BVal i.val = 0 := by
  fin_cases c <;> decide

/-- **The γ-weighted A-shadow sum of the M2-pulled `e_R`
weights is `1`, NOT zero** — the integer content of the
pulled eR clause at (M2, pi1) FAILS. The surviving seat
is 17: `m2Seat` sends the `e_R` seat 25 to seat 1 and
seat 9 to seat 17, and at seat 17 the γ-sign and the
`pi1` A-table multiply to `+1` with nothing cancelling
it. This is the computation the refutation (§5b) is
built on. -/
theorem pulWZ2_sum_A_eR :
    ∑ i : Fin 32, pulWZ2 eRInd i * pi1AVal i.val = 1 := by decide

/-- The γ-weighted B-shadow sum of the M2-pulled `e_R`
weights vanishes — the failure is in the A-direction
only, so the pulled eR trace at `(α, β)` is exactly
`α • I` (§5b). -/
theorem pulWZ2_sum_B_eR :
    ∑ i : Fin 32, pulWZ2 eRInd i * pi1BVal i.val = 0 := by decide

/-! ## §5b. (M2, pi1): the vanishing clauses, the failing clause, the refutation -/

/-- **The pulled trace at (M2, pi1) vanishes** whenever
the two shadow sums do — §2b's pattern at denominator
`1`. -/
theorem pulled_trace_M2_pi1 (P : Matrix (Fin 32) (Fin 32) ℂ)
    (ind : ℕ → ℤ)
    (hP : P = Matrix.diagonal (fun i => (ind i.val : ℂ)))
    (hA : ∑ i : Fin 32, pulWZ2 ind i * pi1AVal i.val = 0)
    (hB : ∑ i : Fin 32, pulWZ2 ind i * pi1BVal i.val = 0)
    (α β : ℤ) :
    Matrix.trace (gammaF * (M2ᵀ * P * M2) * pi1 (u1Gen α β))
      = 0 := by
  rw [ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal,
    ThetLogos.DialOnePiUFamily.trace_mul_diagonal]
  have hterm : ∀ i : Fin 32,
      (gammaF * (M2ᵀ * P * M2)) i i
          * (Complex.I
            * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ))
        = Complex.I
          * ((pulWZ2 ind i
              * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [pulled_diag_M2 P ind hP]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, pulWZ2 ind i
        * (pi1AVal i.val * α + pi1BVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, pulWZ2 ind i
          * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (pulWZ2 ind i * pi1AVal i.val) * α
          + (pulWZ2 ind i * pi1BVal i.val) * β :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      hA, hB]
    simp
  rw [hsum]
  simp

/-- **The pulled lepton clause at (M2, pi1) — PROVED.**
The failure at this point is eR-specific; lep and col
hold. -/
theorem pulled_lep_M2_pi1 :
    ∀ α β : ℤ,
      Matrix.trace (gammaF * (M2ᵀ * lepProj * M2)
        * pi1 (u1Gen α β)) = 0 :=
  fun α β => pulled_trace_M2_pi1 lepProj lepInd
    ThetLogos.DialOnePiUFamily.lepProj_eq_diag
    pulWZ2_sum_A_lep pulWZ2_sum_B_lep α β

/-- **The pulled colour clause at (M2, pi1) — PROVED.** -/
theorem pulled_col_M2_pi1 :
    ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (M2ᵀ * colProj c * M2)
        * pi1 (u1Gen α β)) = 0 :=
  fun c α β => pulled_trace_M2_pi1 (colProj c) (colInd c)
    (ThetLogos.DialOnePiUFamily.colProj_eq_diag c)
    (pulWZ2_sum_A_col c) (pulWZ2_sum_B_col c) α β

/-- **The pulled eR trace at (M2, pi1), computed
exactly:** it is `(α : ℂ) • I` — zero only at `α = 0`.
The A-sum is `1` (§5a) and the B-sum is `0`, so the
trace is the A-direction coefficient times `I`. -/
theorem pulled_eR_M2_pi1_value (α β : ℤ) :
    Matrix.trace (gammaF * (M2ᵀ * eRProj * M2)
        * pi1 (u1Gen α β))
      = (α : ℂ) * Complex.I := by
  rw [ThetLogos.DialOneShapeBIdentification.pi1_u1Gen_diagonal,
    ThetLogos.DialOnePiUFamily.trace_mul_diagonal]
  have hterm : ∀ i : Fin 32,
      (gammaF * (M2ᵀ * eRProj * M2)) i i
          * (Complex.I
            * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ))
        = Complex.I
          * ((pulWZ2 eRInd i
              * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [pulled_diag_M2 eRProj eRInd
      ThetLogos.DialOnePiUFamily.eRProj_eq_diag]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32, pulWZ2 eRInd i
        * (pi1AVal i.val * α + pi1BVal i.val * β) = α := by
    have h1 : ∀ i : Fin 32, pulWZ2 eRInd i
          * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (pulWZ2 eRInd i * pi1AVal i.val) * α
          + (pulWZ2 eRInd i * pi1BVal i.val) * β :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      pulWZ2_sum_A_eR, pulWZ2_sum_B_eR]
    simp
  rw [hsum]
  ring

/-- **The pulled eR clause at (M2, pi1) FAILS**: at
`(α, β) = (1, 0)` the trace is `I ≠ 0`. -/
theorem pulled_eR_M2_pi1_ne_zero :
    ¬ ∀ α β : ℤ,
      Matrix.trace (gammaF * (M2ᵀ * eRProj * M2)
        * pi1 (u1Gen α β)) = 0 := by
  intro h
  have h1 := h 1 0
  rw [pulled_eR_M2_pi1_value] at h1
  have hI : ((1 : ℤ) : ℂ) * Complex.I = Complex.I := by simp
  rw [hI] at h1
  exact Complex.I_ne_zero h1

/-- **`conjRep M2 pi1` is NOT in the strengthened
family**: its `FeR` component is the pulled eR clause
at (M2, pi1) (the landed `feR_conjRep_iff`, at M2's
landed centralizing membership), and that clause
fails. -/
theorem not_strengthened_conjRep_M2_pi1 :
    ¬ DialOneStrengthenedFam (conjRep M2 pi1) := by
  intro h
  have hFeR : FeR (conjRep M2 pi1) := h.2.2.2.2
  have h2 := (ThetLogos.DialOneGradeRConj.feR_conjRep_iff
    M2_centralizing pi1).mp hFeR
  exact pulled_eR_M2_pi1_ne_zero h2

/-- # **¬PreservationQReal — REFUTED AT T1. K-Q1-PRES-NEWU FIRES.**

The amended class's preservation statement is FALSE.
The counterexample pair is `(M2, pi1)`: M2 is a member
of the amended class at T1 (§1e,
`M2_realCentralizing`), `pi1` is in the strengthened
family (landed), but `conjRep M2 pi1` is not — its
`FeR` clause fails, the pulled eR trace at
`(α, β) = (1, 0)` being `I ≠ 0`
(`pulled_eR_M2_pi1_value`), the surviving seat being
17 (the M2 seat sends the `e_R` seats `{9, 25}` to
`{17, 1}`, and at seat 17 the γ-sign and the `pi1`
A-table multiply to `+1`).

Consequences, stated at their tiers: `PreservationQReal`
is decided — negatively. M-U1's preservation half closes
as a KILL; the orbit half was already refuted
(2026-11-08), so **the Q1 pair is fully decided, both
halves negative**. The positive instances stand as
proved: preservation holds at every `conjU` point swept
in `DialOnePresSweep` and at every M1 point (§§2–4 of
this module) — the failure is M2's, at pi1's eR clause.
NO CLAIM is touched: no measured number was ever
derived from preservation; Dial 1 remains 0, now with
its gauge-class question closed rather than open. -/
theorem not_PreservationQReal :
    ¬ ThetLogos.DialOneGradeRConjAmend.PreservationQReal := by
  intro h
  exact not_strengthened_conjRep_M2_pi1
    (h M2 pi1 M2_realCentralizing
      ThetLogos.DialOneGammaFamilyChecks.strengthened_pi1)

end ThetLogos.Q1PresSweep
