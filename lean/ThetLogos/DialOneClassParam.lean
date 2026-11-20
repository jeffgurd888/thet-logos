import Mathlib.Tactic
import ThetLogos.Q1PresSweep

open Matrix Complex
open ThetLogos.PreOptionARepresentation
open ThetLogos.DialOneGradeRConjPin
open ThetLogos.DialOneGradeRConjAmend
open ThetLogos.DialOneConjugationCounterexample
open ThetLogos.Q1PresSweep

namespace ThetLogos.DialOneClassParam

/-!
# ThetLogos.DialOneClassParam — CLS Line C: the (P,Q) parametrization at T1

Governing texts: the CLS classification scope
(`cls-classification-scope-2026-11-17.md`, Line C) and the Q1P-0
hull computation (`q1p0-hull-computation-2026-11-14.md`).

**PROBE-GRADE NOTICE.** Q1P-0 computed, by exact rational
arithmetic (cross-validated, NOT kernel-checked), that the linear
hull of `RealCentralizingClass` over ℚ is 40-dimensional with the
`(P, Q)` block form below, `P, Q ∈ 𝒯`, and that membership in the
class is the hull cut by `PPᵀ + QQᵀ = I₈ ∧ PQᵀ + QPᵀ = 0`. This
module upgrades that parametrization to kernel-checked T1, brick
by brick (CLS-C1: the (a)∧(c) commutant; CLS-C2: the
(b)-identification; CLS-C3: the quadratic cut). **Until a brick
lands, its content stays PROBE GRADE and is labeled so.**

Fences: the decided neighbors stay decided — `PiAntiOrbitQReal`
and `PreservationQReal` are REFUTED at T1, M-U1 is CLOSED; this
module reopens nothing. A full landing buys program closure
(Q1P-0 at T1), NOT an M-U2 target: **Dial 1 = 0 under every
outcome. NO CLAIM.** Kill armed: **K-CLS-PARAM** — if any block
step fails in Lean, Q1P-0 stays probe grade permanently and
landed sub-bricks report as partial results, not as a
classification.
-/

/-! ## §0. Infrastructure: type classes, block/local indices, seats -/

/-- The Yukawa type class of a local seat index: `ν ↦ 0`,
`e ↦ 1`, `u ↦ 2`, `d ↦ 3`. On local indices `0..7` this reads
`0, 1, 2, 3, 2, 3, 2, 3` — the `A`-pattern of `DF_oneGen`,
matching the case split inside `dcoef`. -/
def yukClass (n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then 1 else if n % 2 = 0 then 2 else 3

theorem yukClass_lt (n : ℕ) : yukClass n < 4 := by
  unfold yukClass
  split_ifs <;> omega

/-- The type space `𝒯`: the 8×8 matrices supported within Yukawa
type classes (Q1P-0: `dim 𝒯 = 1² + 1² + 3² + 3² = 20`). -/
def InT (P : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  ∀ a b : Fin 8, yukClass a.val ≠ yukClass b.val → P a b = 0

/-- The 8-block index of a seat (`0, 1, 2, 3` for
`B0, B1, B2, B3`). -/
def blk (i : Fin 32) : ℕ := i.val / 8

/-- The local index of a seat, as a natural (`i.val % 8`). -/
def locv (i : Fin 32) : ℕ := i.val % 8

/-- The local index of a seat. -/
def loc (i : Fin 32) : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The seat with block `r` and local index `a`. -/
def seat (r : Fin 4) (a : Fin 8) : Fin 32 :=
  ⟨r.val * 8 + a.val, by have h1 := r.isLt; have h2 := a.isLt; omega⟩

theorem blk_seat (r : Fin 4) (a : Fin 8) : blk (seat r a) = r.val := by
  have h2 := a.isLt
  change (r.val * 8 + a.val) / 8 = r.val
  omega

theorem loc_seat (r : Fin 4) (a : Fin 8) : loc (seat r a) = a := by
  apply Fin.ext
  have h1 := r.isLt
  have h2 := a.isLt
  change (r.val * 8 + a.val) % 8 = a.val
  omega

theorem locv_seat (r : Fin 4) (a : Fin 8) : locv (seat r a) = a.val := by
  have h1 := r.isLt
  have h2 := a.isLt
  change (r.val * 8 + a.val) % 8 = a.val
  omega

/-- A seat is recovered from its block and local indices. -/
theorem seat_blk_loc (i : Fin 32) :
    seat ⟨blk i, by unfold blk; have h := i.isLt; omega⟩ (loc i) = i := by
  apply Fin.ext
  have h := i.isLt
  change (i.val / 8) * 8 + i.val % 8 = i.val
  omega

/-- `seat r a = i` iff `r` is `i`'s block and `a` is `i`'s local
index. -/
theorem seat_eq_iff {r : Fin 4} {a : Fin 8} {i : Fin 32} :
    seat r a = i ↔ r.val = blk i ∧ a = loc i := by
  constructor
  · intro h
    have h1 : blk (seat r a) = blk i := by rw [h]
    have h2 : loc (seat r a) = loc i := by rw [h]
    rw [blk_seat] at h1
    rw [loc_seat] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have h := seat_blk_loc i
    rw [← h2] at h
    have hr : (⟨blk i, by unfold blk; have hh := i.isLt; omega⟩ : Fin 4) = r := by
      apply Fin.ext
      simp [h1]
    rw [hr] at h
    exact h

theorem blk_cases (i : Fin 32) :
    blk i = 0 ∨ blk i = 1 ∨ blk i = 2 ∨ blk i = 3 := by
  unfold blk
  have h := i.isLt
  omega

/-- The 80-dimensional (a)∧(c) form of Q1P-0's staged
computation: diagonal blocks `P` (blocks 0, 1) and `S`
(blocks 2, 3); off-diagonal blocks `Q` (blocks `(0,3)`, `(1,2)`)
and `R` (blocks `(2,1)`, `(3,0)`); all other blocks zero. -/
def blockPQ80 (P Q R S : Matrix (Fin 8) (Fin 8) ℂ) :
    Matrix (Fin 32) (Fin 32) ℂ :=
  fun i j =>
    if blk i = blk j then (if blk i ≤ 1 then P else S) (loc i) (loc j)
    else if blk i + blk j = 3 then (if blk i ≤ 1 then Q else R) (loc i) (loc j)
    else 0

/-! ## §1. Entry API: block maps of the seat involutions -/

/-- The block map of the Dirac partner seat: `0 ↔ 1`, `2 ↔ 3`. -/
def dparBlk (r : ℕ) : ℕ :=
  if r = 0 then 1 else if r = 1 then 0 else if r = 2 then 3 else 2

/-- The block map of the antiparticle partner: `0 ↔ 2`, `1 ↔ 3`. -/
def parBlk (r : ℕ) : ℕ :=
  if r = 0 then 2 else if r = 1 then 3 else if r = 2 then 0 else 1

theorem blk_dparSeat (i : Fin 32) : blk (dparSeat i) = dparBlk (blk i) := by
  unfold blk dparBlk dparSeat
  split_ifs <;> simp only [] <;> omega

theorem loc_dparSeat (i : Fin 32) : loc (dparSeat i) = loc i := by
  apply Fin.ext
  unfold loc dparSeat
  split_ifs <;> simp only [] <;> omega

theorem locv_dparSeat (i : Fin 32) : locv (dparSeat i) = locv i := by
  unfold locv dparSeat
  split_ifs <;> simp only [] <;> omega

theorem blk_partner (i : Fin 32) : blk (partner i) = parBlk (blk i) := by
  unfold blk parBlk
  rw [partner_val_eq]
  have h := i.isLt
  split_ifs <;> omega

theorem loc_partner (i : Fin 32) : loc (partner i) = loc i := by
  apply Fin.ext
  show (partner i).val % 8 = i.val % 8
  rw [partner_val_eq]
  have h := i.isLt
  split_ifs <;> omega

theorem locv_partner (i : Fin 32) : locv (partner i) = locv i := by
  unfold locv
  rw [partner_val_eq]
  have h := i.isLt
  split_ifs <;> omega

/-- The Dirac partner seat acts on seats through `dparBlk`,
preserving the local index. -/
theorem dparSeat_seat (r : Fin 4) (a : Fin 8) :
    dparSeat (seat r a)
      = seat ⟨dparBlk r.val, by
          have h1 := r.isLt
          unfold dparBlk
          split_ifs <;> omega⟩ a := by
  symm
  apply seat_eq_iff.mpr
  constructor
  · show dparBlk r.val = blk (dparSeat (seat r a))
    rw [blk_dparSeat, blk_seat]
  · show a = loc (dparSeat (seat r a))
    rw [loc_dparSeat, loc_seat]

/-- The antiparticle partner acts on seats through `parBlk`,
preserving the local index. -/
theorem partner_seat (r : Fin 4) (a : Fin 8) :
    partner (seat r a)
      = seat ⟨parBlk r.val, by
          have h1 := r.isLt
          unfold parBlk
          split_ifs <;> omega⟩ a := by
  symm
  apply seat_eq_iff.mpr
  constructor
  · show parBlk r.val = blk (partner (seat r a))
    rw [blk_partner, blk_seat]
  · show a = loc (partner (seat r a))
    rw [loc_partner, loc_seat]

end ThetLogos.DialOneClassParam
