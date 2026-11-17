/-
# LeibnizPin — the binary dot-row encoding of the LogicLock clock face

**Design-layer pin. NO CLAIM.**

The LogicLock clock face carries a Leibniz ring: every seat of the
calendar and every counted day is written as a row of dots, hollow
for `0` and filled for `1`, in the convention of Leibniz's tactile
clock (c. 1716, MS LBr. 916 Bl. 44r, Gottfried Wilhelm Leibniz
Bibliothek, Hannover) — position `0` nearest the centre with weight
`2^0 = 1`, the weights doubling outward, so the row can be read by
touch in the dark. This module pins that encoding and proves in the
kernel that the reading is exact: a row's value is the sum of its
filled dots' weights, the row of a number below `2^k` reads back to
that number, and the row of a value recovers the row.

This is a pin of a designed object's arithmetic. It proves facts
about a finite encoding and nothing else: no physics, no calendar
claim, NO CLAIM on any dial. The calendar's seats (April = 0,
numbered 0–12) and its counted labels (0–363) are taken as given.
April 1 — Zero.zero, the Boundary Day — stands outside the count
and carries NO row: the day row below is defined on `Fin 364`
only, so the residual day has no encoding, by the calendar's
ruling (2026-11-14: the count stays 0–363 in all years).
-/

import Mathlib

namespace ThetLogos

/-- The dot row of `n` on `k` positions, in Leibniz's convention:
position `0` nearest the centre, weight `2^0 = 1`, doubling
outward; the dot at position `i` is filled iff bit `i` of `n`
is set. -/
def dotRow (k : ℕ) (n : ℕ) : Fin k → Bool :=
  fun i => n.testBit i.val

/-- The number a dot row reads: the sum of the weights of its
filled dots. -/
def rowValue (k : ℕ) (r : Fin k → Bool) : ℕ :=
  ∑ i : Fin k, if r i then 2 ^ (i : ℕ) else 0

/-- Splitting a row one position out: the value of a row on
`k + 1` positions is the value of its inner `k` positions, plus
the outermost dot's weight if that dot is filled. -/
theorem rowValue_castSucc (k : ℕ) (r : Fin (k + 1) → Bool) :
    rowValue (k + 1) r
      = rowValue k (fun i => r i.castSucc) + (if r (Fin.last k) then 2 ^ k else 0) := by
  unfold rowValue
  rw [Fin.sum_univ_castSucc]
  congr 1

/-- A row on `k` positions reads below `2^k`. -/
theorem rowValue_lt : ∀ (k : ℕ) (r : Fin k → Bool), rowValue k r < 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro r
      simp [rowValue]
  | succ k ih =>
      intro r
      rw [rowValue_castSucc]
      have h1 := ih (fun i => r i.castSucc)
      have h2 : (if r (Fin.last k) then 2 ^ k else 0) ≤ 2 ^ k := by
        split <;> simp
      rw [pow_succ']
      omega

/-- The row of `n` on `k` positions reads `n % 2^k`: the row
keeps exactly the low `k` bits of `n`. -/
theorem rowValue_dotRow_mod : ∀ (k n : ℕ), rowValue k (dotRow k n) = n % 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro n
      have h0 : rowValue 0 (dotRow 0 n) = 0 := by simp [rowValue]
      rw [h0, show (2 : ℕ) ^ 0 = 1 from rfl, Nat.mod_one]
  | succ k ih =>
      intro n
      have hfun : (fun i => dotRow (k + 1) n i.castSucc) = dotRow k n := rfl
      have hlast : dotRow (k + 1) n (Fin.last k) = n.testBit k := rfl
      rw [rowValue_castSucc, hfun, hlast, ih]
      -- Goal: `n % 2^k + (if n.testBit k then 2^k else 0) = n % 2^(k+1)`.
      have ha : 0 < 2 ^ k := Nat.two_pow_pos k
      have hbit : (if n.testBit k then 2 ^ k else 0) = (n / 2 ^ k % 2) * 2 ^ k := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]
      rw [hbit]
      have hmod : n % 2 ^ (k + 1) = n % 2 ^ k + (n / 2 ^ k % 2) * 2 ^ k := by
        have h1 : n = 2 ^ k * (n / 2 ^ k) + n % 2 ^ k :=
          (Nat.div_add_mod n (2 ^ k)).symm
        have h2 : n / 2 ^ k = 2 * (n / 2 ^ k / 2) + n / 2 ^ k % 2 := by
          have h := (Nat.div_add_mod (n / 2 ^ k) 2).symm
          omega
        have h3 : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ ha
        have h4 : (n / 2 ^ k % 2) * 2 ^ k ≤ 2 ^ k := by
          rcases (by omega : n / 2 ^ k % 2 = 0 ∨ n / 2 ^ k % 2 = 1) with h | h <;> simp [h]
        have h6 : n = (2 ^ k * 2) * (n / 2 ^ k / 2)
            + ((n / 2 ^ k % 2) * 2 ^ k + n % 2 ^ k) := by
          have e1 := h1
          rw [h2] at e1
          exact e1.trans (by ring)
        have h7 : n % 2 ^ (k + 1)
            = (n / 2 ^ k % 2) * 2 ^ k + n % 2 ^ k := by
          have e2 : n % 2 ^ (k + 1) = n % (2 ^ k * 2) := by rw [pow_succ]
          rw [e2]
          conv_lhs => rw [h6]
          rw [Nat.add_comm ((2 ^ k * 2) * (n / 2 ^ k / 2))
              ((n / 2 ^ k % 2) * 2 ^ k + n % 2 ^ k),
            Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (show (n / 2 ^ k % 2) * 2 ^ k + n % 2 ^ k < 2 ^ k * 2 by omega)]
        rw [h7]
        exact Nat.add_comm _ _
      exact hmod.symm

/-- Reading the row of a number below `2^k` gives the number
back: the encoding is exact on its range. -/
theorem rowValue_dotRow (k n : ℕ) (h : n < 2 ^ k) :
    rowValue k (dotRow k n) = n := by
  rw [rowValue_dotRow_mod, Nat.mod_eq_of_lt h]

/-- The row of a value is the row it came from: encoding a
row's value recovers the row, position by position. -/
theorem dotRow_rowValue : ∀ (k : ℕ) (r : Fin k → Bool), dotRow k (rowValue k r) = r := by
  intro k
  induction k with
  | zero =>
      intro r
      funext i
      exact i.elim0
  | succ k ih =>
      intro r
      funext i
      show (rowValue (k + 1) r).testBit i.val = r i
      rw [rowValue_castSucc]
      have hlt : rowValue k (fun i => r i.castSucc) < 2 ^ k := rowValue_lt k _
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · -- Inner position `j`: the outermost dot contributes a multiple
        -- of `2^k`, which no bit below `k` can see.
        rw [Fin.val_castSucc]
        have hA : (rowValue k (fun i => r i.castSucc)
            + (if r (Fin.last k) then 2 ^ k else 0)).testBit j.val
            = (rowValue k (fun i => r i.castSucc)).testBit j.val := by
          by_cases hb : r (Fin.last k) = true
          · rw [if_pos hb, Nat.add_comm (rowValue k (fun i => r i.castSucc)) (2 ^ k)]
            exact Nat.testBit_two_pow_add_gt j.isLt _
          · rw [if_neg hb, Nat.add_zero]
        rw [hA]
        exact congrFun (ih _) j
      · -- Outermost position: the bit at `k` is exactly the last dot.
        rw [Fin.val_last]
        have hdiv : (rowValue k (fun i => r i.castSucc)
            + (if r (Fin.last k) then 2 ^ k else 0)) / 2 ^ k % 2
            = (r (Fin.last k)).toNat := by
          have hcase : (if r (Fin.last k) then 2 ^ k else 0)
              = (r (Fin.last k)).toNat * 2 ^ k := by
            cases hb : r (Fin.last k) <;> simp
          rw [hcase, Nat.mul_comm ((r (Fin.last k)).toNat) (2 ^ k),
            Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
            Nat.div_eq_of_lt hlt]
          cases hb : r (Fin.last k) <;> simp
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        cases hb : r (Fin.last k) <;> rfl

/-- Distinct numbers below `2^k` have distinct rows: `dotRow k`
is injective on its range. -/
theorem dotRow_injective (k : ℕ) :
    Function.Injective (fun n : {n : ℕ // n < 2 ^ k} => dotRow k n) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (rowValue k) hab
  rwa [rowValue_dotRow k a.val a.2, rowValue_dotRow k b.val b.2] at h

/-- The seat row: the row of a calendar seat (April = 0, seats
0–12) on four positions — weights 1, 2, 4, 8, exactly the row of
Leibniz's tactile clock. -/
def seatRow (s : Fin 13) : Fin 4 → Bool :=
  dotRow 4 s.val

/-- A seat's row reads back the seat. -/
theorem seatRow_value (s : Fin 13) : rowValue 4 (seatRow s) = s.val :=
  rowValue_dotRow 4 s.val (show s.val < 16 by have h := s.isLt; omega)

/-- Distinct seats have distinct rows. -/
theorem seatRow_injective : Function.Injective seatRow := by
  intro a b hab
  apply Fin.ext
  have h := congrArg (rowValue 4) hab
  rwa [seatRow_value, seatRow_value] at h

/-- The counted-day row: the row of a counted day (labels
0–363) on nine positions, weights 1 through 256. April 1,
outside the count, has no row: this is a function on `Fin 364`
only, so the residual day carries no encoding. -/
def dayRow (d : Fin 364) : Fin 9 → Bool :=
  dotRow 9 d.val

/-- A counted day's row reads back the day. -/
theorem dayRow_value (d : Fin 364) : rowValue 9 (dayRow d) = d.val :=
  rowValue_dotRow 9 d.val (show d.val < 512 by have h := d.isLt; omega)

/-- Distinct counted days have distinct rows. -/
theorem dayRow_injective : Function.Injective dayRow := by
  intro a b hab
  apply Fin.ext
  have h := congrArg (rowValue 9) hab
  rwa [dayRow_value, dayRow_value] at h

/-- Seat 12 — March, the seam seat — has its row filled at
exactly positions 2 and 3: weights 4 and 8, and 4 + 8 = 12.
This is Leibniz's own worked example on the manuscript page:
"4 und 8 macht 12". -/
theorem seatRow_twelve :
    ∀ i : Fin 4, seatRow ⟨12, by norm_num⟩ i = true ↔ i = 2 ∨ i = 3 := by
  decide

/-- Counted day 227 — the counted day of 2026-11-15 — has its
row filled at exactly positions 0, 1, 5, 6, 7: weights
1, 2, 32, 64, 128, summing to 227. -/
theorem dayRow_227 :
    ∀ i : Fin 9, dayRow ⟨227, by norm_num⟩ i = true
      ↔ i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  decide

end ThetLogos
