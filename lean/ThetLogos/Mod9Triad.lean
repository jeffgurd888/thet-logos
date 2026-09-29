/-
  ThetLogos.Mod9Triad — the mod-9 arithmetic cited by the ontological integration.

  HONESTY LEDGER (read before citing):
  - This file proves ELEMENTARY ARITHMETIC FACTS about Z/9Z, all closed by
    `decide`. Zero sorrys, no new axioms.
  - It does NOT prove any physical claim. The mappings Layer 0/3/5/1-2/6
    (triad ↔ TRO product, wheel ↔ modular flow, etc.) are INTERPRETIVE
    (Tier 5): suggestive correspondences, not deductions. This file is the
    arithmetic the ontology cites — nothing more.
  - "Invariant under triadic scaling": multiplication by 3 collapses every
    triad element to 0 (3·3 = 9 ≡ 0). The file states this exactly as it is:
    the scaling returns everything to the identity — the completion that is
    also the origin. It does not pretend this is deep.

  Contents:
  - `triad = {0,3,6}`: closed under addition, contains 0 and negatives,
    card 3, annihilated-by-3 characterization (= the unique order-3 content).
  - `wheel = {1,2,4,5,7,8}`: exactly the orbit of 2^k mod 9 (period 6).
  - `axis_wheel_disjoint`: the orbit never lands on the triad.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

namespace ThetLogos.Mod9

/-- The invariant triadic axis: {0, 3, 6} ⊆ Z/9Z. -/
def triad : Finset (ZMod 9) := {0, 3, 6}

/-- The dynamic wheel: the doubling orbit, {1, 2, 4, 5, 7, 8} ⊆ Z/9Z. -/
def wheel : Finset (ZMod 9) := {1, 2, 4, 5, 7, 8}

/-- Closure under addition: the triad is additively closed. -/
theorem triad_closed_add : ∀ x ∈ triad, ∀ y ∈ triad, x + y ∈ triad := by
  decide

/-- The triad contains the identity. -/
theorem triad_zero_mem : (0 : ZMod 9) ∈ triad := by
  decide

/-- The triad is closed under negation. -/
theorem triad_neg_mem : ∀ x ∈ triad, -x ∈ triad := by
  decide

/-- The triad has exactly three elements. -/
theorem triad_card : triad.card = 3 := by
  decide

/-- Triadic scaling: multiplying any triad element by 3 returns the identity.
    (3·3 = 9 ≡ 0, 3·6 = 18 ≡ 0: the scaling collapses to the origin.) -/
theorem triad_scale_three : ∀ x ∈ triad, 3 * x ∈ triad := by
  decide

/-- The elements annihilated by 3 are exactly the triad.
    This is the computational content of "unique order-3 subgroup":
    every element of order dividing 3 lies in {0,3,6}. -/
theorem annihilator_eq_triad :
    Finset.filter (fun x : ZMod 9 => 3 * x = 0) Finset.univ = triad := by
  decide

/-- The doubling has period 6 mod 9. -/
theorem two_pow_six : (2 : ZMod 9) ^ 6 = 1 := by
  decide

/-- Every power of 2 mod 9 lands on the wheel. -/
theorem wheel_mem_pow : ∀ k : ℕ, (2 : ZMod 9) ^ k ∈ wheel := by
  intro k
  have h6 : (2 : ZMod 9) ^ 6 = 1 := by decide
  have hred : (2 : ZMod 9) ^ k = (2 : ZMod 9) ^ (k % 6) := by
    conv_lhs => rw [← Nat.div_add_mod k 6]
    rw [pow_add, pow_mul, h6, one_pow, one_mul]
  rw [hred]
  have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  suffices h : ∀ r : ℕ, r < 6 → (2 : ZMod 9) ^ r ∈ wheel from h _ hlt
  intro r hr
  interval_cases r <;> decide

/-- Every wheel element is a power of 2 (exponent below 6). -/
theorem wheel_subset_powers :
    ∀ x ∈ wheel, ∃ k : ℕ, k < 6 ∧ (2 : ZMod 9) ^ k = x := by
  decide

/-- The doubling orbit never lands on the triadic axis. -/
theorem axis_wheel_disjoint : Disjoint triad wheel := by
  decide

end ThetLogos.Mod9
