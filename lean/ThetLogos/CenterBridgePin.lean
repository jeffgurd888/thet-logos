/-
# CenterBridgePin — the center-of-mass / center-of-gravity bridge (finite ℚ seat)

Zero's seeing chain of 2026-11-15: "cold is forced to find center of mass" →
"center of mass equals center of gravity" → "also equals the strongest center
thermal Equilibrium". This pin builds ONLY the first equality's bridge, as
algebra, on a finite rational seat: sites `ι` (a `Fintype` with `Nonempty`),
positions `x : ι → ℚ` on a line, masses `m : ι → ℚ` positive, and a pull
function `g : ι → ℚ` positive (the field's pull at each site).

What is proved here:
- the **bridge identity** (`bridge_uniform`): if the pull is constant
  (`g i = c` for all `i`), the center of gravity *is* the center of mass —
  the two weighted averages coincide because the weightings coincide;
- the **hot leg** (`wCenter_const`): constant weights reduce the weighted
  center to the plain average of positions;
- the **split** (`dumbbell_split`, Brick 2): on a two-site seat with uneven
  pull, the center of gravity sits strictly on the stronger-pulled side of
  the center of mass, both centers strictly between the two sites;
- the **cold leg** (`wCenter_deviation`, `wCenter_deviation_le`, Brick 2):
  the weighted center's deviation from site 0 is exactly the far weight's
  share `w 1 / (w 0 + w 1)` of the span, bounded by `w 1 / w 0` of the span —
  as the far weight's share shrinks, the weighted center walks to the
  ground site (the GAPFLOOR shape).

Fences (read before citing):
- This pin proves an algebraic identity about CENTERS. It is NOT a gravity
  object: the corpus holds zero gravity objects, Dial 2 = 0, and only
  G-READ stands. NO CLAIM.
- It does NOT prove the chain's third step: a self-gravitating system has
  no true thermal equilibrium (negative heat capacity); nothing here seats
  one, and the center of a self-gravitating body is a balance point, not a
  resting equilibrium.
- The Gibbs join is by shared weighted-average form only: this module's
  weights are rational; the in-tree Gibbs weights
  (`ModularVariance.profWeight`, positivity proved in the census as
  `profWeight_pos`) are real exponentials satisfying the same positivity
  hypothesis. This module states that reading; it does not re-prove the
  real case, and it imports nothing from the tree.
- The GR center problem (no unique center of mass for an extended body in
  curved spacetime) is FRONTIER and untouched.

Charter: T5 for the seeing; the theorems below are T1 lane grade when
proved. Working label only — the public name is Zero's to coin.
-/

import Mathlib

namespace ThetLogos.CenterBridgePin

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The weighted center of positions `x` under weights `w`:
the weight-weighted average `(∑ i, w i * x i) / (∑ i, w i)`. -/
def wCenter (w x : ι → ℚ) : ℚ :=
  (∑ i, w i * x i) / (∑ i, w i)

/-- The center of mass: the mass-weighted average of positions. -/
def centerMass (m x : ι → ℚ) : ℚ :=
  wCenter m x

/-- The center of gravity: each site weighted by its mass times the
field's pull at that site. -/
def centerGrav (m g x : ι → ℚ) : ℚ :=
  wCenter (fun i => m i * g i) x

/-- The denominator of a weighted center is positive when every weight is. -/
theorem sum_pos_of_pos {w : ι → ℚ} (hw : ∀ i, 0 < w i) : 0 < ∑ i, w i :=
  Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty

/-- The gravity weights `m i * g i` are positive when masses and pulls are. -/
theorem gravWeight_pos {m g : ι → ℚ} (hm : ∀ i, 0 < m i) (hg : ∀ i, 0 < g i) :
    ∀ i, 0 < m i * g i :=
  fun i => mul_pos (hm i) (hg i)

/-- **THE BRIDGE.** If the field's pull is constant (`g i = c` for all `i`,
with `c > 0`), the center of gravity equals the center of mass: the
weightings `m i * c` and `m i` differ by the constant factor `c`, which
cancels in the weighted average. -/
theorem bridge_uniform {m g x : ι → ℚ} {c : ℚ} (hm : ∀ i, 0 < m i)
    (hg : ∀ i, g i = c) (hc : 0 < c) :
    centerGrav m g x = centerMass m x := by
  have hnum : (∑ i, (m i * g i) * x i) = c * (∑ i, m i * x i) := by
    calc (∑ i, (m i * g i) * x i) = ∑ i, c * (m i * x i) :=
          Finset.sum_congr rfl (fun i _ => by rw [hg i]; ring)
    _ = c * (∑ i, m i * x i) := by rw [Finset.mul_sum]
  have hden : (∑ i, m i * g i) = c * (∑ i, m i) := by
    calc (∑ i, m i * g i) = ∑ i, c * m i :=
          Finset.sum_congr rfl (fun i _ => by rw [hg i]; ring)
    _ = c * (∑ i, m i) := by rw [Finset.mul_sum]
  have hc0 : c ≠ 0 := ne_of_gt hc
  unfold centerGrav centerMass wCenter
  rw [hnum, hden, mul_div_mul_left _ _ hc0]

/-- **The hot leg.** With constant weights, the weighted center is the
plain average of positions: `wCenter w x = (∑ i, x i) / card ι`
(the β = 0 reading: constant Gibbs weights average everything evenly). -/
theorem wCenter_const {w x : ι → ℚ} {c : ℚ} (hw : ∀ i, w i = c) (hc : 0 < c) :
    wCenter w x = (∑ i, x i) / (Fintype.card ι : ℚ) := by
  have hnum : (∑ i, w i * x i) = c * (∑ i, x i) := by
    calc (∑ i, w i * x i) = ∑ i, c * x i :=
          Finset.sum_congr rfl (fun i _ => by rw [hw i])
    _ = c * (∑ i, x i) := by rw [Finset.mul_sum]
  have hden : (∑ i, w i) = c * (Fintype.card ι : ℚ) := by
    calc (∑ i, w i) = ∑ _i : ι, c :=
          Finset.sum_congr rfl (fun i _ => hw i)
    _ = (Fintype.card ι : ℚ) * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = c * (Fintype.card ι : ℚ) := mul_comm _ _
  have hc0 : c ≠ 0 := ne_of_gt hc
  unfold wCenter
  rw [hnum, hden, mul_div_mul_left _ _ hc0]

/-- Sanity: the weighted center of a constant configuration is that
constant — a body sitting at one point has its center there. -/
theorem wCenter_const_config {w : ι → ℚ} (hw : ∀ i, 0 < w i) (a : ℚ) :
    wCenter w (fun _ => a) = a := by
  have hS : (∑ i, w i) ≠ 0 := ne_of_gt (sum_pos_of_pos hw)
  unfold wCenter
  show (∑ i, w i * a) / (∑ i, w i) = a
  rw [← Finset.sum_mul, div_eq_iff hS]
  ring


/-- Helper: on a two-site seat with positive weights, the weighted center
lies strictly between the two positions. -/
theorem wCenter_between {w x : Fin 2 → ℚ} (hw : ∀ i, 0 < w i) (hx : x 0 < x 1) :
    x 0 < wCenter w x ∧ wCenter w x < x 1 := by
  have hS : 0 < w 0 + w 1 := add_pos (hw 0) (hw 1)
  have h0 : 0 < w 0 := hw 0
  have h1 : 0 < w 1 := hw 1
  unfold wCenter
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  constructor
  · rw [lt_div_iff₀ hS]
    nlinarith [mul_pos h1 (sub_pos.mpr hx), mul_pos h0 (sub_pos.mpr hx)]
  · rw [div_lt_iff₀ hS]
    nlinarith [mul_pos h1 (sub_pos.mpr hx), mul_pos h0 (sub_pos.mpr hx)]

/-- On a dumbbell (two sites, `x 0 < x 1`), the center of mass lies
strictly between the two sites. -/
theorem dumbbell_com_between {m x : Fin 2 → ℚ} (hm : ∀ i, 0 < m i)
    (hx : x 0 < x 1) : x 0 < centerMass m x ∧ centerMass m x < x 1 :=
  wCenter_between hm hx

/-- On a dumbbell, the center of gravity also lies strictly between the
two sites (its weights `m i * g i` are positive). -/
theorem dumbbell_cog_between {m g x : Fin 2 → ℚ} (hm : ∀ i, 0 < m i)
    (hg : ∀ i, 0 < g i) (hx : x 0 < x 1) :
    x 0 < centerGrav m g x ∧ centerGrav m g x < x 1 :=
  wCenter_between (gravWeight_pos hm hg) hx

/-- **THE SPLIT.** On a dumbbell with the pull stronger at site 0
(`g 1 < g 0`), the center of gravity sits strictly on site 0's side of the
center of mass: `centerGrav < centerMass`. In closed form the gap is
`m 0 * m 1 * (g 0 - g 1) * (x 1 - x 0)` over the product of the two
denominators — every factor positive. -/
theorem dumbbell_split {m g x : Fin 2 → ℚ} (hm : ∀ i, 0 < m i)
    (hg : ∀ i, 0 < g i) (hx : x 0 < x 1) (hgs : g 1 < g 0) :
    centerGrav m g x < centerMass m x := by
  have hS : 0 < m 0 + m 1 := add_pos (hm 0) (hm 1)
  have hSg : 0 < m 0 * g 0 + m 1 * g 1 :=
    add_pos (mul_pos (hm 0) (hg 0)) (mul_pos (hm 1) (hg 1))
  have key : 0 < m 0 * m 1 * (g 0 - g 1) * (x 1 - x 0) :=
    mul_pos (mul_pos (mul_pos (hm 0) (hm 1)) (sub_pos.mpr hgs)) (sub_pos.mpr hx)
  unfold centerGrav centerMass wCenter
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [div_lt_div_iff₀ hSg hS]
  nlinarith [key]

/-- **The cold leg, exact form.** On a two-site seat, the weighted
center's deviation from site 0 is exactly the far weight's share
`w 1 / (w 0 + w 1)` of the span. -/
theorem wCenter_deviation {w x : Fin 2 → ℚ} (hw : ∀ i, 0 < w i)
    (hx : x 0 < x 1) :
    |wCenter w x - x 0| = (w 1 / (w 0 + w 1)) * |x 1 - x 0| := by
  have hS : 0 < w 0 + w 1 := add_pos (hw 0) (hw 1)
  have hS0 : (w 0 + w 1) ≠ 0 := ne_of_gt hS
  have hdev : wCenter w x - x 0 = (w 1 / (w 0 + w 1)) * (x 1 - x 0) := by
    unfold wCenter
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    field_simp
    ring
  rw [hdev, abs_mul, abs_of_pos (div_pos (hw 1) hS)]

/-- **The cold leg, GAPFLOOR-shaped bound.** The deviation is at most
`w 1 / w 0` of the span: as the far weight's share `w 1 / w 0` shrinks,
the weighted center walks to the ground site 0. -/
theorem wCenter_deviation_le {w x : Fin 2 → ℚ} (hw : ∀ i, 0 < w i)
    (hx : x 0 < x 1) :
    |wCenter w x - x 0| ≤ (w 1 / w 0) * |x 1 - x 0| := by
  have hS : 0 < w 0 + w 1 := add_pos (hw 0) (hw 1)
  have hshare : w 1 / (w 0 + w 1) ≤ w 1 / w 0 := by
    rw [div_le_div_iff₀ hS (hw 0)]
    nlinarith [mul_pos (hw 0) (hw 1), hw 1]
  rw [wCenter_deviation hw hx]
  exact mul_le_mul_of_nonneg_right hshare (abs_nonneg _)

end ThetLogos.CenterBridgePin
