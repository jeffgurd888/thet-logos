import ThetLogos.BSDRankPin
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDRefinedPin — the refined BSD formula for `E2`, pinned as a `Prop`

Source: the BSD goal charter (`goals/birch-and-swinnerton-dyer-the-long-project`),
rung 2 (the refined-formula pin for the worked curve), scoped 2026-10-29
(`scoping-bsd-rung-2-2026-10-29.md`). Design authority: rung 1
(`ThetLogos.BSDRankPin`) — named hypothesis Props as defs with genuine statable
content, honesty tiers in the header, analytic data carried as labeled debt,
never hidden inside a definition.

**What this file IS.** A machine-checked *statement* of the refined
Birch–Swinnerton-Dyer formula for the single worked curve `E2 : y² = x³ - 2`,
in the only honest form available today: exact objects where the tree owns
them, labeled seams where the literature owns them, and labeled numeric
interval hypotheses where only computation owns them — assembled so that the
one genuinely provable content (the balance, and the value of Sha) can be
proved, by interval arithmetic, in a later brick (B2-6). This brick (B2-0)
opens the module: the seams, the (c) value Props, the right-hand-side
assembly `refinedRHS`, the stated-and-unproved pin `BSDRefinedE2`, and the
bad-prime support fact. It proves nothing about the formula itself.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the rank
  equality (rung 1's `BSDRankEquality`, Wiles's chapter text). The refined
  formula is Wiles's Remark 1. This pin is a regression/honesty instrument
  for the statement; it is not, and must never be described as, the official
  statement or part of it.
- **Not existence of the package.** `BSDAnalyticData E2` existing is
  modularity — settled mathematics, formalization debt in this tree,
  inherited from rung 1 unchanged. The pin is vacuous at any `E` for which
  no package exists; it says so.
- **Not analytic Sha = algebraic Sha outside the region licence.** The
  `sha` the pin solves for is the analytic order (the real quotient).
  Identifying it with `#Ш(E2)` as a group order is licensed for this curve
  only by the Gross–Zagier/Kolyvagin proved region (with Rubin's/Kolyvagin's
  precise-coefficient results) — cited on Seam B1's face, not proved.
  Outside that region this identification is itself conjectural; the
  charter's pre-registered kill (analytic Sha used as algebraic Sha outside
  the proved region) is inherited by this rung verbatim.
- **Nothing about any other curve.** General-`E` refined BSD is not stated,
  let alone touched. `E1` appears only as B2-6's statement-only sibling;
  it is not in this brick.
- **No laundered exactness.** Every numeric hypothesis carries its bar on
  its face (±0.001 on Reg — hence on the sha conclusion; 1e-5 on `L′`, set
  conservatively below the method's E1-validated precision; 1e-7 on `Ω`).
  No statement in this module may quote Reg or Sha to more precision than
  1.3496 / 1.000 ± 0.001.

**The pin's shape, stated plainly.** Everything proved in this rung lives
on the right-hand side and in the assembly. The left-hand side is carried:
the analytic package is class (b) (a labeled hypothesis, rung 1), the
analytic order `analyticRank D = 1` is class (b) (a hypothesis on the
package), and the value of `deriv D.L 1` is class (c) (a numeric interval
hypothesis about a (b) object — the tree can neither compute nor bound
`deriv D.L 1`; see the scoping memo's §4).

**Board verdict.** Closing this rung in full closes **ZERO** parts of the
official statement. NO CLAIM on BSD, parts 0 — before, during, and after
this rung.

Honesty tiers in this file:
- **T1 (proved):** the bad-prime support fact `E2_bad_prime_support`.
- **T5 (statement, unproved by design):** `BSDRefinedE2` — a `def` stating
  a `Prop`, deliberately left unproved pending B2-1…B2-6.

**B2-1 addition (the torsion sweep).** The final section discharges the
torsion factor for `E2`, modulo the one shared seam: the sweep arithmetic
over `ℤ` (the candidate ordinates with `y² ∣ 1728`, and the exclusion of
rational cubes at `x³ = y² + 2`) is proved in-tree, and
`E2_torsion_card_eq_one_of_nagellLutz` concludes
`Nat.card (AddCommGroup.torsion E2.toAffine.Point) = 1` *conditional on*
the labeled hypothesis `NagellLutzCriterionE2` from rung 1, in the
sanctioned strength only. The board does not move: BSD parts closed by
this section: **0**, NO CLAIM.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The seams -/

/-- **Seam B1, E2 instance.** Ш(E2) is a finite group and the pin's `sha`
denotes its order; the group is not an object of this tree, so the seam's
statable residue is the positivity of the denoted order. The identification
of the analytic sha with `#Ш(E2)` is licensed for E2 ONLY by the
Gross–Zagier/Kolyvagin proved region (Rubin/Kolyvagin precise
coefficients), cited, not proved; outside that region the identification
is conjectural and this seam may not be assumed (the charter's kill,
inherited verbatim). -/
def ShaFiniteE2 (sha : ℕ) : Prop :=
  0 < sha

/-- **The Tamagawa seam instance, as a named hypothesis.** No Tamagawa
object exists in Mathlib; the value is the E2 study's Tate Step-3 hand
read-off (type II at 2 and at 3, `c₂ = c₃ = 1`, product 1); discharge is
B2-7, FRONTIER, not queued. -/
def E2TamagawaValue (tam : ℝ) : Prop :=
  tam = 1

/-! ## The (c) value Props — bars exactly as scoped; no tighter bar
may be introduced anywhere in this line. -/

/-- **The (c) value of `L′(E2, 1)`.** AFE value, method validated on E1
against LMFDB to 14 digits; the tree can neither compute nor bound
`deriv D.L 1` — scoping memo §4; B2-4/B2-5 carry the readout/provenance
soldering. The bar is ±1e-5 around 2.9200547683. -/
def E2LPrimeValue (D : BSDAnalyticData E2) : Prop :=
  |(deriv D.L 1).re - 2.9200547683| ≤ 1e-5

/-- **The (c) value of the regulator.** `Reg ∈ [1.3486, 1.3506]`, i.e.
1.3496 ± 0.001 — the duplication limit's own bar. -/
def E2RegulatorValue (Reg : ℝ) : Prop :=
  Reg ∈ Set.Icc 1.3486 1.3506

/-- **The (c) value of the period.** `Ω ∈ [2.1636817, 2.1636818]`
(±1e-7; quadrature and the Beta closed form agreed to 14 digits). -/
def E2PeriodValue (Ω : ℝ) : Prop :=
  Ω ∈ Set.Icc 2.1636817 2.1636818

/-! ## The right-hand-side assembly -/

/-- The refined formula's right-hand side, as a pure assembly function:
`sha * Ω * Reg * tam / tors ^ 2` (with `sha` coerced to `ℝ` at use sites).
It bakes in no finiteness, no value, and no conclusion: every factor is a
named hypothesis at the pin `BSDRefinedE2`. -/
noncomputable def refinedRHS (sha Ω Reg tam tors : ℝ) : ℝ :=
  sha * Ω * Reg * tam / tors ^ 2

/-! ## The pin -/

/-- **The pin (rung 2, E2 instance), stated and left unproved pending
B2-1…B2-6.** Parameterized over `(periodE2, regE2)` because the exact
objects land in B2-2/B2-3 and the Tamagawa value is a seam; B2-6
instantiates. The tolerance `5e-3` is set by the dominant error bar
(Reg's bar × Ω, plus margin), per the scoping memo §1.2. **`sha` is a
bound variable and its value is the conclusion's second conjunct —
derived in B2-6, never input (the circularity fence, memo §1.2).** The
torsion factor in `refinedRHS` is the literal `1`: `#tors = 1` is not a
hypothesis of this pin — it is B2-1's conditional theorem, discharged
modulo the one shared Nagell–Lutz seam. -/
def BSDRefinedE2 (periodE2 regE2 : ℝ) : Prop :=
  ∀ (D : BSDAnalyticData E2) (sha : ℕ) (tam : ℝ),
    ShaFiniteE2 sha → analyticRank D = 1 →
    E2LPrimeValue D → E2TamagawaValue tam →
    E2RegulatorValue regE2 → E2PeriodValue periodE2 →
    |(deriv D.L 1).re - refinedRHS sha periodE2 regE2 tam 1|
      ≤ 5e-3 ∧ sha = 1

/-! ## The bad-prime support fact -/

/-- The primes dividing `1728` are exactly `{2, 3}`: the bad-prime
support of E2, since `E2.Δ = -1728` (rung 1's `E2_delta`). Proved on the
Nat route from `1728 = 2^6 * 3^3` by prime-divisor arithmetic: a prime
dividing the product divides a factor, a prime dividing a prime power
divides the prime, and a prime dividing `2` (resp. `3`) is `2` (resp.
`3`). -/
theorem E2_bad_prime_support :
    ∀ p : ℕ, p.Prime → (p ∣ 1728 ↔ p = 2 ∨ p = 3) := by
  intro p hp
  constructor
  · intro hdvd
    have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [h1728] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · have hdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h1 | h2
      · exfalso; have hge := hp.two_le; omega
      · exact Or.inl h2
    · have hdvd3 : p ∣ 3 := hp.dvd_of_dvd_pow h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h1 | h3
      · exfalso; have hge := hp.two_le; omega
      · exact Or.inr h3
  · rintro (rfl | rfl)
    · norm_num
    · norm_num

/-! ## B2-1: the torsion sweep for `E2`, modulo the shared seam -/

/-- Integrality of a rational cube root: if `x : ℚ` satisfies
`x ^ 3 = c` for `c : ℤ`, then `x` is an integer and that integer cubes
to `c`. The route is the integral root theorem: `x` is a root of the
monic cubic `X ^ 3 - C c` over `ℤ` (`exists_integer_of_is_root_of_monic`),
so `x` is integral. No kernel decision procedure is run on `ℚ` goals. -/
theorem int_cube_of_rat_cube {c : ℤ} {x : ℚ} (hx : x ^ 3 = (c : ℚ)) :
    ∃ xi : ℤ, x = (xi : ℚ) ∧ xi ^ 3 = c := by
  have hroot : Polynomial.aeval x (Polynomial.X ^ 3 - Polynomial.C c) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      algebraMap_int_eq, sub_eq_zero]
    exact hx
  obtain ⟨xi, hxi, -⟩ := exists_integer_of_is_root_of_monic
    (p := (Polynomial.X ^ 3 - Polynomial.C c))
    (Polynomial.monic_X_pow_sub_C c (by norm_num)) hroot
  refine ⟨xi, by simpa using hxi, ?_⟩
  have h2 : (xi : ℚ) ^ 3 = (c : ℚ) := by simpa [hxi] using hx
  exact_mod_cast h2

/-- The sweep's cube exclusions: for each value
`c ∈ {2, 3, 6, 11, 18, 38, 66, 146, 578}` — namely `2` (the `y = 0`
case, `x ^ 3 = 2`) and `y ^ 2 + 2` for the nonzero Nagell–Lutz
candidate ordinates `y ∈ {±1, ±2, ±3, ±4, ±6, ±8, ±12, ±24}` — there
is no rational cube root of `c`. By `int_cube_of_rat_cube` a rational
root would be an integer `xi` with `xi ^ 3 = c`; positivity and
`c < 729 = 9 ^ 3` force `1 ≤ xi ≤ 8`, and the finitely many remaining
cases are checked by integer arithmetic. -/
theorem rat_cube_ne_of_sweep_value {c : ℤ}
    (hc : c = 2 ∨ c = 3 ∨ c = 6 ∨ c = 11 ∨ c = 18 ∨ c = 38 ∨ c = 66 ∨
      c = 146 ∨ c = 578)
    (x : ℚ) : x ^ 3 ≠ (c : ℚ) := by
  intro hx
  obtain ⟨xi, -, hxi⟩ := int_cube_of_rat_cube hx
  have hc_pos : 0 < c := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hc_lt : c < 729 := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hpos : 0 < xi := by
    by_contra hcon
    have hle : xi ≤ 0 := by omega
    have hnp : xi ^ 3 ≤ 0 := Odd.pow_nonpos (by norm_num) hle
    omega
  have hle8 : xi ≤ 8 := by
    by_contra hcon
    have h9 : (9 : ℤ) ≤ xi := by omega
    have h729 : (729 : ℤ) ≤ xi ^ 3 := by
      calc (729 : ℤ) = 9 ^ 3 := by norm_num
        _ ≤ xi ^ 3 := pow_le_pow_left₀ (by norm_num) h9 3
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases xi <;> norm_num at hxi

/-- The candidate enumeration: an integer whose square divides `1728`
is one of `0, ±1, ±2, ±3, ±4, ±6, ±8, ±12, ±24`. From `y ^ 2 ∣ 1728`
one gets `y ^ 2 ≤ 1728`, hence `-41 ≤ y ≤ 41`; the finitely many
remaining cases are checked by integer arithmetic (the true divisors
survive, the rest contradict the divisibility hypothesis). -/
theorem eq_of_sq_dvd_1728 (y : ℤ) (h : y ^ 2 ∣ 1728) :
    y = 0 ∨ y = 1 ∨ y = -1 ∨ y = 2 ∨ y = -2 ∨ y = 3 ∨ y = -3 ∨ y = 4 ∨
    y = -4 ∨ y = 6 ∨ y = -6 ∨ y = 8 ∨ y = -8 ∨ y = 12 ∨ y = -12 ∨
    y = 24 ∨ y = -24 := by
  have hle : y ^ 2 ≤ 1728 := Int.le_of_dvd (by norm_num) h
  have hhi : y ≤ 41 := by
    by_contra hcon
    have h42 : (42 : ℤ) ≤ y := by omega
    have hsq : (1764 : ℤ) ≤ y ^ 2 := by
      calc (1764 : ℤ) = 42 ^ 2 := by norm_num
        _ ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) h42 2
    omega
  have hlo : -41 ≤ y := by
    by_contra hcon
    have h42 : (42 : ℤ) ≤ -y := by omega
    have hsq : (1764 : ℤ) ≤ y ^ 2 := by
      calc (1764 : ℤ) = 42 ^ 2 := by norm_num
        _ ≤ (-y) ^ 2 := pow_le_pow_left₀ (by norm_num) h42 2
        _ = y ^ 2 := by ring
    omega
  interval_cases y <;> norm_num at h <;> norm_num

/-- The sweep's conclusion at the level of points, conditional on the
shared seam: under `NagellLutzCriterionE2` (sanctioned strength only),
every torsion point of `E2(ℚ)` — torsion in the criterion's own form,
`∃ n : ℤ, n ≠ 0 ∧ n • P = 0` — is the point at infinity. The affine
case is excluded candidate by candidate: the criterion gives integer
coordinates `(xi, yi)` on `y ^ 2 = x ^ 3 - 2` with `yi = 0` or
`yi ^ 2 ∣ 1728`; the enumeration `eq_of_sq_dvd_1728` lists the
possible `yi`, and for each of them `xi ^ 3 = yi ^ 2 + 2` is one of
the values excluded by `rat_cube_ne_of_sweep_value`. The point at
infinity is handled separately — it is not an affine `Point.some`. -/
theorem E2_point_eq_zero_of_torsion (hNL : NagellLutzCriterionE2)
    (P : E2.toAffine.Point) (htors : ∃ n : ℤ, n ≠ 0 ∧ n • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    obtain ⟨xi, yi, hx, hy, hy0⟩ := hNL x y h htors
    have heq : y ^ 2 = x ^ 3 - 2 := by
      have heq0 := h.1
      rw [WeierstrassCurve.Affine.equation_iff] at heq0
      simp only [E2] at heq0
      linarith [heq0]
    rw [hx, hy] at heq
    have hcube : (xi : ℚ) ^ 3 = ((yi ^ 2 + 2 : ℤ) : ℚ) := by
      push_cast
      linarith [heq]
    rcases hy0 with h0 | hdvd
    · subst h0
      norm_num at hcube
      exact absurd hcube (rat_cube_ne_of_sweep_value (by norm_num) xi)
    · rcases eq_of_sq_dvd_1728 yi hdvd with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> norm_num at hcube <;>
        exact absurd hcube (rat_cube_ne_of_sweep_value (by norm_num) xi)

/-- **B2-1's card theorem.** Conditional on the one shared seam
`NagellLutzCriterionE2`, the torsion subgroup of `E2(ℚ)` has
cardinality `1`: it is the trivial subgroup. The membership form of
Mathlib's torsion subgroup is finite additive order, i.e. a nonzero
*natural* multiple vanishing; that is converted to the criterion's
integer-multiple form (the cast `(n : ℤ)` with `n ≠ 0`) before
`E2_point_eq_zero_of_torsion` is applied, so the subgroup is `⊥`,
whose underlying type is a singleton. This is the `#tors = 1` the
refined pin consumes; it is conditional on the seam, and it closes
zero parts of the official BSD statement. -/
theorem E2_torsion_card_eq_one_of_nagellLutz (hNL : NagellLutzCriterionE2) :
    Nat.card (AddCommGroup.torsion E2.toAffine.Point) = 1 := by
  have hbot : AddCommGroup.torsion E2.toAffine.Point = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro P hP
    rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero] at hP
    obtain ⟨n, hn, hns⟩ := hP
    apply E2_point_eq_zero_of_torsion hNL P
    refine ⟨(n : ℤ), by exact_mod_cast hn.ne', ?_⟩
    simpa using hns
  rw [hbot]
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩,
    ⟨⟨0, AddSubgroup.zero_mem _⟩⟩⟩
  have ha : a.1 = 0 := AddSubgroup.mem_bot.mp a.2
  have hb : b.1 = 0 := AddSubgroup.mem_bot.mp b.2
  exact Subtype.ext (by rw [ha, hb])

end ThetLogos
