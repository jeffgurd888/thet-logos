import ThetLogos.BSDRankPin
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

end ThetLogos
