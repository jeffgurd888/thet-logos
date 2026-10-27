# BSD Rung 1 — the Rank Equality, Pinned

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/BSDRankPin.lean`
(strict 21, defs 15; zero placeholders, zero
`native_decide`; main-tree build green, 3,707 jobs,
parent-verified; every proved theorem's axiom set
inside `[propext, Classical.choice, Quot.sound]`).
**Parts of the Clay Birch–Swinnerton-Dyer statement
closed by this landing: 0. NO CLAIM.** Called by
Jeff 2026-10-27 ("build the bsd rung"). The two-rung
charter's first rung: pin the rank equality — which,
per Wiles's Clay chapter, is the whole Millennium
statement — in Lean, definitions-first. The pin
stands. It is a statement, not a proof: its truth is
the conjecture.*

## What the pin says

`BSDRankEquality`: for every nonsingular elliptic
curve E over ℚ, and for every analytic data package
for E, the analytic rank equals the algebraic rank:

ord_{s=1} L(E, s) = rank E(ℚ).

Both sides are defined before the assertion. The
algebraic rank is owned: the ℚ-rank of the rational
point group, carried through the tensor product with
ℚ (`algebraicRank E = Module.rank ℚ (ℚ ⊗[ℤ]
E(ℚ))`), with its sanity theorems proved in this
module — a finite point group has rank 0, and a
point of infinite order forces rank > 0
(`rank_pos_of_infiniteOrder`, via flatness of ℚ over
ℤ), with the finrank form carrying an explicit
`Module.Finite` side-hypothesis (Mordell–Weil
finiteness, flagged, not assumed invisibly).

The analytic rank is the order of vanishing at
s = 1 of a *hypothesized* continuation: the structure
`BSDAnalyticData` carries a holomorphic `L : ℂ → ℂ`,
its agreement with the Euler product, and the
analytic rank defined from it via the meromorphic
order at 1. The continuation is an **explicit labeled
hypothesis on the statement's face** — formalization
debt (the mathematics is settled via modularity;
Mathlib cannot yet prove it), never hidden inside a
definition. A statement that cannot fail is worth
nothing; this one can.

## One correction to the house's own audit

The 2026-10-19 BSD Mathlib Audit recorded "Mathlib
owns no L-function." **In this pin that is
superseded:** Mathlib v4.35.0-rc3 contains
`WeierstrassCurve.LFunction` / `LSeries`, built from
the same local polynomial 1 − aT + qT² with
a = q + 1 − #points that the audit derived by hand.
The agreement hypothesis is therefore stated against
Mathlib's owned `E.LSeries` — the full Euler product
— and the module's own Euler side (`ap`,
`localFactor`) is built and proved to agree with it
at good primes. Rank, Sha, the regulator, Tamagawa
numbers, and continuation at s = 1 remain unowned;
Sha and the leading-coefficient formula are rung 2
and absent here by design.

## The worked curve, y² = x³ − 2

Finite pieces, proved: the point (3, 5) is on the
curve; the integral model's discriminant is −1728;
a₅ = 0 and a₇ = 1 by enumeration of the points over
ZMod 5 and ZMod 7; the Nagell–Lutz arithmetic
(5 ≠ 0 and 25 ∤ −1728, over ℤ — divisibility lives
on the integral model) is proved. The infinite order
of (3, 5) — the one step between that arithmetic and
rank ≥ 1 — is carried as the explicitly labeled
hypothesis `E2InfiniteOrderHypothesis` (the
`nagellLutz_seam`): Nagell–Lutz is literature (T4),
its Lean proof is a named future brick, and rank ≥ 1
for this curve is proved *from* the hypothesis, in
both cardinal and finrank form. The seam is on the
module's face, not under it.

## Fences

This module pins a statement and proves finite
arithmetic about one curve. It proves no case of
BSD, no rank equality for any curve, and nothing
about Sha's finiteness. The Millennium board is
unchanged: NO CLAIM on every problem; parts closed
remain 0; Yang–Mills remains the active ladder and
this is a called side-rung on its bench.

Census effect: 6,825 → **6,846 strict** /
6,903 → **6,924 attribute-inclusive** / 234 → **235
modules**; the seven quarantined placeholders are
unchanged.

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
