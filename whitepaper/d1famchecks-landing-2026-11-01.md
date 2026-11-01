# D1-CMP-FAM CHECKS LANDING DOSSIER — 2026-11-01

**Item:** D1-CMP-FAM (Dial-1 lane) — family pre-checks + the
quark-swap tests. Entry COMPLETE.

## VERDICT: FULL — K-CMP-F1 DOES NOT FIRE (proved); THE TOGGLE EXCLUSION LANDS

**Artifact:** `lean/ThetLogos/DialOneGammaFamilyChecks.lean` —
strict 83, defs 7 (above the pack's 18–35: the P-generic
trace machinery and per-colour order-zero lemmas live in this
one module; reported as counted, not trimmed). Verified by
the coordinator in the main tree (build green, 3140 jobs);
all ten headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## Part 1 — the family at π₁ and piDouble

π₁ satisfies the whole clean family: the γ-weighted (A, B)
sub-sums are (0, 0) for **every** clause (C3lep, C3col c for
each colour, FeR) — T1 by ℤ-shadow decide. **K-CMP-F2 does
not fire.** piDouble fails the family **by F_eR alone**, as
registered: C3lep and the colour clauses hold for it, and
`Tr (γ_F · eRProj · piDouble (u1Gen α β)) = −2αi`, witness
(1, 0) → −2i ≠ 0. **K-CMP-F3 does not fire.** F_eR is
load-bearing, confirmed in Lean.

## Part 2 — the quark swaps die at ORDER-ZERO

Every per-colour swap `piSwap c` (the (u_R^c, d_R^c) double
flip) **holds the whole family** — invisible to every clean
functional, as the kernel enumeration said — and satisfies
non-proportionality on its own seats (`swap_slice_nonprop`,
every colour). But **every swap FAILS `DialOneBase`, at the
order-zero clause**, by one mechanism at all three colours:
the toggle single at a quark-R seat does not commute with
ρ₁, whose quark-R block is a colour **matrix**, not a scalar
— with b carrying the colour single at (c′, c), the
(u_R^c, u_R^{c′}) entry of the two products is −i versus +i.
The base set grips the quark-R seats through the
colour-matrix order-zero clause in a way it does not grip
the lepton seats (where ρ-diagonals are scalars and the
(1↔9) pairing transported piDouble through). A structural
asymmetry of the base set, landed at T1.

**Therefore `kCMP_F1_does_not_fire : ¬ QuarkSwapCheck
piSwap` is proved**, and the registered conclusion lands at
exactly its rank: **`toggle_exclusion`** — π₁ ∈
`DialOneStrengthenedFam` (base ∧ C3 ∧ clean family), while
piFlip, piDouble, and every piSwap c stand outside it.
**Toggle-level exclusion only — NOT a forcing theorem**
(non-toggle representations remain the unscoped
classification question, CLS line).

**One pin-shape caveat, at full rank:** the pin's
non-proportionality statement quantifies over the colour-0
slice only, so as pinned it is vacuous for colours 1/2
(κ = 1 satisfies it) — an artefact of the conclusion shape
inherited from D1-CMP's pin. It does not touch the verdict
(every swap fails base regardless), and the per-colour form
`swap_slice_nonprop` is proved for all colours in this
module. Recorded so no future pass cites the pinned form
for more than it says.

## Fences

**Dial 1: 0.** NO CLAIM. The Dial-1 lane's landed state:
base + C3 + clean family excludes every toggle compensator
(piFlip, the lepton double flip, the three quark swaps);
forcing at every scoped set is either killed (base, base +
C3) or fenced off (the classification is the honest
frontier — CLS-0 is its registration pin, priced S).

**Census after landing: 11,644 strict / 11,942 total / 396 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
