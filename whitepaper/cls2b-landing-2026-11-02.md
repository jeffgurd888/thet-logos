# CLS-2b LANDING DOSSIER — 2026-11-02

**Item:** CLS-2b (Dial-1 classification lane) — the decision
on `DialOneBase` at the uniform triple swap.

## VERDICT: THE BASE HOLDS — K-CLS-2 FIRES: the strengthened set has exactly two toggle-orbit points, pi1 and the uniform triple swap, and the second carries the WRONG weights

**Artifact:** `lean/ThetLogos/DialOneSwapOrbitBase.lean` —
strict 111, defs 3 (above the 25–50 estimate — entry
infrastructure for the clause-by-clause decision; reported
at actuals). Verified by the coordinator in the main tree
(build green, 3528 jobs); the headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

**The decision:** `base_allSwap : DialOneBase (orbitRep
allSwapBits)`, proved clause by clause (the 10-tuple
mirroring pi1's base proof), never by piDouble analogy. The
mechanism, proved where used: the uniform correction is
diagonal and **colour-blind** — its quark-R diagonal depends
only on seat parity (`swapCorr_diag_R`) — so order-zero
closes by the parity-only diagonal against ρ₁'s colour
matrix, and the first-order condition splits into brackets
that all vanish: the C1 brackets by pi1's landed first-order
theory, and [E, rho1] on the mixed (Lq, R)/(R, Lq) rectangles
by a **colour-sum collapse** (the Yukawa weight and the
correction diagonal are isospin-only, and ρ₁'s colour entries
at fixed isospin agree on both sides). The colour-uniformity
that defeated both CLS-2 exclusion mechanisms is exactly
what the base clauses reward.

**K-CLS-2 FIRES.** Assembled:
`allSwap_mem_strengthened : DialOneStrengthenedFam (orbitRep
allSwapBits)` (via the landed `strengthened_allSwap_iff_base`),
and the completed classification:

```
orbit_classification_complete :
  ∀ b, DialOneStrengthenedFam (orbitRep b) ↔ b = 0 ∨ b = allSwapBits
```

**The weight read-back, in the strong form:**
`allSwap_not_weightAt_common : ¬ weightAt (orbitRep
allSwapBits) commonWeightVector` — the determinant-1 and
gcd conditions force the direction (α, β) = ±(3, −1); along
it, the lifted entry at uSeat 0 has exponent ∓2, against the
common matrix's 4 at that seat; character rigidity closes.
So the strengthened set's second toggle point is a genuinely
different representation carrying different weights — **not**
a compensator for the table, and Grade W is untouched:
`WeightQuestionW` (does ANY π ≠ pi1 in the strengthened set
carry the table's weights?) remains open exactly as pinned,
now with its toggle-orbit chapter fully decided on both
sides — membership AND weights.

**CLS-2's PARTIAL seam is thereby closed** (its landed text
stands untouched in `DialOneSwapOrbit`, per discipline; this
dossier + module supersede its verdict). The group-law seam
((ℤ/2)⁴ composition form) remains named open — the orbit is
classified as a set with membership and weights; the
composition law is bookkeeping the lane has not needed.

## Fences

NO CLAIM; **Dial 1: 0.** Classification state: Grade T
COMPLETE over the 16-point orbit (two points in, both with
weights read: pi1 = the table, allSwap ≠ the table);
Grade W open (non-toggle representations unclassified —
CLS-1, the extraction gap, is the next priced item);
Grade R unposed.

**Census after landing: 12,090 strict / 12,450 total / 410 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
