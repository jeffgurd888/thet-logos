# Brick α — The Crossing Marginal's Symmetries (PARTIAL, as registered)

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneCrossingSymm.lean` (strict 11, defs 9, zero
`sorry`, zero `native_decide`; main-tree build green, 3,397 jobs,
parent-verified on the shipped text). Scoped by the seat
computation memo routeb-general-scratch/crossing-sign-seats-2026-10-26.
**Parts of the Clay Yang–Mills statement closed by this landing:
0.** (H-PF) at general (G, ρ) remains L+/open; no positivity is
claimed here.*

## What landed

- **`planeCrossingMarginal_symm`** — the crossing marginal is
  symmetric in its two arguments at general (G, ρ), every even N,
  every real β (with reality and conjugate symmetry alongside).
  Proved through assembly reflection and Haar-inversion — the
  corpus packaging of the mechanism the seat computation found.
  Identification, stated exactly: the analyst's M *is*
  `planeCrossingMarginal`; the seat's factor A (with M = A⊙A) is
  an N = 2 object — at general even N the corpus exposes no
  one-stratum factor, and none is asserted here.
- **Diagonal gauge invariance** — `wilsonActionZero_gauge_invariant`,
  its assembly transport, and
  `planeCrossingMarginal_gauge_invariant`. A subtlety the proof
  forced into the open: the second argument's gauge action is
  necessarily the **mirror transport** (`gaugeMirrorPos`); the
  naive same-g linkwise action on z′ provably does not satisfy
  the transport identity, because z′ enters only through
  `joinNeg`'s mirror formula.

## The named remainder

**Brick α-remainder (open):** *separate* gauge invariance —
independent gauge functions per argument, the property the seat's
A has — and with it the (H-PF) reduction corollary (the pairing
sees only gauge-averaged observables). The diagonal statement
landed here does not imply the separate one at general N. It is
named, priced with Brick β's scoping, and not hidden.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Census effect

Strict 5,942 → **5,953**; attribute-inclusive 6,020 → **6,031**;
modules 200 → **201**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
