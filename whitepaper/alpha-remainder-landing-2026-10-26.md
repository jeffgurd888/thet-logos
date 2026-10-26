# Brick α-Remainder — Separate Gauge Invariance and the Reduction

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneCrossingSeparate.lean` (strict 42, defs 6,
zero `sorry`, zero `native_decide`; main-tree build green, 3,398
jobs, parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** (H-PF) at
general (G, ρ) remains L+/open — this brick is invariance and
reduction, not positivity.*

## What landed

- **`planeCrossingMarginal_gauge_invariant_separate`** — the
  crossing marginal is invariant under *independent* gauge
  functions on its two arguments, at general (G, ρ), all even N,
  all real β (with one-sided forms), and the same for
  `planeAvgKernel` through the corpus factorization.
- **The reduction corollary** — `planeAvgPairing` (the owned
  osForm integrand) is slot-wise gauge invariant, and
  `planeAvgPairing_averages`: pairing the two Haar gauge averages
  of the observables equals pairing the observables themselves.
  **The pairing factors through the two twirls** — (H-PF) at
  general geometry is now, as a theorem, a question about
  gauge-invariant observables only.

## The mechanism — why separate was hiding inside diagonal

The decoupling is in the gauge functions, not the strata.
`gaugePosFun g` reads only site times < N/2; `gaugeMirrorPos h`
reads only site times ≥ N/2 — the reflection is *between* sites.
So the glued function `gaugeGlued g h` acts as g on the first
argument and as h on the second, independently, and Brick α's
diagonal theorem applied to the glued function *is* separate
invariance. What α's dossier named as a remainder fell to a
reading of its own proof.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## What remains of the finite theory's last wall

The reduction is complete; the core is positivity of the one-layer
kernel 𝒜 from the Brick β scoping (M = A₁·A₂, both factors
evaluations of 𝒜). β1 (the factorization brick, M) is next;
𝒜 ⪰ 0 itself (β2) remains L+/open with its mechanism scoping
priced S.

## Census effect

Strict 6,058 → **6,100**; attribute-inclusive 6,136 → **6,178**;
modules 207 → **208**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
