# The Doeblin Step — An Explicit Gap Bound at General (G, ρ)

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/DoeblinGap.lean` (strict 20, defs 3, zero
`sorry`, zero `native_decide`; main-tree build green, 3,577
jobs, parent-verified). **Parts of the Clay Yang–Mills
statement closed by this landing: 0.** The bound proved here
decays with volume and says nothing at large N — uniformity
across N remains open. Read the fence before citing the
number.*

## The headline

Until today, the corpus's per-instance gap was qualitative:
δ = 1 − sup R, its positivity extracted by contradiction with
vacuum simplicity, no modulus in (β, N) anywhere. This module
assembles the Doeblin minorization from landed parts (U-0's
pointwise kernel floor; both marginals of the two-slice kernel
equal to 1 a.e.; the HDen form identity) and proves:

> **`transfer_spectrum_le_doeblin`** — at general (G, ρ),
> every even N ≥ 2, all real β: every spectral point λ ≠ 1 of
> the transfer operator satisfies **‖λ‖ ≤ 1 − δ₀**, where
> **δ₀(β, N) = exp(−6 · actionBound β) = exp(−192·|β|·N⁴)**
> (the identity `actionBound β = |β| · 32N⁴` is proved in the
> module, `actionBound_eq_volume`; δ₀ ∈ (0, 1], δ₀ = 1 at
> β = 0). Corollary at the circle seat: `gapBoundU1_doeblin`,
> the first gap bound in the corpus whose δ is a *formula*.

Axiom sets on the headline, the compression, and the corollary:
exactly `[propext, Classical.choice, Quot.sound]`.

## The fence — the enemy, measured

δ₀ **decays exponentially in the four-volume**: at any fixed
β ≠ 0, inf over N of δ₀ is 0. This is not a defect of the
assembly; it is what a global action bound can see — all N⁴
plaquettes treated as adversarial, the locality a genuine
uniformity modulus needs erased by construction. This brick
*measures the enemy*: mission Step 2 of the ladder, done.
Step 3 (uniformity) needs a local input the corpus does not yet
own; nothing here touches it.

## Census effect

Strict 6,175 → **6,195**; attribute-inclusive 6,253 → **6,273**;
modules 210 → **211**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
