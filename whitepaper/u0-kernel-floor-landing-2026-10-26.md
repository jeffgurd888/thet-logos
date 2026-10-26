# Brick U-0 — The Pointwise Kernel Floor

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/UniformityDensityBound.lean` (strict 3, zero
`sorry`, zero `native_decide`; main-tree build green, 3,574 jobs,
parent-verified on the shipped text; headline axiom set exactly
`[propext, Classical.choice, Quot.sound]`). Scoped in
routeb-general-scratch/uniformity-attack-scoping-2026-10-26 §5.
**Parts of the Clay Yang–Mills statement closed by this landing:
0.***

## What landed

At general (G, ρ), for **all real β**, 2 ≤ N, and every product
point p:

- **`jDensity_toReal_ge`** — the missing lower companion to the
  landed `jDensity_toReal_le`: the two-slice density read as a
  real is at least `exp(−2·actionBound β)`, from `jDensity_ge` by
  monotonicity of `ENNReal.toReal`.
- **`kReal_ge` (U-0 itself)** —
  `exp(−6·actionBound β) ≤ kReal μG ρ hN2 β p`, pointwise, no a.e.
  weakening, no seat restriction: the exact dual of the landed
  `kReal_le`, assembled from the numerator's floor and the two
  marginal ceilings in `sliceDensity_toReal_mem`.
- **`hdKernel_re_ge`** — the same floor for the real value of the
  candidate HDen kernel, the casting form the scoping registered.

The memo's constant survived contact with the landed chain
unchanged: −2A from the numerator, +2A twice from the
denominator, −6A total. No discrepancy to report.

## Fences — read before citing

**This is a density bound only. It states and implies no
spectral gap and no uniformity.** The Doeblin candidate this
floor would feed, δ₀(β, N) = exp(−6·actionBound β) =
exp(−192βN⁴) at β > 0, **decays exponentially in N** at every
fixed β > 0 — its infimum over N is 0 and it yields **no (U-vol)
regime**, exactly as the scoping recorded before this brick was
fired. Coupling the floor to a gap is the scoping's separate
brick Q1 (priced M); a genuine uniformity theorem remains
L+ / research program, because the global action bound erases
the locality a real modulus would need. Uniformity across N
remains OPEN, untouched by this landing.

## Census effect

Strict 5,942 → **5,945**; attribute-inclusive 6,020 → **6,023**;
modules 200 → **201**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
