# Variable-Axis Brick 2 — The Rank-Crossing Switch

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyRankSwitch.lean` (strict 27, defs 8, zero
`sorry`, zero `native_decide`; main-tree build green, 3,229 jobs,
parent-verified on the shipped text). Scoped in
routeb-general-scratch/varaxis-scoping-2026-10-26 §B. **Parts of
the Clay Yang–Mills statement closed by this landing: 0.**
Classical mechanics, abstract body only; the Earth application of
this line was KILLED on 2026-10-25 and is not revived.*

## What landed

The general-axis frozen linearization package (`linCoeffI`,
`linCoeffJ`, `rankCore`, `rankQ`, with `qₖ` proved equal to the
coefficient product), and the **sign theorem in all three cases**,
for all three labeled axes:

- `qₖ > 0` **iff** `Iₖ` is strictly between the other two moments
  — the spin axis is intermediate: hyperbolic, growing;
- `qₖ = 0` **iff** `Iₖ` ties a neighbor — the degenerate
  linearization;
- `qₖ < 0` **iff** `Iₖ` is strictly outside — extremal:
  elliptic, oscillatory.

Cross-checks against the landed seats: at axis 1, `qₖ` is the
foundation's `linCoeffA · linCoeffB` (the growth product); at axis 2
under `I₁<I₂<I₃`, `qₖ = −(stableRate)²` — the switch's sign agrees
with both seats the foundation already owned.

**The crossing corollary** (`rankQ_crossing`, by IVT): along any
continuous path of positive labeled moments carrying axis `k` from
strictly intermediate to strictly extremal, there is a crossing
time where `Iₖ` exactly ties a neighbor and `qₖ` passes from
positive to negative. An affine-path instance is included. That —
not a physical axis jumping — is the rank-crossing switch, in
theorem form.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Fences

**Frozen coefficients only.** This brick proves what the
linearization's *type* does at a crossing; it says nothing about a
trajectory while the moments are actually changing. That is
Brick 3's different model — the corrected equations with their
`−İω/I` terms, the energy law `dT/dt = −½ Σ İᵢωᵢ²`, and `|L|²`
surviving only through the corrected dynamics — separately priced,
not yet built.

## Census effect

Strict 5,885 → **5,912**; attribute-inclusive 5,955 → **5,982**;
modules 196 → **197**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
