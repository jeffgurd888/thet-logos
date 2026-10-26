# Variable-Axis Brick 4 — The Minimum-Axis Mirror Seat

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyMinAxis.lean` (strict 17, defs 8, zero
`sorry`, zero `native_decide`; main-tree build green, 3,231 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** Classical
mechanics, abstract body only, linearized level.*

## The formula correction — reported first, at full volume

The dispatch brief carried the rate with denominator `I₁·I₃`.
Deriving from the foundation's `eulerRHS` about `ω = (Ω, 0, 0)`
gives instead

  ν_min² = Ω² (I₃−I₁)(I₂−I₁) / (I₂·I₃)

— the denominator is the product of the two **non-spin** moments,
matching both seats already landed (the max seat's `stableRate`
has `I₁I₂` in the denominator: its two non-spin moments). Numeric
check at (I₁,I₂,I₃,Ω) = (1,2,3,1): the true rate is √(1/3); the
brief's formula gives √(2/3) and is wrong. The error was the
parent's, in the brief; the builder's derivation caught it before
anything was registered, and the corrected formula is what the
module proves. The min seat **is** stable — the correction is a
formula fix, not a stability kill.

## What landed

The min-axis seat (`minCoeffA/B`, `minRate` with
`minRate_sq : ν² = −a·b`, exhibited modes solving the transverse
system, boundedness), **both modes periodic** with
`P_min = 2π/ν_min`, and over the variable family `(I₁, s, I₃)`:

- `Pmin_tendsto_atTop` — as `s ↓ I₁`, `P_min(s) → ∞`;
- `Pmin_mul_sqrt_tendsto` — `P_min(s)·√(s−I₁) →
  2π/(Ω·√((I₃−I₁)/(I₁·I₃)))`: inverse square root in the closing
  gap at the lower neighbor, mirroring Brick 1's law at the upper.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## State of the variable-axis program

Bricks 1–4 close the program's buildable content: both stable
seats with their periods and divergence laws, the rank-crossing
sign switch with its crossing corollary, and the honest
time-varying-moments dynamics with its corrected laws. Remaining
open, named and fenced: the nonlinear separatrix period (elliptic
machinery absent from the pin — L+, later program) and the
polhode-portrait topology statement (later brick per the scoping).

## Census effect

Strict 5,922 → **5,939**; attribute-inclusive 6,000 → **6,017**;
modules 198 → **199**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
