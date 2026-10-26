# Variable-Axis Brick 1 — Linearized Period and Its Divergence

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyPeriod.lean` (strict 10,
attribute-inclusive 13, defs 3, zero `sorry`, zero `native_decide`;
main-tree build green, 3,230 jobs, parent-verified on the shipped
text). Scoped in routeb-general-scratch/varaxis-scoping-2026-10-26.
**Parts of the Clay Yang–Mills statement closed by this landing:
0.** This is classical rigid-body mechanics at T1 formalization —
and the Earth application of this line was KILLED on 2026-10-25
(H ≈ 1/305, wrong sign) and is not revived here: the body in this
module is abstract.*

## What landed

Fix `0 < I₁ < I₃`, `Ω > 0`, and let `b_s` be the body with moments
`(I₁, s, I₃)` for `s ∈ (I₁, I₃)`, with `Pmax(s) = 2π / stableRate`:

- **Both stable modes are periodic with period `Pmax(s)`**
  (`modeXs_periodic_varBody`, `modeYs_periodic_varBody`) — the
  foundation's `stableRate` is confirmed as their common angular
  frequency. (Minimality of the period was not registered and is
  not asserted.)
- **The period diverges** as the middle moment climbs to the
  maximum: `Pmax_tendsto_atTop` — `Tendsto Pmax (𝓝[<] I₃) atTop`.
- **At the exact rate**: `Pmax_mul_sqrt_tendsto` —
  `Pmax(s)·√(I₃−s) → 2π / (Ω·√((I₃−I₁)/(I₁·I₃)))`: inverse
  square root in the closing gap, constant named.

All headlines' axiom sets: exactly
`[propext, Classical.choice, Quot.sound]`.

## Fences

The divergence is middle-moment ↑ maximum-moment, about the
maximum axis, at the *linearized* level only. Nothing nonlinear is
claimed; the full separatrix period is elliptic machinery the pin
does not carry (later program, L+). The intermediate axis's `1/γ`
is an e-folding **timescale**, never a period. Still open in this
program, as separate bricks: the frozen rank-crossing sign switch
(the product `q_k`: positive exactly when the spin axis is
intermediate), and the honest time-varying-moments dynamics (with
its `−İω/I` corrections and the energy law
`dT/dt = −½ Σ İᵢωᵢ²`).

## Census effect

Strict 5,875 → **5,885**; attribute-inclusive 5,942 → **5,955**;
modules 195 → **196**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
