# Period Stage N2 — The Separatrix Log-Divergence

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyPeriodDiv.lean` (strict 12, defs 3, zero
`sorry`, zero `native_decide`; main-tree build green, 3,509 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** Classical
mechanics, abstract body only, frozen coefficients.*

## What landed

The quadrature period diverges logarithmically at the separatrix,
from both sides, with explicit constants:

- **Comparison core** (`periodQuad_ge_log_aux`): on the fixed
  window near the saddle, the integrand is bounded below by
  const·(g + v)⁻¹, where g is the roots gap; FTC against
  `Real.log` gives `periodQuad ≥ divCoeff·(log(g + Λ/2) − log g)`.
- **Quantitative bound, both bands** (`periodQuad_ge_log_top/bot`,
  `periodQuad_ge_abs_log_top/bot`): with τ = |E − E_sep| and the
  exact gap identity g = κτ,
  `periodQuad ≥ divCoeff·log(1 + B/τ)`, hence the classical form
  `periodQuad ≥ c₁·|log τ| − c₂` for τ ≤ 1, with
  c₁ = divCoeff = (2/quadCoeff)·(Λ·slope1·slope3)^(−1/2) > 0
  explicit and c₂ = divCoeff·|log B|.
- **Divergence** (`periodQuad_tendsto_atTop_top/bot`):
  periodQuad(E) → ∞ as E → E_sep from above and from below.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## The two freezes, kept distinct — on the record

This house now owns two period-divergence theorems about a
spinning body, and they are **different theorems**: Brick 1's
*linearized* period diverges like an inverse square root as a
*moment* approaches its neighbor (a parameter path); N2's
*nonlinear quadrature* period diverges like a logarithm as the
*energy* approaches the separatrix at fixed moments (a level
path). They are never to be merged in prose.

## Fences

Quadrature period throughout — the trajectory identification is
stage N4, deferred; the optional two-sided Θ-rate (N3) is the
only remaining priced stage of this program besides N4 and the
portrait's component-count L tail.

## Census effect

Strict 6,038 → **6,050**; attribute-inclusive 6,116 → **6,128**;
modules 205 → **206**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
