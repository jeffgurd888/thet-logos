# General κ₄^dep — Closed Form FULL; the Sign Reduced to One Named Component

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/PlaneCrossingBeta4.lean`
(strict 36, defs 8; zero placeholders, zero
`native_decide`; main-tree build green, 3,447 jobs,
parent-verified; headline axiom sets exactly
`[propext, Classical.choice, Quot.sound]`). **Parts of
the Clay Yang–Mills statement closed by this landing:
0.** The β⁴ dependent coefficient of the layer kernel
now has an exact closed form at general (G, ρ). Its
sign does not: the sign question is reduced, by proof,
to a single named functional whose evaluation needs an
object the tree does not yet own. PARTIAL is the
verdict, at the seam the brick pre-registered.*

## The closed form (FULL, T1)

At general (G, ρ), Even N, 3 ≤ N, ρ continuous, the
β⁴ Taylor coefficient of `layerKernel` splits exactly.
The constant part is the cumulant over partitions of
the distinct-column support, in the owned moment
vocabulary (A_j = `densMomentValue j`, B = 1 − e₁/d,
M = `colCount N`):

κ₄^const = M·A₄ + 4M(M−1)·A₃·B + 3M(M−1)·A₂²
  + 6M(M−1)(M−2)·A₂·B² + M(M−1)(M−2)(M−3)·B⁴

The pattern values at order 4 are V₄ = A₄,
V₃₁ = A₃·B, V₂₂ = A₂² — the support-2 pattern (2,2)
is CONSTANT, not dependent; the probe's assembly
correction is confirmed at general (G, ρ), not just
at its two seats — V₂₁₁ = A₂·B², and
V₁₁₁₁ = B⁴ + d⁻⁴(quadReMoment C − e₁⁴).

The dependent part is one sum (`kappa4dep_eq`):

κ₄^dep = d⁻⁴ · Σ_{C ∈ primitiveQuads}
  (quadReMoment C u u′ − e₁⁴)

where `quadReMoment C` is the stratum integral of the
product of the column real parts over the 4-subset C,
and a quad is *primitive* when every column's both
sites are shared with another column of the quad. The
engine is `excess_eq_zero_of_not_primitive`: at a
non-primitive quad a private site integrates its
column out against e₁, so the excess vanishes; the
counting bridge
(`nested_quadruple_sum_eq`: ordered distinct
quadruples = 24 · 4-subsets) assembles the total.

## The sign (PARTIAL, at the pre-registered seam)

`kappa4dep_sign_reduction` states the reduction: the
sign of κ₄^dep is the sign of

Φ(u, u′) := Σ_{C ∈ primitiveQuads}
  (quadReMoment C u u′ − e₁⁴).

Plaquette telescoping predicts Φ ≥ 0 on the diagonal
— each primitive quad contributing a sum of squares
of plaquette-loop functionals — and both probed seats
conform, with margin exactly zero (κ₄ probe dossier,
same date). But the telescoping evaluation of
`quadReMoment` at a primitive quad passes through a
ρ⊗ρ projector integral — Peter–Weyl orthogonality of
the matrix coefficients of `repMatrix` — **which does
not exist in the tree**. The seats were evaluated from
their character tables; no seat-independent sign is
claimed. K-K4G-1 did not fire (no new seat was
specialized by this brick, so no certified negative
direction exists from it). K-K4G-2 respected (the
observable space was not widened; every statement
lives on the layer kernel's own (u, u′) arguments).

## The two open items, named

1. **The sign of Φ.** Its final address is now a
   single missing object: the ρ⊗ρ projector integral
   (Peter–Weyl orthogonality for `repMatrix`). Build
   that, and the telescoping evaluation — and with it
   the sign at order β⁴ — becomes a priced brick
   instead of a shape.
2. **Primitive = plaquette.** The closed form sums
   over primitive quads (the dep-set criterion). The
   further identification of primitive quads with
   unit plaquettes at 5 ≤ N (excluding N | 4 wrap
   lines) is a combinatorial refinement NOT landed
   here; it is recorded as open, not asserted.

## Fences

Finite-volume lattice algebra about the β⁴
coefficient of the finite layer kernel. Not a
statement about 𝒜 ⪰ 0 in the large: the zero margins
at both probed seats say the dependent form, even
where PSD, carries no perturbative cushion, and
order-5/6 negativity at some seat remains a live
possibility. Not a continuum statement, not a gravity
statement. NO CLAIM; dials 0/4, unchanged.

Census effect: 6,743 → **6,779 strict** /
6,821 → **6,857 attribute-inclusive** / 231 → **232
modules**; the seven quarantined placeholders are
unchanged.

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
