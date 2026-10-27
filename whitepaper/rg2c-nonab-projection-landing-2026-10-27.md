# RG-2c — S4 FULL: The Projection Exists at the Nonabelian Seat (and Departs from Truth at Its Anchor)

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/BlockingProjectionNonab.lean`
(strict 84, defs 16; zero placeholders, zero
`native_decide`; main-tree build green, 3,565 jobs,
parent-verified; headline axiom sets exactly
`[propext, Classical.choice, Quot.sound]`). **Parts of
the Clay Yang–Mills statement closed by this landing:
0.** The plaquette-matched projection — proved
nonexistent at the abelian RG-1 seat (RG-2a) — is
proved to **exist, be unique, and be strictly
monotone** at a nonabelian seat. And its anchor
carries the line's sharpest honesty yet: at this seat
the projection departs from the measure truth at the
very first point.*

## The seat

`DihedralGroup 4` — chosen on the record: no S₃
representation exists anywhere in the tree, and S₃'s
standard representation needs √3/2 entries; D₄ is the
smallest nonabelian group whose faithful
2-dimensional unitary representation has entries in
{0, ±1} (rotations by 90°), so every trace is exactly
computable. The representation is built in-module;
the RG-1 geometry is reused verbatim. KC-2c-1 (seat
degeneracy) does not fire: the coarse density is
genuinely nonconstant (values 0, 1/3, 5/3 witnessed;
exactly 24 of 64 link pairs fail to commute).

## What is proved

- **Existence + uniqueness (S4).**
  `nb_matched_exists_unique` — for every β ≥ 0 there
  is a unique β′ with the mean plaquette densities
  matched. KC-2c-2 (second vacuity) does not occur:
  the fine value lies in (0, 1], strictly inside the
  coarse range (0, max A_c) with max A_c ≥ 5/3 —
  proved, not assumed.
- **Strict monotonicity.** `nb_matched_strict_mono` —
  β₁ < β₂ forces β₁′ < β₂′. Mechanism correction on
  the record: the scoping memo's route (the
  self-covariance derivative) was *not* used; strict
  antitonicity of the tilt mean is proved directly by
  the symmetrized-sum variance identity — the
  integrated form of the same covariance,
  derivative-free.
- **The anchor, corrected.** RG-2b's β′(0) = 0 was a
  property of *that* seat (intertwiner trace = d).
  Here the fine side at β = 0 equals 1, the coarse
  side at β′ = 0 equals 3/4 (Σ_V A_c(V) = 3072 over
  4096 coarse configurations, proved), so (0,0) does
  **not** match (`nb_not_matched_zero_zero`), every
  β′ matched to 0 is negative (`nb_anchor_neg`) —
  and yet the blocked measure *is* the coarse Gibbs
  measure at (0,0) (`nb_anchor_blocked`, by the
  general Stage-2 theorem). **The projection and the
  measure truth part company at the anchor itself.**
  Any future sentence calling β′(β) "the blocked
  coupling" dies against this landing.

## The fence

β′(β) at this seat is a statistic of a pair of
measures at one finite seat — proved to exist, proved
monotone, proved *not* to be the measure's own
coupling at the anchor. No flow, no curve, no
β-function, no iteration, no fixed point is defined
or implied (KC-2c-3 respected; the standing kill is
quoted on the module's face). Whether
BlockedGibbsIsCoarseGibbs fails at *this* seat for
β > 0 is explicitly untouched — RG-1 answered that
only at the abelian seat. NO CLAIM; dials 0/4.

## Census effect

Strict 6,567 → **6,651**; attribute-inclusive 6,645 →
**6,729**; modules 227 → **228**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
