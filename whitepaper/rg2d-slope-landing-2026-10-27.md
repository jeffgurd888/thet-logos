# RG-2d — The Bookkeeping Statistic Has a Slope, and It Never Poles

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/BlockingProjectionDeriv.lean`
(strict 24, defs 3; zero placeholders, zero
`native_decide`; main-tree build green, 3,586 jobs,
parent-verified; headline axiom sets exactly
`[propext, Classical.choice, Quot.sound]`). **Parts of
the Clay Yang–Mills statement closed by this landing:
0.** The plaquette-matched projection β′(β) at the
nonabelian D₄ seat (RG-2c: exists, unique, strictly
monotone) is now proved **differentiable**, with its
slope given by an exact covariance ratio — and the
pre-registered pole kill (KD-1) is discharged by
proof: the variance in the denominator never
vanishes.*

## What is proved

- **The finite exponential-family kit (general).**
  For a finite configuration type and a nonconstant
  observable A, the tilt mean
  m(t) = ΣA e^{−tA}/Σe^{−tA} satisfies
  m′(t) = −tiltVar (the tilted variance is defined
  in-module, proved nonnegative, and proved
  **strictly positive at every tilt** — `tiltVar_pos`,
  full support plus nonconstancy), and m is smooth at
  every order (`tiltMean_contDiff`).
- **The matched slope.** At the D₄ seat, with
  `nbMatched` the choice function of RG-2c's
  existence theorem: β′(β₀) is differentiable on the
  domain (continuity by a strict-antitonicity squeeze,
  no general implicit-function theorem), and

  > **β′′(β₀) = 2 · tiltVar_fine(12β₀) /
  > tiltVar_coarse(6β′(β₀))** for β₀ ≥ 0,

  with `deriv_nbMatched` the proved statement and
  `nbMatched_slope_pos` its corollary: **the slope is
  strictly positive at every domain point**, the
  anchor included (one-sided, at tilt 0 the fine
  variance is the plain uniform variance).

## Kill conditions, on the record

- **KD-1 (pole at a degenerate tilt): discharged by
  proof.** Because `tiltVar_pos` holds at *every*
  tilt for any nonconstant observable, the slope's
  denominator never vanishes; no pole exists anywhere
  on the domain. The kill was pre-registered so this
  discharge is a theorem, not an assumption.
- **KD-2 (slope promoted to a β-function): respected.**
  The fence stands on the module's face: this is the
  derivative of a bookkeeping statistic at one finite
  seat — the same statistic RG-2c proved departs from
  the measure truth at its own anchor. No flow, no
  running, no fixed points of a slope equation, no
  critical exponents.

## The fence

The differential face of the RG line is now complete
at the two seats the line owns: vacuity at the
abelian seat (RG-1/RG-2a), existence/uniqueness/
monotonicity/slope at the nonabelian seat
(RG-2c/RG-2d). Nothing here is a blocked-measure
equality, a flow, or a continuum statement. NO CLAIM;
dials 0/4. Next on the ladder: LOC-3 (the polymer
partition function and the bridge to the layer
weight), then the finite core itself, 𝒜 ⪰ 0 on
gauge-invariant observables.

## Census effect

Strict 6,651 → **6,675**; attribute-inclusive 6,729 →
**6,753**; modules 228 → **229**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
