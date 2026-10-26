# The Polhode Portrait — Band Separation and the Saddle Passage

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyPortrait.lean` (strict 30, defs 4, zero
`sorry`, zero `native_decide`; main-tree build green, 3,231 jobs,
parent-verified on the shipped text). Scoped in
routeb-general-scratch/nonlinear-rigid-scoping-2026-10-26, built on
N0's landed forms. **Parts of the Clay Yang–Mills statement closed
by this landing: 0.** Classical mechanics, abstract body only,
frozen coefficients.*

## What landed

- **Band separation, both bands.** In the top band, `M₁` never
  vanishes on the polhode level set 𝒫_E: the level set is covered
  by the two disjoint half-spaces `M₁ > 0` and `M₁ < 0`, **both
  nonempty** (points exhibited), and `topBand_no_path_crossing` —
  no curve inside 𝒫_E joins the two pieces (IVT). The bottom band
  is symmetric in `M₃`.
- **The saddle passage.** `sep_saddle_set` and
  `sep_path_through_saddle`: at E = E_sep, every curve inside the
  level set from `M₁ > 0` to `M₁ < 0` passes through a saddle
  `(0, ±√Λ, 0)`. The separatrix is exactly where the two sides
  touch, and the touching points are named.
- **The crossing corollary.** `saddle_axis_rankQ_signs`: the
  saddle's axis (index 1) is the *unique* labeled axis with
  `rankQ > 0` — Brick 2's trichotomy read on the portrait — and
  `saddle_label_exchange` re-exports the rank-crossing theorem
  with the portrait reading: after a crossing, the saddle attaches
  to a different labeled axis.

Everything consumes N0's corrected (decreasing/decreasing) affine
forms; the scoping memo's superseded §0 wording was never used.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Fences

The exact component *count* of the level sets is the fenced L
tail and was not attempted — separation and the saddle passage
are what this brick claims. Next in the scoping's order: the
period stages N1 (quadrature + finiteness) and N2 (the
log-divergence headline), then the optional two-sided rate N3;
the dynamics identification (N4) stays deferred, so the period
theorems are honestly about the *quadrature* period.

## Census effect

Strict 6,004 → **6,034**; attribute-inclusive 6,082 → **6,112**;
modules 203 → **204**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
