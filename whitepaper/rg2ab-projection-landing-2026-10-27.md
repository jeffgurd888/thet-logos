# RG-2a + RG-2b — The Projection, Measured: Vacuous at the Flow Seat, Anchored at Zero

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/BlockingProjection.lean` (strict 14,
defs 2, zero placeholders, zero `native_decide`;
main-tree build green, 3,560 jobs, parent-verified;
both headlines' axiom sets exactly `[propext,
Classical.choice, Quot.sound]`). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** Both
bricks FULL. Dial 3's RG-curve absence is now a
*measured* absence at these seats — nothing here is a
flow, a curve, or a fixed point, and the module says
so on its face.*

## RG-2a — the vacuity, as a theorem

`plaquetteMatched_flow_vacuous` — at the RG-1 flow
seat, for every β > 0 and every β′ : ℝ, plaquette
matching **fails**: the coarse mean plaquette density
is identically 0 (landed `flow_coarse_density` — every
coarse plaquette is a commutator in an abelian group),
while the blocked density is strictly positive
(bridged from the fine expectation through `blockMap`
to the blocked measure's expectation of effAction/6,
bounded below at the singleton `flowV₂`). The
projection β′(β) therefore does not merely fail
uniqueness at this seat — **it does not exist** for
β > 0. The RG-2 scoping's finding is now theorem-grade.

## RG-2b — the anchor at zero

`plaquetteMatched_torus_zero` — at the torus seat,
β′(0) = 0: PlaquetteMatched holds at (0, 0), with both
β = 0 expectations 0 at the one-site seat. Beside it,
`gibbsExpectR_zero_meanPlaqDensity` assembles the
general β = 0 value 1 − Re(tr haarIntertwiner)/d at
no-fixed-shift lattices from the landed
`gibbsExpect_zero_plaquette`, and
`torus_anchor_is_coarse_gibbs` records that at β′ = 0
the blocked measure *is* the coarse Gibbs measure —
the one point where bookkeeping and equality coincide.

Two glosses in the scoping memo were corrected by the
build and are corrected on the verdict memo's first
lines: the matching definition needed its
ensemble-equality bridge stated and proved (done), and
the memo's "intertwiner trace on both sides" sentence
merged two seats — the trace evaluation lives at
no-fixed-shift lattices; at the one-site seat the value
is 0 by pointwise collapse. Both statements as proved
are the record.

## The fence

A projected β′(β), where it exists, is **bookkeeping**.
The standing kill rides the module: any projected
β′(β) presented as an RG flow without a
blocked-measure equality theorem is killed on sight.
RG-2's remaining priced work (RG-2c: existence at a
nonabelian small seat; RG-2d: the derivative kit)
stands in the queue behind the Dial-1 line.

## Census effect

Strict 6,492 → **6,506**; attribute-inclusive 6,570 →
**6,584**; modules 225 → **226**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
