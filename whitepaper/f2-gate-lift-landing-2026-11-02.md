# F2-GATE-LIFT — LANDING DOSSIER (2026-11-02)

**Brick:** F2-GATE-LIFT (engine) of the F2 weld line.
Parent-verified (main-tree targeted build green; CI axiom
fence PASS on the five headline lemmas, axioms exactly
`[propext, Classical.choice, Quot.sound]`).

**Module:** `lean/ThetLogos/Span3SeatSchurGateLift.lean`
(counted **strict 14 / defs 3**, zero sorrys). Not in the
root import list; verified by targeted build.

## What landed

The engine for the G2c discharge, three parts:

1. **Splice API.** `spliceTop` (def) — the named form of the
   configuration `fiberAvgTop` integrates over (top-layer
   links read the layer observable `u`, all other positive
   links read `z`); `fiberAvgTop_eq_spliceTop` (by `rfl`);
   `spliceTop_apply_embLayerTop`;
   `spliceTop_apply_of_forall_ne`.
2. **Disjointness at `4 ≤ N`.** `tauBot_spliceTop_of_four_le`:
   the bottom extraction of a top splice is the bottom
   extraction of the unspliced configuration, because the
   embeddings' time coordinates (`N/2 − 1 ≥ 1` vs `0`) are
   disjoint — the same disjointness the seat brick proved
   linkwise, lifted to the tauBot extraction. This is the
   exact point where the `N = 2` mechanism of GATE-2's kill
   (K-F2-2 at `N = 2`: the embeddings coincide and the fiber
   average returns `φ` verbatim) is excluded at `4 ≤ N`.
3. **The two gauge lifts.** `layerGaugeLift` (def): `γ` at
   the top time layer (`(x 0).val = N/2 − 1`), `1` elsewhere;
   `layerGaugeLiftMirror` (def): `γ` at the reflected top
   time layer (`(x 0).val = N/2`, via
   `reflSite_topSite_time_val`: `reflSite (topSite c)` has
   time value exactly `N/2`). For each lift: its values at
   the (reflected) top layer and at spatial shifts of it,
   the invariance of `tauBot` under the corresponding gauge
   action at the lifted function (`tauBot_gaugePosFun_lift`,
   `tauBot_gaugeMirrorPos_lift`), and the commutation of the
   splice with the gauge action
   (`spliceTop_gaugePosFun_lift`,
   `spliceTop_gaugeMirrorPos_lift`).

## Scope

This module decides neither G2c nor any gate item — it is
the engine; the discharge is the F2-GATE-2c brick. The
mirror half is genuinely needed: `mirrorGaugeAvg` is
invariant under the *mirror* action, not the pos action, so
the second conjunct of G2c cannot reuse the pos lift.

**NO CLAIM** — parts of any official Millennium statement
closed: 0. Dials: 0/4. No Gram factorization of `𝒜`
appears or is used.

## Census

Contribution +14 strict / +3 defs (combined gate-run census
after all three bricks: **12,745 strict / 13,270 total / 456
modules**, zero sorrys).

## BRIDGE-1

No registry interaction; registry unchanged.
