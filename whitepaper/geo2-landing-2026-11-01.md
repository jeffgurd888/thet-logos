# GR-GEO-2 LANDING — 2026-11-01

## The Green weld: FULL seat values; the shadow instance HOLDS at its smallest seat (working label: GR-GEO line)

**Module:** `ThetLogos.LayerCubeGreenKernel` — strict 79 /
defs 15, parent-verified (independent count, main-tree
build, headline axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,570 strict / 10,647 total /
358 modules, zero sorrys.**

**BRIDGE-1: BR1-024 — PASS, 19/19** (independent exact
reimplementation; registry:
`whitepaper/cross-check-registry.md`).

**Named seat, on the module's face, named in advance and
never re-named (K-GR-STAB respected): N = 2, m = 1,
C = 1/2.**

## What was delivered

- **`greenKernel m` at general N, for named m > 0:**
  `⟪e_ℓ, (maxwellOp N + m²)⁻¹ e_ℓ'⟫`, with invertibility
  **proved, never assumed** — MAX-2's M1 gives the Maxwell
  form nonnegative, so the m² shift is strictly positive
  on nonzero angles, hence injective, hence bijective in
  finite dimension (`shiftedOp_injective`); the kernel is
  built from that linear equiv. Symmetry
  (`greenKernel_symm`) and diagonal positivity
  (`greenKernel_diag_nonneg`) are proved from the shifted
  form.
- **Seat values at N = 2, m = 1** — computed via an exact
  Fourier candidate on the ZMod 2 cube verified against
  the operator itself (`shiftedOp_greenCand`,
  `greenKernel_seat_formula`), and classified
  (`greenKernel_seat_cases`). The Lean-proved value sets
  by linkGeoDist class r:

  | r | kernel values |
  |---|---|
  | 0 | 293/585 (directions equal), 11/117 (directions differ) |
  | 1 | 22/117, −8/65, −11/117, 2/117 |
  | 2 | 8/65, 4/117, 11/117, −2/117 |
  | 3 | 32/585 (directions equal), 2/117 (directions differ) |

  Every diagonal entry is 293/585 (`greenKernel_seat_diag`).
- **The predicate instance, as a seat fact:**
  `PoseObjFShadow 2 (greenKernel 2 1) (1/2)` **HOLDS at
  this seat** (`poseObjFShadow_seat`) — per-class margins:
  r=1 max 22/117 ≤ 1/2; r=2 max 8/65 ≤ 1/8 (64 against 65
  — one part in 65 of slack); r=3 max 32/585 ≤ 1/18
  (576 against 585). The tightness at r=2 and r=3 is part
  of the record: the comparison nearly fails at this seat
  and does not.

## The ceiling, honored exactly

This is the instance outcome at the named smallest seat,
**not a falloff-law verdict in either direction**. The
law — the comparison at seats beyond the smallest,
against the pin's registered form — remains a future
candidate brick's burden (a NEW entry, separately scoped;
its prior, on the vocabulary memo's face, is death by
finite-size/torus effects). One precision disclosure:
the finer pattern split inside classes r=1 and r=2 (which
direction is the displacement axis) is confirmed by the
BRIDGE-1 exact computation but is not itself a Lean
theorem; the Lean-proved content is the per-class value
sets above.

**Price honesty:** the module landed at 79 strict against
the brick's 25–45 estimate — the excess is the
operator-action/doubling/family machinery needed to
verify the Fourier candidate against the operator rather
than assume it. The estimate was wrong, the landing is
FULL, and the difference is disclosed here rather than
absorbed silently.

## What this landing is not

A finite matrix inverse on a chosen finite operator, at
one named seat — instrument bookkeeping. Not a
Green's function of any spacetime, not a falloff law, not
a gravity object. The chair's state after tonight's
vocabulary program is the program's own §0 ceiling, now
reached: **the corpus can receive a statable PoseObjF
candidate** — the predicate exists, its smallest instance
is decided, and the law's burden sits exactly where the
memo put it. Dial 2 = 0; NO CLAIM; dials 0/4.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
