# WindingRing — winding numbers on a finite phase ring

**Verdict: STANDS WHOLE (T1).** Compiled green 2026-10-21
(`lake build ThetLogos.WindingRing`, 3,117 jobs, 0 errors, 0 warnings),
parent-verified on the exact shipped text: `.olean` present, strict
recount 14, placeholder census 0, axioms on the five checked headline
theorems standard only (`propext`, `Classical.choice`, `Quot.sound` —
no `sorryAx`).

Module: `lean/ThetLogos/WindingRing.lean` — 14 strict theorems/lemmas,
3 defs, 0 `@[simp]` declarations. Program totals move
**3,323 → 3,337 strict** (3,363 → 3,377 attribute-inclusive),
**117 → 118 counted modules**.

## What it is

Commissioned by Jeff 2026-10-21, out of the sitting on strings, knots,
light-as-wiggling-heat, and heat-separating-charge. The audit of that
weave named three missing pieces: a single stage, the exchange rates,
and the SLIP — the event that lets a conserved quantity change. This
brick builds the smallest honest piece of that country: winding as
integer bookkeeping on a finite ring, and the slip as the one event
that changes it.

The stage is a finite ring of `N` edges. A configuration is a step
pattern `a : Fin N → ℤ` (integer phase steps, in ticks); `M : ℕ` is
ticks per full turn. When `M` divides the total step count, the
winding number is the exact quotient `(∑ i, a i) / M` in `ℤ`.
Integer bookkeeping only: no real angles, no circle API, no analysis.

## What is proved

Pattern level:
- `winding_zero` — the zero pattern winds 0.
- `winding_add` — compound winding is addition: `w(a + b) = w a + w b`
  (each summand's divisibility assumed separately).
- `winding_neg` — `w(-a) = -w a`.
- `sum_slip` — one edge gaining exactly one full turn of ticks raises
  the period sum by exactly `M`.
- `winding_slip` — hence winding rises by **exactly 1** per slip
  (`winding_slip_twice`: two slips, +2).
- `slip_modEq` — the headline: after a slip, the pattern agrees with
  the original **modulo M at every edge**. The visible phases are
  unchanged everywhere; only the global winding sector moved. Winding
  is real and locally invisible — the discrete shadow of flux
  quantization, and of FluxTwist's 2π periodicity (T1, in-corpus).
- `counterexample` — the pattern `(1, -1)` on a 2-ring has winding
  **0** and is **not zero**. The converse of `winding_zero` is false,
  killed inside the brick: winding zero does not mean trivial.

Lift level (the flow):
- `lift_steps_telescope` — the steps of a lift `u : ℤ → ℤ` telescope:
  the period sum is `u(N) - u(0)`.
- `lift_period_sum` — the pattern sum of a lift's steps equals that
  same difference (bridge between the two levels).
- `regauge_period_eq`, `winding_regauge` — re-gauging a lift by any
  integer-periodic `p` cannot move the winding. Winding changes
  **only** at slip events; the invariance/event pair is complete.

## Verification record

- Drafted 2026-10-21 under an UNVERIFIED header; compile run 1 red
  (one error), repaired, run 3 clean green; header flipped to
  VERIFIED only after the parent re-ran the targeted build on the
  exact shipped text (green, 3,117/3,117).
- One repair, in the open: `winding_neg`'s draft proof
  (`Finset.sum_neg_distrib` under bare `exact`) failed with a stuck
  typeclass codomain; replaced by an `eq_neg_of_add_eq_zero_left`
  argument. Proof body only — no statement, name, or fence changed.
  The draft's other six named risks compiled as written.
- Axiom audit (`#print axioms`): `winding_slip`, `winding_regauge`,
  `counterexample`, `winding_add` depend on exactly
  `[propext, Classical.choice, Quot.sound]`; `slip_modEq` on
  `[propext, Quot.sound]`. No `sorryAx` anywhere.

## Fences (on the module's face)

- NOT an Abrikosov vortex: no manifold, no order-parameter field, no
  broken phase, no core energy, no vortex dynamics.
- No knots: a ring carries no crossings; winding here is `ℤ`
  bookkeeping (π₁ of the circle), not braid or knot data.
- "Flow" means re-gauging invariance of a lift — not a time-evolution
  equation, not a PDE, not modular flow (kinship only: both are
  phase bookkeeping).
- Nothing about Yang–Mills, the continuum, or any Millennium
  statement. Cabinet tier: a finite miniature, honestly fenced.
