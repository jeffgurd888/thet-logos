# Q1′′ Brick B — The Re-Posed Clock Question, Entered

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/MeasuredClockQuestion2.lean` (strict 1,
defs 1, 121 lines, zero `sorry`, zero `native_decide`;
main-tree build green, parent-verified). **Parts of the
Clay Yang–Mills statement closed by this landing: 0.**
Definitions only: nothing about any N is decided here.
The decision belongs to Brick D.*

## The entry

> **`measuredClockQuestion2 (N) [NeZero N]`** — there
> exist β > 0, a spectrum `lam : Fin N → ℝ`, and an
> assignment `f : Fin 7 → Fin N × Fin N` such that every
> line lands within **its own entered tolerance**:
> |modularFreqDiff β lam (f m).1 (f m).2 − clockObs m|
> ≤ clockObsErr m.

The free scale `c` of Q1′ is eliminated — absorbed into
the spectrum, equivalently fixed at 1 — because the
collapse receipt (`MeasuredClockCollapse`, Brick A)
proved the posed Q1′ existential true at every N for
every ε > 0: an absolute tolerance against a freely
scaling target answers itself. Q1′′ is a **new entry**
under the relabeling rule; Q1′ stands as posted, receipt
attached. On this module's face: the graph reading (a
fit is 7 edges on N vertices; the only obstructions are
cycle sums), and the fence — the clock table is T4
input, and a verdict on Q1′′ answers the clock question
only. NO CLAIM.

## One flag, carried openly

The scoping said Q1′′ at N = 8 and N = 9 is "answered
for free" by the existing exact fits. Morally true —
those fits are exact at c = 1 with error 0 — but **not**
a free corollary in Lean: the exact-fit equalities live
as local steps inside the Q1′ proofs, and the Q1′
existential's witnesses cannot be extracted from its
theorems. This brick therefore states the 8/9 point as
prose context only, and Brick D inherits the small task
of re-deriving the c = 1 witnesses as Q1′′ instances if
it wants them at theorem grade. Recorded here so the
gap between the prose and the proof is on the books.

## Census effect

Strict 6,406 → **6,407**; attribute-inclusive 6,484 →
**6,485**; modules 217 → **218**; `sorry` placeholders
unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
