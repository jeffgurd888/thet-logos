# Q1′′ Brick D — The Decision at N = 7: NO FIT, at Theorem Grade

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/MeasuredClockDecision7.lean` (strict
35, defs 8, 1,037 lines, zero `sorry`, zero
`native_decide`; main-tree build green, 3,354 jobs,
parent-verified). **Parts of the Clay Yang–Mills
statement closed by this landing: 0.** The clock
question's final honest shape is now complete at every
posed instance: fits at N = 8 and N = 9 (exact), an
ill-posed original (receipted), and — here — a proved
kill at N = 7 for the correctly re-posed question.*

## The headline

> **`measuredClockNoFit7`** — `¬ measuredClockQuestion2 7`:
> Q1′′ has **no fit at N = 7**. Axiom set exactly
> `[propext, Classical.choice, Quot.sound]`.

The proof is the scoping's skeleton, formalized whole:
a fit is a graph of 7 line-edges on 7 vertices;
self-loops and repeated pairs are excluded by the data;
component counting forces a component with at least as
many edges as vertices; a spanning tree plus one extra
edge closes a trail; telescoping around the trail forces
a signed sum of the entered ratios to vanish within the
accumulated tolerances (< 10⁻¹¹). The finite check then
closes it: patterns avoiding line 6 are rescaled to ℤ
and discharged by kernel decision over all 729
coefficient functions (kernel `decide` on ℚ goals stalls
in this pin — the integer rescaling is the route);
patterns using line 6 fall to the triangle inequality
against the Sr/Cs magnitude (> 46,681). The margin is
the enumeration's: the closest signed sum misses by
≈ 0.02342881 against a tolerance scale of ~10⁻¹¹ —
**thirteen orders of magnitude**, in Lean as in the
computation. This is not a near miss dressed as a kill.

## The secondary deliverable

**`measuredClockAnswer2_8`** and
**`measuredClockAnswer2_9`** — Q1′′ holds at N = 8 and
N = 9, rebuilt from the exported square identities at
β = 1 with residual exactly 0 per line. This discharges
Brick B's flag: the "answered for free" point is now
theorem-grade for Q1′′ itself, not prose about Q1′
witnesses that could not be extracted.

## The ledger, corrected in one place

With this landing, the clock line reads clean end to
end: Q1′ as posed was ill-posed (Brick A's receipt) and
its N = 8/N = 9 theorems stand as exact c = 1 fits to
that definition; Q1′′, the correctly posed question, is
**decided at every instance it was posed**: yes at 8 and
9, no at 7. Nothing is claimed for N ≤ 6 — not asked,
not decided. The clock table remains T4 input; all of
this answers the clock question only. NO CLAIM; dials
0/4.

## Census effect

Strict 6,407 → **6,442**; attribute-inclusive 6,485 →
**6,520**; modules 218 → **219**; `sorry` placeholders
unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
