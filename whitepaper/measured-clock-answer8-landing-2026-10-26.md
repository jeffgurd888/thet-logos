# Q1′ at N = 8 — Answered FULL

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/MeasuredClockAnswer8.lean` (strict 3, defs 3, zero
`sorry`, zero `native_decide`; main-tree build green, 3,311 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.***

## The instance and the fit

The question `measuredClockQuestion 8 (clockObsErr 6)` — the same
ε as the N = 9 landing (the largest entered uncertainty) — is
proved with an **exact fit** (error 0).

The way through is a different fit, not a truncated N = 9. The
landed N = 9 construction's level squares `{0, 1, 1+obs m}` never
used their 0 level — the shared base 1 did all the work. Dropping
the offset anchor and anchoring on zero instead gives squares
`{0, obs₀, …, obs₆}` — exactly 8 levels — with β = 1, c = 1, and
each measured line read as `obs m − 0 = obs m`. It is legal
because every measured ratio is positive, so `√(obs m)` is a
genuine level.

## Per-instance discipline

Q1′ now stands proved at N = 9 and at N = 8. **Its live form moves
to N ≤ 7**, which neither landing decides: at N = 7 the
zero-anchored budget is exhausted (there is no spare zero level)
and the shared-base shape needs 8. The pigeonhole kill of the
uniform-over-all-spectra closure remains what it always was — a
kill of a *neighbor* statement, not of Q1′. `blockedQ1` is
untouched.

Axiom set: exactly `[propext, Classical.choice, Quot.sound]`.

## Census effect

Strict 5,939 → **5,942**; attribute-inclusive 6,017 → **6,020**;
modules 199 → **200**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
