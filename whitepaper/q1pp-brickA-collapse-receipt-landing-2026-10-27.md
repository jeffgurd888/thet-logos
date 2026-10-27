# Q1′′ Brick A — The Collapse Receipt: Q1′ As Posed Answers Itself at Every N

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/MeasuredClockCollapse.lean` (strict 4,
defs 0, zero `sorry`, zero `native_decide`; main-tree
build green, parent-verified). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** This
dossier is a self-correction artifact, filed at the same
volume as a win: the clock question Q1′, as posed, is
**ill-posed** — and that is now a theorem, not an
opinion.*

## The receipt

> **`measuredClockQuestion_trivial`** — for every N with
> `[NeZero N]`, `measuredClockQuestion N (clockObsErr 6)`
> holds, by the exact witness β = 1, lam ≡ 0,
> f ≡ (0, 0), c = 19/10¹⁷. Every frequency difference is
> 0, and c·obs_m ≤ c·obs_6 = clockObsErr 6 — the last
> equality being the data entry's own exact rational
> identity (`clockObsErr_six_eq`, verified from the
> source, not assumed).

> **`measuredClockQuestion_of_pos`** — the general form:
> for **every ε > 0**, the posed question holds at every
> N, by the same construction with c = ε/(2·obs₆).

Axiom sets: exactly `[propext, Classical.choice,
Quot.sound]` on both. The disease is structural: the
posed existential carries an **absolute** tolerance
against a target `c · obs` that scales with a **free**
constant c. Shrink c and the target shrinks into the
tolerance with a zero spectrum. The definition answers
itself; it has no N-content at all.

## What this does and does not touch

- The **N = 9 and N = 8 theorems STAND.** They are exact,
  nondegenerate fits at c = 1, and those witnesses remain
  the meaningful content of the clock line.
- What **falls** is the framing around them: "below the
  threshold the question is a question" is false for the
  definition as posted. The threshold analysis tracked the
  exact-fit constructions, not the quantified statement.
  The earlier dossiers' framing is corrected by this
  receipt; the theorems in them are not.
- `blockedQ1` is untouched (the relabeling rule). The
  live question proceeds as **Q1′′** — a new entry with c
  eliminated and per-line tolerances — whose N = 7
  decision is a finite exact problem (Brick C's
  enumeration already returned NO FIT at computation
  grade; Brick D will decide it in Lean).

## Census effect

Strict 6,402 → **6,406**; attribute-inclusive 6,480 →
**6,484**; modules 216 → **217**; `sorry` placeholders
unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
