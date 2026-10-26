# The Measured-Clock Question, Answered at Its Pre-Registered Instance

*Landing dossier, 2026-10-26. Module: `lean/ThetLogos/MeasuredClockAnswer.lean`
(108 lines, strict 6, defs 3, zero `sorry`, zero `native_decide`).
**Parts of the Clay Yang–Mills statement closed by this landing: 0.***

## What was answered

`MeasuredClockSpectrum.lean` posted the repaired question Q1′ as the
definition `measuredClockQuestion (N) (ε)`: does one thermal triple
reproduce the entered measured clock spectrum within tolerance ε? The
question owes its meaning to two choices — the fit size N and the
tolerance ε. This landing fixes both **before any proof attempt**,
pre-registered in the builder's progress record:

- **N = 9** — the scoping analysis's own threshold (M + 2 for M = 7
  entered ratios): exactly the size at which that analysis showed the
  question stops being open, via the explicit construction it named.
- **ε = clockObsErr 6 ≈ 8.87 × 10⁻¹²** — the largest of the seven
  entered published uncertainties, proved maximal inside the module
  (`clockObsErr_six_max`, entry by entry).

## The landing (FULL, at the instance)

`measuredClockAnswer : measuredClockQuestion 9 (clockObsErr 6 : ℝ)` —
proved with witnesses β = 1, c = 1, A = 1 and level squares
(0, 1, 1 + obs 0, …, 1 + obs 6), each measured line paired to its own
level against the shared base. **The fit is exact: the achieved error
is 0, which is ≤ ε with the whole tolerance to spare.** Axiom check on
the shipped text: exactly `[propext, Classical.choice, Quot.sound]`
for both proved declarations.

## The fences, printed on the module's own face

- This is a verdict on **this instance only**. N = 9 is precisely
  where the scoping analysis showed the construction always works —
  so the landing's real content is the **threshold itself**: below it
  the question is a question, at it the answer is a construction.
- **The question at N ≤ 8 remains open and untouched.** Nothing here
  shows a fixed-size spectrum of the framework's own matches the
  measured clocks; that is the live form of Q1′ now.
- The scoping analysis's neighbor kill (the uniform-over-all-spectra
  closure is false, by pigeonhole) is unchanged, and is **not** a kill
  of Q1′ — it never was.
- The original `blockedQ1` stands untouched, per the relabeling rule.

## Census effect

Strict 5,782 → **5,788**; attribute-inclusive 5,849 → **5,855**;
modules 187 → **188**; `sorry` placeholders unchanged at **6** (the
five T5 question-posts and Open Problem 2).

## Backers since last landing

No new backers inscribed in this interval; the roll stands as recorded
in `BACKERS.md`. Every gift is published with the proof stream, named
as the giver wishes, amounts only with the giver's permission — the
standing reciprocity of this house.
