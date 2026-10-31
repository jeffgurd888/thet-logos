# SEP-0 — LANDED: the separation-operator miniature, registered (survived reduced; guards proved on its face)

**Date:** 2026-10-31 · **Brick:** SEP-0 (S), head of the
SEP line, per `scoping-separation-operator-2026-10-31.md`.
Module: `ThetLogos.ChargeSeparationPost`. **Verdict:
LANDED** (strict 6 / defs 8, parent-verified from disk;
main-tree build green, 3,245 jobs). Hard gate PUMP-0
satisfied and consumed (`χB`, `QB`, `popB`,
`chargePumpState`, `chargePumpTurnedWeight` — used, not
redefined).

**Fences: NO CLAIM. Parts of any official statement
closed: 0. Dials: 0/4.** **Claims registry: Card SEP**
is registered for this line; its verdict brick is
SEP-3 — no outcome class is reported until then.
K-PUMP-4/K-PUMP-5 carry over and bind this dossier.

## The reduction, on the face

Jeff's coinage names the line; the memo's honest
working label governs its content: **"a thermal state's
measured sector imbalance, and the driven step that
changes it."** `Qsep` is READ, not applied — it
separates nothing; the clock does every bit of the
moving; β sets the state's imbalance and the flux's
size.

## What is registered

- `Qsep := Matrix.diagonal (fun k => 2 * χB k − 1)`
  over PUMP-0's `χB`, with `Qsep = 2 • QB − 1` PROVED
  at registration (`chargeSeparation_Qsep_eq`), and
  its diagonal entries proved (−1, −1, +1, +1).
- `chargeSeparationExpectation` (the diagonal
  expectation ⟨Qsep⟩_w) and the registered identity
  Prop `⟨Qsep⟩_w = 2 * popB w − 1`.
- **Targets S1–S4, verbatim in substance:** S1 the
  static value (exp(−β/2) − 1)/(exp(−β/2) + 1)
  (= −tanh(β/4)), zero iff β = 0, strictly negative for
  β > 0; S2 the one-turn action Δ⟨Qsep⟩ = 2 × the
  PUMP-1 flux, with the factor-2 consistency clause
  inside the same statement; S3 the two-factor iff
  (a permutation drive separates the Gibbs family iff
  it fails sector preservation AND β ≠ 0); S4 the
  no-go corollaries (diagonal-unitary invariance,
  modular-flow stationarity, conservation + cycle
  return at operator level).
- **Face guards PROVED at registration (K-SEP-4):**
  both directions exhibited — the nonzero direction
  (S1's closed form, entries proved) and genuine
  failing cases: at β = 0 a clock turn changes the
  imbalance by exactly 0 (weights computed: 1/4 each),
  and the within-sector swap — a partition-preserving
  drive — changes no state's imbalance at any β,
  proved on Gibbs weights for every β.

## Named registration-form seams (not defects)

S2 is registered in expectation/weight form; its
operator-conjugation form is SEP-2's brick (gated on
PUMP-1), stated as such on the face. S4(ii) is
registered in normalized-state form; the transport from
the landed unnormalized `gibbsWeight_stationary` is
SEP-3's work. The composite form of everything in this
line is DEFERRED to Q7CR-3 — dependency, not
duplication.
**Census: 8,492 → 8,498 strict / 8,570 → 8,576
attribute-inclusive / 292 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
