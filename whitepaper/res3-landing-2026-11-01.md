# RES-3 LANDING DOSSIER — 2026-11-01

**Item:** RES-3 (ratios and octaves), per the ratified scoping
memo (`scoping-resonance-2026-10-30.md`, §2(b)/(c)) and the
coordinator pack (`pack-res-3.md`). RES-0/1/2 vocabulary cited,
never forked.

**Status: FULL — all six clauses**, with one memo imprecision
caught and receipted at full rank (below).

**Artifact:** `lean/ThetLogos/SumResonanceRatios.lean` —
strict 26, defs 3 (in the memo's 16–28 band). Verified by the
coordinator in the main tree (build green, 3120 jobs); all 15
headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What landed

- **(b1)** Unison is overlap: the fenced count at ratio (1,1) is
  the inner product of the multiplicity functions over the
  nonzero tones, and every ratio is that one theorem after
  scaling (`resCount_eq_sum_scaled`) — stated once, used
  everywhere, as registered.
- **(b2)** The zero-fence lemma: `resCountAll p q a b =
  resCount p q a b + multA a 0 * multA b 0`. **Correction on the
  record:** the memo's "at any ratio" is FALSE at p = 0 — a zero
  a-tone then pairs with every b-tone, contributing
  `multA a 0 * n`, not `* multA b 0`. The lemma therefore
  carries p ≠ 0 (every named ratio — (1,1), (2,1), (3,2) —
  satisfies it), and the p = 0 anomaly is proved separately at
  full rank (`resCountAll_zero_left`) with the reason on the
  module's face. (b1)'s ratio form likewise carries q ≠ 0. The
  memo's statement is corrected by the landing, not silently
  narrowed.
- **(b3)** The geometric ladder's closed forms: octave
  self-count exactly k; fifth self-count exactly 0 — the fifth
  proved through (c1) as registered (a fifth pair would force
  odd parts 1 = 3).
- **(c1)** The class invariant: for positive rationals,
  `OctEq x y ↔ octInv x = octInv y`; powers of 2 are exactly the
  class of 1.
- **(c2) No finite octave closure (kill-grade, on the face):**
  a finite S not containing 0 and closed under doubling is
  empty; and OctChain length is bounded by the spectrum's own
  range (`octChain_le_max`). Any "octave-complete finite
  spectrum" claim dies against this on sight.
- **(c3)** The two extremal censuses: the geometric family lies
  in ONE octave class; the arithmetic family {1, …, L} meets
  exactly the odd classes ≤ L, count (L + 1) / 2.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
abstract finite combinatorics; no dial moves. K-RES-1 on the
face.

**Census after landing: 11,271 strict / 11,477 total / 383 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
