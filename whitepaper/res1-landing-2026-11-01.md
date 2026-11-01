# RES-1 LANDING DOSSIER — 2026-11-01

**Item:** RES-1 (the shared-gap core), the headline brick of the
resonance line, per the ratified scoping memo
(`scoping-resonance-2026-10-30.md`, §2(a)) and the coordinator
pack (`pack-res-1.md`). RES-0's vocabulary cited, never forked.

**Status: FULL on all three clauses.**

**Artifact:** `lean/ThetLogos/SumResonanceCore.lean` — strict 29,
defs 0 (in the memo's 28–42 band). Verified by the coordinator
in the main tree (build green, 3118 jobs); all axiom-checked
headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What landed

- **(a1) The collision inner-product identity**
  (`collCount_eq_sum_diffCount`): `collCount a b = ∑ d ∈
  diffRange a, diffCount a d * diffCount b d` — every coincidence
  in the sum is paid for by a shared difference of the factors,
  and the total is exactly the inner product of the two
  difference-count functions. Proved by fiberwise counting over
  `diffRange a` (diffCount vanishes off its own range), the fiber
  lemma closing via RES-0's `diffCount_neg`. The union-range and
  `diffRange b` forms, per-summand bounds, and the self-collision
  sum-of-squares form landed with it.
- **(a2) The shared-gap criterion, sharp** (`collCount_eq_mul_iff`):
  `collCount a b = m * n` iff the distinctness conjunct
  (`diffCount a 0 * diffCount b 0 = m * n`) holds AND no nonzero
  d is a difference of both factors — the memo's exact form,
  equality case included. Corollary
  (`nontrivial_coincidence_iff_shared_gap`): under within-factor
  distinctness, a nontrivial coincidence exists iff the two gap
  sets share a nonzero element — the line's surviving headline
  in theorem form: systems share a resonance iff they share a
  nonzero gap. Plus `diffCount_zero_eq_iff_injective`
  (diffCount a 0 = m ↔ a injective).
- **(a3) The ternary identity** (`collCount3_eq_sum`): triple
  coincidences are the sum over difference triples summing to
  zero of the product of the three difference counts, via the
  three-equation fiber lemma.

(a4) untouched — RES-2b's optional content, as registered.
K-RES-1 is on the face: the theorems are the criterion and the
identity; raw counts are bookkeeping.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
abstract finite combinatorics, nothing physical asserted; no
dial moves.

**Census after landing: 11,182 strict / 11,376 total / 380 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
