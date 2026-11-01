# RES-2 LANDING DOSSIER — 2026-11-01

**Item:** RES-2 (forcing and extremality), per the ratified
scoping memo (`scoping-resonance-2026-10-30.md`, §3) and the
coordinator pack (`pack-res-2.md`). RES-0/RES-1 vocabulary
cited, never forked.

**Status: FULL — all four clauses.**

**Artifact:** `lean/ThetLogos/SumResonanceForcing.lean` —
strict 30, defs 7 (in the memo's 22–36 band). Verified by the
coordinator in the main tree (build green, 3119 jobs); headlines
on exactly `[propext, Classical.choice, Quot.sound]`, one on the
cleaner subset `[propext, Quot.sound]`.

## What landed

- **Denominator clearing as a stated transport:** every finite
  ℚ-spectrum scales into ℤ by a positive common scale
  (`exists_scale_int`, `exists_common_scale_int`), and the
  (a)-family quantities are invariant under common nonzero
  scaling in the memo's exact sense (`collCount_scale`,
  `diffCount_scale` as the pattern at D·d, `excess_scale`,
  `sumMult_scale`) — the scale is a symmetry, proved, not
  asserted.
- **The pigeonhole floor:** sums landing in a value set S give
  `m * n − S.card ≤ excess a b` (`excess_ge_floor`), and some
  sum value carries multiplicity at least the ceiling form
  `(m * n + K − 1) / K` (`exists_sumMult_ceil_ge`) — with the
  integer-seat forms carried through the cast bridge.
  Coincidences past this floor are arithmetic rent, now at
  theorem grade.
- **The distinct-sums range bound:** all sums distinct ⇒ the
  sum range is at least `m * n − 1`
  (`distinct_sums_range_bound`, over ℤ seats, with the attained
  form).
- **The extremal witness:** the base-(2L+1) family
  (`baseA L i = i`, `baseB = (2L+1) • baseId`) — all sums
  distinct (proved by reduction mod 2L+1), and the bound's
  shape is achieved: the top sum is exactly
  `L + (2L+1)(n−1)` (`sumFamZ_base_range_achieved`). Between the
  floor and the encoding sits everything a seat can honestly
  say — §3's framing, now T1.

RES-2b ((a4) perturbation finiteness) untouched — optional, as
registered.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
abstract finite combinatorics; no dial moves. K-RES-1 on the
face (these theorems price seat reports; they are not seat
reports).

**Census after landing: 11,245 strict / 11,448 total / 382 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
