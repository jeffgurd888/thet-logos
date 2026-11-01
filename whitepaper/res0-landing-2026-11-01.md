# RES-0 LANDING DOSSIER — 2026-11-01

**Item:** RES-0 (SumResonance definitions and API), opening
brick of the resonance line, per the ratified scoping memo
(`scoping-resonance-2026-10-30.md`) and the coordinator pack
(`pack-res-0.md`).

**Status: FULL.** Registration-grade definitions landed — the
vocabulary RES-1..RES-4's Props are stated in. RES-1's shared-gap
core was NOT touched (no API lemma turned out to be an RES-1
statement in disguise; the two closest neighbours,
`diffCount_zero` and `collCount_diag_le`, are strictly weaker
than (a1)/(a2), on the record).

**Artifact:** `lean/ThetLogos/SumResonance.lean` — strict 27,
defs 17. Strict runs above the memo's 8–14 estimate: the overrun
is the pack's own itemization (15 frozen defs including the
ternary twins, the four named API items, plural bridges, one
read-back per definition), disclosed on the builder's report and
here. Verified by the coordinator in the main tree (build green,
3117 jobs); all 8 axiom-checked headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## What landed

Definitions (ℚ throughout, memo §2 forms): `sumFam`/`sumSpec`
and the ternary twins `sumFam3`/`sumSpec3`; `multA`; `diffCount`,
`diffRange`, `diffSpec`; `collCount`, `collCount3`; `excess`;
`resCount` (zero-fenced in the definition, per (b2)); `OctEq`,
`octInv` (via `padicValRat 2`), `OctChain`. API: sum-index cards,
the multiset↔family bridges (`sumSpec_eq_map`, `multA_eq_count`,
`diffCount_eq_count`, `diffRange_eq_toFinset`), `diffCount_neg`
(r(−d) = r(d)), `diffCount_zero` (= ∑ (multA x)²),
`collCount_diag_le` (the diagonal floor m*n ≤ collCount),
`excess_add_dedup_card`, the zero-fence at work
(`resCount_zero_family`), `octEq_two_mul`. Thirteen exact
read-backs on the named example families.

## Fences

The memo's registered framing is on the face (systems share a
resonance iff they share a nonzero gap — the abstract
combinatorial statement only), K-RES-1 noted (raw counts are
bookkeeping, not the theorems). NO CLAIM — no Millennium problem
is claimed solved or advanced; no dial moves.

**Census after landing: 11,049 strict / 11,229 total / 376 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
