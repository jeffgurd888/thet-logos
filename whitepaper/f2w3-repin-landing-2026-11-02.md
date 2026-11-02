# F2-W3 GATE RE-PIN LANDING DOSSIER — the gate re-pinned at 4 ≤ N; seat separation FULL — 2026-11-02

**Item:** DECISION 5 (Jeff, 2026-11-01 23:23 EST): re-pin the
F2-W3 gate interface at 4 ≤ N (the GATE-0 pin's G2c Prop was
DISPROVED at N = 2 by GATE-2 — K-F2-2 / K-GATE-2 fired), then
run the re-pinned gate's first brick.

## VERDICT: RE-PIN LANDED (new entry, relabeling rule — the GATE-0 pin and the GATE-2 kill stand unedited); FIRST BRICK LANDED FULL

**Artifacts:** `lean/ThetLogos/Span3SeatSchurGateRepin.lean`
— strict 0, defs 6; `lean/ThetLogos/Span3SeatSchurGateSeat.lean`
— strict 1, defs 0. Verified by the coordinator in the main
tree (build green, 3656 jobs); the brick's headline on exactly
`[propext, Classical.choice, Quot.sound]` (coordinator
re-checked).

## The re-pin (six frozen Props)

GATE-0's interface mirrored with `(hN : Even N) (hN4 : 4 ≤ N)`:
the G2c decision lemma
`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4`;
the G2a product↔iterated Props (top/bot) at 4 ≤ N with `hInt`
carried as an explicit hypothesis in exactly GATE-2's landed
integrand form; the G2b fiber-average identity Props (top/bot)
at 4 ≤ N with `hInt` and `hMarg` carried explicitly — so
GATE-2's landed `…_of_integrable` / `…_of_integrable_marg`
theorems are precisely the re-pinned Props' supplied
instances; and the discharge headline
`seatSchurProductStepOpen_discharge_gate4` as a ∀-Prop over
Even N with 4 ≤ N.

## Why 4 ≤ N is the honest domain (on the pin's face)

The GATE-2 kill is proved, in-tree, at N = 2: the top and
bottom layer embeddings COINCIDE there
(`embLayerTop_eq_embLayerBot_at_two` — the top extraction
site's time is N/2 − 1 = 0, the bottom time), so the dressed
fiber average is the dressing itself, unaveraged, and a
non-gauge-invariant dressing φ is a counterexample
(`g2c_counterexample`). With `NeZero N`, **N = 2 is the only
even N below 4** — so 4 ≤ N excludes exactly the killed seat
and no other seat, and the disjointness premise the GATE-0
pin needed holds only for N ≥ 4 (gate2 dossier). The domain
restriction is read off a proved counterexample's mechanism,
not asserted.

## First brick — seat separation, FULL in the strongest form

`embLayerTop_ne_embLayerBot_of_four_le : ∀ ℓ : LayerLink N,
embLayerTop hN ℓ ≠ embLayerBot hN ℓ` for Even N, 4 ≤ N —
proved for EVERY layer link (an equality would force the
time coordinates N/2 − 1 and 0 to agree; at 4 ≤ N,
N/2 − 1 ≥ 1). **The exact coincidence mechanism of the N = 2
kill is proved excluded at 4 ≤ N.** This brick decides the
seat, not G2c: `fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4`
remains the re-pinned gate's open decision lemma, and
`seatSchurProductStepOpen` itself remains OPEN.

## Kills and fences

**K-F2-2 is RE-ARMED at 4 ≤ N**: a counterexample at any even
N ≥ 4 kills the re-pinned route at full rank. K-F2-3 / K-F2-4
/ K-GATE-2 / K-GATE-3 stand as registered. The weld fence is
unchanged: factoring 𝒜 itself is forbidden inside the weld;
only seat-shaped Schur structure for bounded kernels on
probability spaces may be consumed. Even a FULL re-pinned
gate + W3 would prove neither FACT nor clause (a) —
`LayerKernelPos`, clause (a), 𝒜 ⪰ 0, and uniformity stand
open exactly as before. NO CLAIM; dials 0/4.

**Census after landing: 12,648 strict / 13,169 total / 449
counted modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
