# B4-FIN LANDING DOSSIER — 2026-11-02

**Item:** B4-FIN (SHELF-7b-disc chain, GATE-B discharge
campaign) — finiteness of the zeros of f − mu in a closed
subdisc: ingredient 3's finiteness step.

## VERDICT: FULL — K-B4-FIN does NOT fire; the registered route went through with the pin's API exactly as scoped

**Artifact:** `lean/ThetLogos/DiscZeroFiniteness.lean` —
strict 6, defs 1. Verified by the coordinator in the main
tree (build green, 2991 jobs); headline on exactly
`[propext, Classical.choice, Quot.sound]`.

**Headline:** `finite_zeros_closedBall` — for
`DiscHolomorphic f R`, any `R₂ < R` (the only radius
hypothesis the route needs; no 0 < R₂), and g = f − mu not
identically zero on the open disc: there is a Finset whose
members are exactly the zeros of f − mu in
`closedBall 0 R₂`. Delivered with the Finset
(`zeroFinsetClosedBall` + its membership lemma) and the
set-form finiteness statement.

**Route, as registered in the B4 scoping:** analyticity on
the open disc (`DifferentiableOn.analyticOnNhd`) → the
identity theorem's isolated-zeros form (in this pin:
`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`)
→ codiscreteness of the zero set in the open disc → **the
armed transport glue went through**:
`Filter.codiscreteWithin_mono` along
`Metric.closedBall_subset_ball` restricts codiscreteness to
the closed ball, and
`IsCompact.finite_sdiff_of_mem_codiscreteWithin` at
`isCompact_closedBall` closes. No replacement route was
used or needed.

**Campaign state:** B4-REPAIR ✔, B4-FIN ✔; B4-PROD (the
coefficient-product identity) fires next; B4-TAIL
(multiplicity iteration + tail identification, consuming
this finiteness) behind it; then B4-UNIT, B4-ASM ⇒
`shelf7bDiscInterior_proved` unconditional and GATE-B
closes for the disc chain.

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked.

**Census after landing: 12,261 strict / 12,668 total / 423 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
