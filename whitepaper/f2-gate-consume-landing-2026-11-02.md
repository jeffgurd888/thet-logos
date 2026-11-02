# F2-GATE-CONSUME — LANDING DOSSIER (2026-11-02)

**Brick:** F2-GATE-CONSUME of the F2 weld line. Parent-verified
(post-rollback re-verification; see the environment note at the
foot of this dossier).

**Module:** `lean/ThetLogos/Span3SeatSchurGateConsume.lean`
(counted **strict 4 / defs 0**, zero sorrys). Not in the root
import list; verified by targeted build
(`lake build ThetLogos.Span3SeatSchurGateConsume`, green) and by
the CI axiom fence (all four declarations PASS, axioms exactly
`[propext, Classical.choice, Quot.sound]`).

## What landed

The re-pinned gate (`Span3SeatSchurGateRepin`) froze items 2
(G2a) and 3 (G2b) at `4 ≤ N` as Props taking the banked GATE-2
inputs `hInt`/`hMarg` as explicit hypotheses. This module
machine-checks that those Props are EXACTLY the instances
landed in GATE-2 (`Span3SeatSchurGateFiber`), by stating each
re-pinned Prop as a theorem and proving it by exact
application of the landed GATE-2 theorem:

- `seatPairing_pullTop_eq_pullTopPairingIter_gate4_of_integrable`
- `seatPairing_pullBot_eq_pullBotPairingIter_gate4_of_integrable`
- `seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4_of_integrable_marg`
- `seatPairing_pullBot_eq_layerPairing_fiberAvg_gate4_of_integrable_marg`

**K-F2-3 check:** the K-F2-3 weakening trap (landing a strictly
weaker statement under the weld headline) does NOT trigger:
the bot G2a integrand's seat-factor slot swap
`(tauBot p.2) (tauBot p.1)` matches on both sides, and all
four consumptions are exact definitional applications — no
hypothesis added, dropped, or reshaped anywhere.

## What this does NOT do

Item 1 (G2c) is discharged in the companion brick
F2-GATE-2c, not here. The gate plus F2-W3 prove neither FACT
nor clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity
remain open before and after.

**NO CLAIM** — parts of any official Millennium statement
closed: 0. Dials: 0/4.

## Census

12,725 → contribution +4 strict / +0 defs (this brick's slice
of the combined gate-run landing; combined census after all
three gate bricks: **12,745 strict / 13,270 total / 456
modules**, zero sorrys).

## BRIDGE-1

No registry interaction (pure Lean-internal weld brick). The
BR1 registry is unchanged by this landing.

## Environment note (on the record)

This run executed through an environment rollback that
destroyed the first landing attempt's commit, dossier, and
README/fence edits after they had been produced. All verdicts
in this dossier were re-derived from the surviving tree and
re-verified by the coordinator in the main tree (targeted
build + fence) before this dossier was written. The three
gate bricks are therefore landed in ONE combined commit,
stated on its face; the per-brick dossiers carry the
individual verdicts.
