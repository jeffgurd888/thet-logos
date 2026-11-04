# GATE-3, BRICK 2 — THE MEASURABILITY SWAP — landing note (2026-11-04)

Status: LANE landing, FULL. Build only in the isolated
worktree `thet-logos-gate3meas` (branch `gate3-meas-swap-lane`,
base main-tree HEAD `843be2b`); parent integrates. Commissioned
by Jeff 2026-11-04 ("fire all", GATE-3 front, Brick 2).
Contract: `~/workspace/your_files/gate3-reg-audit-2026-11-04.md`
(the GATE3-REG-AUDIT census — the work order) and
`~/workspace/your_files/gate3-second-attack-scoping-2026-11-04.md`
(Angle A). Fences: **NO CLAIM; dials 0/4.**

## The landing

New module `lean/ThetLogos/Span3SeatSchurGateMeasSwap.lean`,
beside the landed statements, **nothing edited**: the frozen
GATE-3 statement and the `_of_cont` chain are untouched. The
BRIDGE-COR chain is re-proved with the continuity hypothesis
`hρcont : Continuous fun g : G => repMatrix ρ g` replaced
throughout by measurability
`hρmeas : Measurable fun g : G => repMatrix ρ g`, landing the
measurability form of the frozen statement:

```
theorem pullBotKernel_seatFactorApproxExpansion_of_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g) :
    pullBotKernel_seatFactorApproxExpansion (N := N) μG ρ
```

i.e. at every `Even N` and every `β ≥ 0`, `LayerKernelPos`
implies `SeatFactorApproxExpansion` — **at every measurable
ρ**. Strict count: **10 theorems + 1 def**, inside the
re-priced band 10–18. All ten theorems verified by
`#print axioms` to depend on exactly
`{propext, Classical.choice, Quot.sound}`; zero `sorry`
(source-checked), no `native_decide`; targeted module build
green (3,676 jobs) with **zero warning/error lines naming
the module** (the build log's warnings are pre-existing
notes in dependency modules, none in this file).

## Census-to-build mapping (audit row → what the build did)

| # | Census site (audit verdict) | Build outcome |
|---|---|---|
| 1 | `LatticeLayerFactor:178` `measurable_plaquetteDensity_lf` — the root, the cone's only direct consumption, via `hρcont.measurable` (MEASURABILITY-ONLY) | `measurable_plaquetteDensity_meas`: verbatim replay with `hρmeas.comp (measurable_plaquette …)` as the drop-in term. One deviation, cosmetic: the auto-included `[MeasurableInv G]` instance is unused at this site and is dropped via `omit` (house pattern) for a warning-clean build; the Prop proved is identical. |
| 2 | `GateItem6:178` `measurable_layerAction` — pass-through | `measurable_layerAction_meas`: replay, consuming #1 and the regularity-free `measurable_layerConfig`. |
| 3 | `GateItem5:929` `layerKernelFun_memLp` — pass-through via #2 | `layerKernelFun_memLp_meas`: replay; boundedness stays the continuity-free `layerKernel_norm_le` + `MemLp.of_bound`. |
| 4 | `GateItem5:1031` `LayerKernelPosAll` (def) — `hρcont` only in a proof-irrelevant `MemLp` slot (DEFINITIONAL) | `LayerKernelPosAll_meas` (def, founded on #3) + `layerKernelPosAll_meas_eq`: the `_meas` and `_cont` indices are **the same Prop** (proof `rfl` — proof irrelevance of the slot, as the audit predicted). |
| 5 | `GateItem5:1173` `seat_stage_memLp` — pass-through | `seat_stage_memLp_meas`: replay with #3. |
| 6 | `GateItem5:1196` `seat_stage_eLpNorm` — pass-through | `seat_stage_eLpNorm_meas`: replay with #3. |
| 7 | `GateItem5:1234` `seatFactorApproxExpansion_of_layerKernelPosAll` — pass-through + definitional index | `seatFactorApproxExpansion_of_layerKernelPosAll_meas`: replay; the regularity-free `exists_seq_tendsto` / `layerKernelFun_selfAdjoint` receive #3 in their `hK` slots and the `_meas` `hAll`. |
| 8 | `PosBridge:1175` BRIDGE-MAIN `layerKernelPosAll_of_layerKernelPos` — one production of #3, rest regularity-free | `layerKernelPosAll_of_layerKernelPos_meas`: replay with the single production `hK := layerKernelFun_memLp_meas`; the `integralKernelOp_inner` formula, `layerPairingProd` transports, `gaugeAvg` API and `layerPairing_nonneg_of_layerKernelPos` consumed unchanged. |
| 9 | `PosBridge:1216` `seatFactorApproxExpansion_of_layerKernelPos` — pure composition | `seatFactorApproxExpansion_of_layerKernelPos_meas`: composition of #7 and #8. |
| 10 | `PosBridge:1229` `pullBotKernel_seatFactorApproxExpansion_of_cont` — pure composition | `pullBotKernel_seatFactorApproxExpansion_of_meas`: composition of #9; the headline above. |

Out-of-cone, deliberately not replayed (per the audit's
excluded-sites list): PB-2 `layerKernelOp_inner_gaugeAvg`
(PosBridge:1130) — not called by BRIDGE-MAIN, its content
inlined there; the sibling wrapper
`seatFactorApproxExpansion_of_layerKernelPosAll_of_four_le`
(GATE-4C/W3 cone, not a BRIDGE-COR dependency);
`aestronglyMeasurable_pullTopKernel` (G2/GateSeat cone). No
site resisted the swap; no statement was altered anywhere.

## Scope fence

This lands GATE-3 **at every measurable ρ**. The frozen
GATE-3 statement `pullBotKernel_seatFactorApproxExpansion`
itself remains **OPEN** after this brick: its remaining gap
is exactly the wild class at β > 0 — seats where
`fun g : G => repMatrix ρ g` is not measurable — and within
that class exactly one lemma: the stratum Boltzmann factor
at a wild seat is not `AEStronglyMeasurable` (the
GATE3-REG-AUDIT's Angle-B residue, re-priced 15–40 strict,
UNRESOLVED). This brick does not touch that lemma and does
not claim the frozen statement outright. The composition
brick (Brick 3: measurable/wild case split, 2–5 strict)
stays conditional on that lemma existing in either
direction.

Kill status: **K-GATE-3 did NOT fire** — it fires only on a
seat with `LayerKernelPos` proved and the expansion refuted;
no such seat was produced or approached here, and no swap
resistance occurred (a resistance would have been an
obstruction, not a kill).

NO CLAIM; dials 0/4.
