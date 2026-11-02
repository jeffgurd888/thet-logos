# F2-GATE-2c — LANDING DOSSIER: **G2c DISCHARGED AT `4 ≤ N`** (2026-11-02)

**Brick:** F2-GATE-2c of the F2 weld line, fired under
Jeff's 2026-11-02 00:13 EST order "proceed" (Order A).
Parent-verified: main-tree targeted build green
(`lake build ThetLogos.Span3SeatSchurGateG2c`, 3,658 jobs);
CI axiom fence PASS on both theorems, axioms exactly
`[propext, Classical.choice, Quot.sound]`.

**Module:** `lean/ThetLogos/Span3SeatSchurGateG2c.lean`
(counted **strict 2 / defs 0**, zero sorrys). Not in the
root import list; verified by targeted build.

## The verdict, at full rank

**G2c_gate4 is DISCHARGED at `4 ≤ N`.**

`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved`:
the re-pinned item-1 Prop holds — for every bounded measurable
`f` and **every** layer function `φ` (no hypotheses on `φ`;
the statement's `hf`/`hfbdd` are in fact not needed — the
invariance is pointwise identities plus measure-preserving
substitution plus the landed twirl invariances), both
`fiberAvgTop` of the `posGaugeAvg`-dressed and of the
`mirrorGaugeAvg`-dressed observable are `GaugeInvariantLayerObs`.

**K-F2-2 does NOT fire at `4 ≤ N`.** Its `N = 2` firing
(GATE-2) stands unedited: at `N = 2` the embeddings coincide
and the dressed fiber average returns `φ` verbatim. At
`4 ≤ N` the mechanism is excluded by the proved disjointness
(`tauBot_spliceTop_of_four_le`), and the decision goes
positive through the Γ-lift: a layer gauge action is lifted
to a configuration gauge function supported at the top time
layer (pos conjunct) resp. the reflected top time layer
(mirror conjunct — the mirror twirl is invariant under its
own action only), the splice commutes with the action under
the lift, `tauBot` is lift-invariant, the fiber integral is
transported by the landed measure-preserving gauge
equivalences (`gaugeStratumEquiv`, `mirrorGaugeEquiv`), and
the landed twirl invariances (`posGaugeAvg_gauge`,
`mirrorGaugeAvg_gauge`) close.

`repinGate_all_items_at_four_le`: with the Consume brick
(items 2/3 = G2a/G2b consumed exactly from GATE-2), **all
five re-pinned gate Props are now theorems at `4 ≤ N`.**

## Behind the gate — the registered sequence, scoped from the record

The weld sequence behind the gate was scoped from the
record in this run. It does NOT fire. Two findings, at the
rank the evidence supports:

**GATE-3 (GATE-0 item 5, `pullBotKernel_seatFactorApproxExpansion`)
— does NOT fire; structural obstruction found at scoping.**
Item 5's hypothesis is `LayerKernelPos` — positivity of the
layer kernel on the gauge-*invariant* sector. The
compression engine recorded in the GATE scoping consumes
factor families on gauge-invariant layer `L²` subspaces.
But Gram sums built from gauge-invariant factors are
invariant in the first kernel slot separately, and HS
limits preserve that invariance, whereas
`layerKernel (γ • u) u' ≠ layerKernel u u'` in general (the
one-sided layer action moves the crossing plaquette
densities between the layer and the stratum; only the
diagonal action leaves the kernel invariant). With
*arbitrary* factor families (which item 5 as frozen
permits), existence of the expansion is equivalent to the
layer-kernel operator being PSD on **all** of `L²(layer)` —
strictly stronger than `LayerKernelPos`, and producing it
would be a Gram/PSD fact about `𝒜` itself: factoring `𝒜` is
forbidden from this chair, and the core-chain fence bars
firing it as a weld brick. Disposition: the registered
GATE-3 headline is not dischargeable through the registered
route; the stronger statement it would need is a core-chain
object. K-GATE-3 (pre-registered: "the adapted
HS-convergence lemma is false as needed") is supported at
dossier grade by this obstruction but is NOT machine-killed
in this run — a formal kill is a separate falsity-probe
brick and a parent decision.

**GATE-4 (GATE-0 item 6, `seatSchurTarget_of_approxProductStep`)
— pin finding of the GATE-2 species.** Item 6's limit
passage needs product-seat integrability (the `hInt`
input): joint measurability of `layerKernel` in its two
layer arguments is landed nowhere at the pin's generality —
every corpus kernel-measurability lemma carries a
`Continuous fun g => repMatrix ρ g` hypothesis the pin does
not carry — and item 5 as frozen supplies factor families
with no measurability and only a difference-kernel `MemLp`
clause, which does not yield the per-factor `L²` membership
item 6's splitting step consumes. The frozen item 6 carries
no such hypothesis. A conditional-under-`hInt` form would
be a NEW registry entry (the re-pin precedent), requiring a
parent decision; K-F2-3 forbids landing the weakened form
under the weld headline. Disposition: scoped and reported;
not built.

**F2-W3 (`seatSchurProductStepOpen`)** stays OPEN behind
GATE-3/GATE-4, exactly as registered. The weld consumes
seat-shaped Schur structure only; nothing in this run
factored `𝒜`.

## The fence, restated

The discharged gate is the weld's decision gate only. The
gate + W3, even completed, prove neither FACT nor
clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity
remain open. **NO CLAIM** — parts of any official
Millennium statement closed: 0. Dials: 0/4.

## Census

Contribution +2 strict / +0 defs (combined gate-run census:
**12,745 strict / 13,270 total / 456 modules**, zero
sorrys). CI fence registry grew 21 → 32 declarations with
this run's headlines; FENCE PASS 32/32.

## BRIDGE-1

No registry interaction; registry unchanged (BR1-001…030).

## Environment note

As recorded in the Consume dossier: an environment rollback
destroyed the first execution of this run's landing
ceremony; every verdict here was re-derived from the
surviving tree and re-verified by the coordinator in the
main tree before shipping. The proof itself was built
independently twice (two builder runs) with the same
result.
