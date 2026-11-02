# GATE-2 LANDING DOSSIER — 2026-11-02

**Item:** GATE-2 (F2 weld line) — fiber-average reduction +
the G2c confinement decision.

## VERDICT: PARTIAL — and K-F2-2 / K-GATE-2 FIRES: G2c is DISPROVED in-tree at N = 2; the weld route dies at that seat

**Artifact:** `lean/ThetLogos/Span3SeatSchurGateFiber.lean` —
strict 13, defs 0 (below the 35–70 estimate, which priced a
full unconditional discharge; reported as counted). Verified
by the coordinator in the main tree (build green, 3654
jobs); all ten checked headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## The kill (top rank, by the house rule for negative verdicts)

**`g2c_counterexample : ¬ fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback`
at N = 2, G = Multiplicative (ZMod 2) — proved in Lean.**
The mechanism: at N = 2 the top and bottom layer embeddings
COINCIDE (the top site's time is N/2 − 1 = 0, the bottom
time), so `tauBot` composed with the top splice is the
identity splice, and for f ≡ 1 the fiber average of the
dressed observable is φ ITSELF — the dressing is not
averaged at all at this seat
(`fiberAvgTop_const_one_mul_pullback_at_two`, for every
layer φ and every (G, μG)). The witness φ (the indicator of
`w ℓ₀ ≠ 1` at one link) is moved by an explicit gauge
function (the flow-seat action at the zero site):
`φ (γ₀ • u₀) = 1 ≠ 0 = φ u₀`. Hence the fiber average is not
a gauge-invariant layer observable. The GATE-0 pin
 quantified over **all** Even N; its disjointness premise
holds only for N ≥ 4. The Prop does not depend on ρ — no
representation choice is involved.

**Consequences, exactly:** the GATE chain as pinned is dead
at G2c. GATE-3's headline feeds through GATE-2's dressed
confinement, so GATE-3/GATE-4 do **not** fire on this pin;
F2-W3 stays gated behind a killed gate. `seatSchurProductStepOpen`
itself remains OPEN — the kill decides the *route*, not the
Prop: a re-pin restricted to 4 ≤ N would be a **new entry**
(relabeling rule) and a parent/Jeff decision; none is taken
here, and no other confinement route is registered.

## G2a / G2b — not discharged as pinned; conditional forms proved; a pin finding, not a kill

The pin's stated hypotheses are two inputs short, isolated
exactly: (1) **`hInt`** — integrability of the pairing
integrand on the product space, whose measurability rests on
joint measurability of `layerKernel` in its two layer
arguments, landed nowhere (every corpus kernel-measurability
lemma carries a `Continuous fun g => repMatrix ρ g`
hypothesis the pin does not carry and which does not follow
from the ambient instances); (2) **`hMarg`** — the splice
disintegration / conditional-expectation property of the
landed `fiberAvgTop`/`fiberAvgBot`, landed nowhere. Proved
under exactly those inputs: both product↔iterated
identifications (`..._of_integrable`) and both fiber-average
identities (`..._of_integrable_marg`), plus the unconditional
`fiberAvgTop_conj` / `fiberAvgBot_conj`. `fiberAvgTop` was
NOT redefined. The G2a/G2b identities stand neither proved
nor disproved at the pin's hypotheses — the conditional
discharges are banked for any re-pin that adds the two
inputs as hypotheses.

## Fences

Even a FULL gate + W3 would have proved neither FACT nor
clause (a); a killed gate proves less. `LayerKernelPos`,
clause (a), 𝒜 ⪰ 0, and uniformity stand open exactly as
before — this kill is about one weld route at one seat.
NO CLAIM; dials 0/4.

**Census after landing: 11,979 strict / 12,336 total / 409 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
