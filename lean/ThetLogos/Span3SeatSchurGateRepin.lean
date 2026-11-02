/-
# F2-GATE-RE-PIN: the F2-W3 gate interface re-pinned at `4 ≤ N`

Brick F2-GATE-RE-PIN of the F2 weld line. This module is a
NEW entry under the relabeling rule: it re-pins the gate
interface frozen by GATE-0
(`ThetLogos.Span3SeatSchurGatePost`) at the restricted
domain `4 ≤ N`, after GATE-2
(`ThetLogos.Span3SeatSchurGateFiber`, dossier
`whitepaper/gate2-landing-2026-11-02.md`) decided the
original pin's G2c decision lemma NEGATIVE at `N = 2`.
The GATE-0 pin itself stands UNEDITED, kill and all;
nothing in this module asserts any of the Props frozen
below, and this module contains no theorems: it is a
defs-only pin (strict count 0, by design).

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, on the face:** even a completed re-pinned
gate plus F2-W3 proves neither FACT nor clause (a); it
would prove only a machine link between two open
statements (`LayerKernelPos` ⇒ clause (a)) at fixed
`(β, N)`. `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity
remain open before and after. **The §2.2 audit point
stands unchanged:** a Gram expansion of `𝒜` itself is
FORBIDDEN and VOID inside the weld — factoring `𝒜`
itself is forbidden; nothing below states or uses a
Gram factorization of `𝒜`.

## Why `4 ≤ N` is the honest domain

GATE-2's kill is proved at `N = 2`, and only there, by
an exact coincidence of the two seat embeddings: at
`N = 2` the top extraction site time is
`N / 2 - 1 = 0`, which is the bottom extraction's own
time, so `embLayerTop = embLayerBot` at `N = 2`
(`embLayerTop_eq_embLayerBot_at_two`, landed in
GATE-2), the top fiber average of a dressed observable
is the dressing layer function verbatim, and a
non-gauge-invariant dressing is a counterexample
(`g2c_counterexample`). The disjointness premise the
GATE-0 pin needed — the two extractions' coordinate
sets being disjoint — holds only for `N ≥ 4` (GATE-2
dossier). The restriction `4 ≤ N` excludes exactly the
killed seat and no other: with `NeZero N` in context,
`N = 2` is the ONLY even `N` below `4` (an even `N`
below `4` is `0` or `2`, and `NeZero N` rules out `0`).
So the re-pin does not retreat from any seat the kill
did not already take, and it does not resurrect the
`N = 2` seat in any form.

## What is re-pinned here

1. The G2c decision lemma, restricted to `4 ≤ N`
   (`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4`).
2. The G2a / G2b target Props at `4 ≤ N`, WITH the two
   banked GATE-2 inputs carried as explicit hypotheses:
   `hInt` (pairing-integrand integrability on the
   product pi space) and, for G2b, `hMarg` (the splice
   disintegration / fiber marginalization). GATE-2
   landed G2a / G2b only as conditional forms
   (`..._of_integrable`, `..._of_integrable_marg`) under
   exactly those inputs; the re-pinned Props below are
   stated so that those landed theorems are exactly
   their `hInt` / `hMarg`-supplied instances — the
   re-pin consumes the conditional forms, it does not
   restate the original pin's (insufficient)
   measurability-plus-boundedness hypotheses.
3. The discharge headline as a `∀`-Prop over `Even N`
   with `4 ≤ N`
   (`seatSchurProductStepOpen_discharge_gate4`).

## Kills armed on the face

- **K-F2-2 RE-ARMED at `4 ≤ N`**: a certified negative
  dressed pairing, or the re-pinned G2c Prop (item 1)
  proved false, at ANY even `N ≥ 4` ⇒ the re-pinned
  weld route dies at that seat, at full rank; sequel
  only as a NEW entry under a strengthened hypothesis.
- **K-F2-3** (as registered: generality creep /
  vacuity — no abstract positive-kernel restatement,
  no finite-seat retreat, no landing under the weld
  headline at a narrower seat).
- **K-F2-4** (as registered: buy inflation — no
  sentence may describe gate or weld progress as
  progress on FACT, `𝒜 ⪰ 0`, clause (a), or
  uniformity).
- **K-GATE-2**: the re-pinned gate's decision goes
  negative (the dressed fiber-average invariance, G2c
  at `4 ≤ N`, fails).
- **K-GATE-3**: the adapted HS-convergence lemma (the
  compression expansions of GATE-3 converging to
  `pullBotKernel` in HS norm) is false as needed.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGatePost
import ThetLogos.Span3SeatSchurGateFiber

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateRepin

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## Item 1 (G2c, re-pinned): the decision lemma at `4 ≤ N` -/

/-- **Item 1, the G2c decision lemma re-pinned at
`4 ≤ N`, frozen as a Prop; asserted nowhere.** This is
the GATE-0 Prop
`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback`
with its seat restricted by the extra hypothesis
`hN4 : 4 ≤ N` — the restriction that excludes exactly
the `N = 2` seat killed in GATE-2 (see the face).
**THE LIVE FORK of the re-pinned gate (Blocker G-β;
its failure at any even `N ≥ 4` is K-F2-2 re-armed /
K-GATE-2).** For every bounded measurable strict-half
observable `f` and every layer function `φ`, the top
fiber average of the twirled observable dressed by the
pulled-back factor, `(posGaugeAvg f) · (φ ∘ tauBot)`,
is a `GaugeInvariantLayerObs` — and likewise for the
mirror/twirled variant, `(mirrorGaugeAvg f) ·
(φ ∘ tauBot)`. Only under this lemma do the dressed
factor pairings of the product step fall inside the
class `LayerKernelPos` controls. -/
def fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4
    (hN : Even N) (hN4 : 4 ≤ N) : Prop :=
  ∀ (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ : (LayerLink N → G) → ℂ),
    AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
    (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
    GaugeInvariantLayerObs (N := N)
        (fiberAvgTop μG hN
          (fun z => (posGaugeAvg μG f) z * φ (tauBot hN z)))
      ∧ GaugeInvariantLayerObs (N := N)
        (fiberAvgTop μG hN
          (fun z => (mirrorGaugeAvg μG f) z * φ (tauBot hN z)))

/-! ## Item 2 (G2a, re-pinned): product ↔ iterated at `4 ≤ N`,
with `hInt` carried as an explicit hypothesis -/

/-- **Item 2, top (G2a) re-pinned at `4 ≤ N`, frozen as
a Prop; asserted nowhere.** For every layer observable
`F`, UNDER the banked GATE-2 input `hInt` — the
integrability, on the product pi space, of the
`pullTopKernel` pairing integrand for `F`, in exactly
the form consumed by the landed conditional theorem
`seatPairing_pullTop_eq_pullTopPairingIter_of_integrable`
— the product-integral `seatPairing` of `pullTopKernel`
on the pulled-back observables equals its iterated
form, the landed `pullTopPairingIter`. That landed
result is exactly this Prop's `hInt`-supplied
instance (at any even `N ≥ 4`): the re-pin consumes
the conditional form. The original pin's
measurability-plus-boundedness hypotheses are NOT
carried here: GATE-2 showed they do not yield `hInt`
from landed material, so the honest target names
`hInt` itself. -/
def seatPairing_pullTop_eq_pullTopPairingIter_gate4
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) : Prop :=
  ∀ F : (LayerLink N → G) → ℂ,
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        F (tauTop hN p.1)
          * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
            * (starRingEnd ℂ) (F (tauTop hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
    seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => F (tauTop hN z)) (fun z => F (tauTop hN z))
      = pullTopPairingIter μG ρ hN β F

/-- **Item 2, bottom (G2a) re-pinned at `4 ≤ N`, frozen
as a Prop; asserted nowhere.** The bottom analogue of
`seatPairing_pullTop_eq_pullTopPairingIter_gate4`, with
`hInt` in exactly the form consumed by the landed
conditional theorem
`seatPairing_pullBot_eq_pullBotPairingIter_of_integrable`,
which is exactly this Prop's `hInt`-supplied instance. -/
def seatPairing_pullBot_eq_pullBotPairingIter_gate4
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) : Prop :=
  ∀ F : (LayerLink N → G) → ℂ,
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        F (tauBot hN p.1)
          * (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
            * (starRingEnd ℂ) (F (tauBot hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
    seatPairing μG (pullBotKernel μG ρ hN β)
        (fun z => F (tauBot hN z)) (fun z => F (tauBot hN z))
      = pullBotPairingIter μG ρ hN β F

/-! ## Item 3 (G2b, re-pinned): the fiber-average identities
at `4 ≤ N`, with `hInt` and `hMarg` carried explicitly -/

/-- **Item 3, top (G2b) re-pinned at `4 ≤ N`, frozen as
a Prop; asserted nowhere.** For every strict-half
observable `g`, UNDER the two banked GATE-2 inputs —
`hInt` (the `pullTopKernel` pairing-integrand
integrability for `g`) and `hMarg` (the splice
disintegration / fiber marginalization for the top
extraction: integrating an observable against a
layer function pulled back along `tauTop` is
integrating its top fiber average against that layer
function) — the `pullTopKernel` seat pairing of `g`
with itself is the `layerPairing` of its top fiber
average `fiberAvgTop g`. Both inputs are in exactly
the forms consumed by the landed conditional theorem
`seatPairing_pullTop_eq_layerPairing_fiberAvg_of_integrable_marg`,
which is exactly this Prop's `hInt` / `hMarg`-supplied
instance (at any even `N ≥ 4`): the re-pin consumes
the conditional form. -/
def seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) : Prop :=
  ∀ g : (↥(posLinks (N := N)) → G) → ℂ,
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        g p.1 * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (g p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
    (∀ (a : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgTop μG hN a u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG)) →
    seatPairing μG (pullTopKernel μG ρ hN β) g g
      = layerPairing μG ρ β (fiberAvgTop μG hN g)

/-- **Item 3, bottom (G2b) re-pinned at `4 ≤ N`, frozen
as a Prop; asserted nowhere.** The bottom analogue of
`seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4`,
with `hInt` and `hMarg` (bottom forms) in exactly the
forms consumed by the landed conditional theorem
`seatPairing_pullBot_eq_layerPairing_fiberAvg_of_integrable_marg`,
which is exactly this Prop's `hInt` / `hMarg`-supplied
instance. -/
def seatPairing_pullBot_eq_layerPairing_fiberAvg_gate4
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) : Prop :=
  ∀ g : (↥(posLinks (N := N)) → G) → ℂ,
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        g p.1 * (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
          * (starRingEnd ℂ) (g p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
    (∀ (a : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a z * Ψ (tauBot hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgBot μG hN a u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG)) →
    seatPairing μG (pullBotKernel μG ρ hN β) g g
      = layerPairing μG ρ β (fiberAvgBot μG hN g)

/-! ## Item 4 (GATE-4 headline, re-pinned): the discharge
target at `4 ≤ N` -/

/-- **Item 4, the GATE-4 headline re-pinned at
`4 ≤ N`, frozen as a ∀-Prop; asserted nowhere.** This
is the GATE-0 discharge headline
`seatSchurProductStepOpen_discharge` restricted to
even `N` with `4 ≤ N`: at every such `N` and every
`β`, the landed open Prop `seatSchurProductStepOpen`
(F2-W2's registered remainder) holds — hence, by that
Prop's definition, `SeatSchurTarget μG ρ hN β` in the
pin's registered form. Discharging this Prop is the
whole re-pinned gate; even then, per the fence on
this module's face, neither FACT nor clause (a) is
proved. -/
def seatSchurProductStepOpen_discharge_gate4 : Prop :=
  ∀ (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ),
    seatSchurProductStepOpen μG ρ hN β

end Span3SeatSchurGateRepin

end ThetLogos
