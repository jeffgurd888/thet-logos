/-
# F2-GATE-CONSUME: the re-pinned gate's items 2/3 are exactly the landed GATE-2 instances

Brick F2-GATE-CONSUME of the F2 weld line. The re-pinned
gate (`ThetLogos.Span3SeatSchurGateRepin`) froze its
items 2 (G2a) and 3 (G2b) at `4 ≤ N` as Props taking the
banked GATE-2 inputs `hInt` / `hMarg` as explicit
hypotheses. GATE-2 (`ThetLogos.Span3SeatSchurGateFiber`)
landed theorems whose statements are exactly those
Props' bodies. This module machine-checks that
consumption: four small theorems stating each
re-pinned Prop and proving it by exact application of
the landed GATE-2 theorem, so the gate state is
machine-checked, not prose.

Item 1 (G2c) is NOT touched by this module.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, on the face:** the gate plus F2-W3 prove
neither FACT nor clause (a); `LayerKernelPos`,
`𝒜 ⪰ 0`, and uniformity remain open before and after.
No Gram factorization of `𝒜` anywhere in this module.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGateRepin

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateConsume

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **Item 2, top (G2a) at `4 ≤ N`, consumed.** The
re-pinned Prop is exactly the `hInt`-supplied instance
landed in GATE-2 as
`seatPairing_pullTop_eq_pullTopPairingIter_of_integrable`. -/
theorem seatPairing_pullTop_eq_pullTopPairingIter_gate4_of_integrable
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) :
    seatPairing_pullTop_eq_pullTopPairingIter_gate4 μG ρ hN hN4 β :=
  fun F hInt =>
    seatPairing_pullTop_eq_pullTopPairingIter_of_integrable μG ρ hN β F hInt

/-- **Item 2, bottom (G2a) at `4 ≤ N`, consumed.** The
re-pinned Prop is exactly the `hInt`-supplied instance
landed in GATE-2 as
`seatPairing_pullBot_eq_pullBotPairingIter_of_integrable`. -/
theorem seatPairing_pullBot_eq_pullBotPairingIter_gate4_of_integrable
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) :
    seatPairing_pullBot_eq_pullBotPairingIter_gate4 μG ρ hN hN4 β :=
  fun F hInt =>
    seatPairing_pullBot_eq_pullBotPairingIter_of_integrable μG ρ hN β F hInt

/-- **Item 3, top (G2b) at `4 ≤ N`, consumed.** The
re-pinned Prop is exactly the `hInt` / `hMarg`-supplied
instance landed in GATE-2 as
`seatPairing_pullTop_eq_layerPairing_fiberAvg_of_integrable_marg`. -/
theorem seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4_of_integrable_marg
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) :
    seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4 μG ρ hN hN4 β :=
  fun g hInt hMarg =>
    seatPairing_pullTop_eq_layerPairing_fiberAvg_of_integrable_marg
      μG ρ hN β g hInt hMarg

/-- **Item 3, bottom (G2b) at `4 ≤ N`, consumed.** The
re-pinned Prop is exactly the `hInt` / `hMarg`-supplied
instance landed in GATE-2 as
`seatPairing_pullBot_eq_layerPairing_fiberAvg_of_integrable_marg`. -/
theorem seatPairing_pullBot_eq_layerPairing_fiberAvg_gate4_of_integrable_marg
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) :
    seatPairing_pullBot_eq_layerPairing_fiberAvg_gate4 μG ρ hN hN4 β :=
  fun g hInt hMarg =>
    seatPairing_pullBot_eq_layerPairing_fiberAvg_of_integrable_marg
      μG ρ hN β g hInt hMarg

end Span3SeatSchurGateConsume

end ThetLogos
