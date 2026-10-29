import ThetLogos.PlaneCrossingCube
import ThetLogos.PlaneCrossingSymm

/-!
# ThetLogos.LayerKernelPos — Brick A0: the `𝒜 ⪰ 0` campaign
target, registered as a Lean proposition (statement only)

This module REGISTERS the campaign target "`𝒜 ⪰ 0` on
gauge-invariant observables" as a Lean proposition in owned
vocabulary (`LayerKernelPos` below). Until today the target
existed only in dossier prose; kills and landings now register
against this statement.

The landed sufficiency chain (`planeCrossingMarginal_layerKernel`
— the β1 factorization — plus the α-remainder twirl reduction
plus the Schur product theorem) makes this proposition
SUFFICIENT for clause (a) of `TransferFormPos`
(`LatticeTransferCompact`); necessity is unknown; a kill of
this proposition kills the sufficient route, NOT clause (a).

**NO proof is attempted here, and nothing in this module
asserts positivity of any kernel.** This is a
statement-registration brick only.

NO CLAIM; parts of the Clay statement closed: 0; dials 0/4;
β⁵ sign and the general β⁶ sign stay FRONTIER.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section LayerKernelPosSection

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The gauge action on layer data**: the corpus's linkwise
gauge action (`gaugeStratumFun`, `PlaneCrossingSymm`) read
through the inclusion of a layer link as a link. At a layer
link `ℓ` with value `v` this is `g (base ℓ) * v * (g (shifted
base ℓ))⁻¹`, where `g` is a gauge function on sites. -/
def layerGaugeAction (g : (Fin 4 → ZMod N) → G)
    (u : LayerLink N → G) : LayerLink N → G :=
  gaugeStratumFun (fun ℓ : LayerLink N => ℓ.1) g u

/-- **Gauge invariance of a layer observable**: a test function
`F` on layer data is gauge invariant when it is unchanged by
the gauge action on layer data, for every gauge function and
every layer datum. (Defined in this module, Brick A0: the
corpus owned a gauge action on layer data but no invariance
predicate on layer observables.) -/
def GaugeInvariantLayerObs (F : (LayerLink N → G) → ℂ) : Prop :=
  ∀ (g : (Fin 4 → ZMod N) → G) (u : LayerLink N → G),
    F (layerGaugeAction g u) = F u

/-- **𝒜 ⪰ 0 on gauge-invariant observables** (the registered
    campaign target; statement only — NO positivity is asserted
    or proved anywhere in this module).

    The pairing is the corpus's integral pairing over layer
    configurations with respect to the product Haar probability
    measure — the normal form for pairings over a
    `(link → G)` configuration space at general `(G, ρ)` (as in
    `layerKernel` itself and the landed Gram / OS pairings):
    at general `G` the configuration space is not finite, so a
    finite sum over all configurations is not available; at a
    finite seat the integral is the sum scaled by the positive
    factor `1 / (number of configurations)`, so the sign
    registered here is the seat sums' sign. -/
def LayerKernelPos (β : ℝ) : Prop :=
  ∀ F : (LayerLink N → G) → ℂ, GaugeInvariantLayerObs F →
    0 ≤ (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG)).re

end LayerKernelPosSection

end ThetLogos
