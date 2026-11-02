/-
# F2-GATE-2c: G2c DISCHARGED at `4 ≤ N`

Brick F2-GATE-2c of the F2 weld line. The F2-W3 gate was
re-pinned at `4 ≤ N` (`ThetLogos.Span3SeatSchurGateRepin`).
Its one remaining open item was item 1, G2c, the Prop
`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4`.
The engine brick `ThetLogos.Span3SeatSchurGateLift` landed
the splice API and both gauge lifts, and the consumption
brick `ThetLogos.Span3SeatSchurGateConsume` landed the
consumption of items 2/3 from GATE-2. This module
DISCHARGES G2c and states the combined all-items theorem:
**G2c DISCHARGED at `4 ≤ N`** through the re-pinned
interface; K-F2-2 does NOT fire at `4 ≤ N` (it fired at
`N = 2` in GATE-2, whose record stands); the proof needs
no integrability hypotheses (they gate items 2/3, not
item 1) — it is pointwise identities plus
measure-preserving substitution plus the landed twirl
invariances. With the Consume brick, ALL FIVE re-pinned
gate Props are now theorems at `4 ≤ N`.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, on the face:** the discharged gate is the
weld's DECISION GATE only — GATE-3 (the seat-factor
expansion), GATE-4 (the assembly) and F2-W3 itself
remain OPEN behind it; the gate + W3 prove neither FACT
nor clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and
uniformity remain open. Factoring `𝒜` itself is
FORBIDDEN — nothing here touches it; no Gram
factorization of `𝒜` appears or is used anywhere in
this module.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGateLift
import ThetLogos.Span3SeatSchurGateConsume

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateG2c

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **G2c DISCHARGED at `4 ≤ N`.** The re-pinned item-1
Prop holds: for every bounded measurable strict-half
observable `f` and every layer function `φ`, both the
pos-twirled and the mirror-twirled dressed observables'
top fiber averages are gauge-invariant layer
observables. The hypotheses `hf` / `hfbdd` are in fact
not needed — the invariance is pointwise identities
plus measure-preserving substitution plus the landed
twirl invariances. -/
theorem fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved
    (hN : Even N) (hN4 : 4 ≤ N) :
    fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4
      μG hN hN4 := by
  intro f φ _hf _hfbdd
  constructor
  · -- Pos conjunct: the twirl is `posGaugeAvg`, the
    -- substitution is the stratum gauge substitution at
    -- the pos lift `layerGaugeLift γ`.
    intro γ u
    rw [fiberAvgTop_eq_spliceTop μG hN _
          (layerGaugeAction γ u),
      fiberAvgTop_eq_spliceTop μG hN _ u]
    calc (∫ z, (posGaugeAvg μG f) (spliceTop hN z
              (layerGaugeAction γ u))
            * φ (tauBot hN (spliceTop hN z
              (layerGaugeAction γ u)))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = ∫ z, (posGaugeAvg μG f) (spliceTop hN z
              (layerGaugeAction γ u)) * φ (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [tauBot_spliceTop_of_four_le hN hN4])
      _ = ∫ z, (posGaugeAvg μG f) (spliceTop hN
              (gaugePosFun (layerGaugeLift γ) z)
              (layerGaugeAction γ u))
            * φ (tauBot hN
              (gaugePosFun (layerGaugeLift γ) z))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          ((measurePreserving_gaugeStratumEquiv μG
              (fun m : ↥(posLinks (N := N)) => m.1)
              (layerGaugeLift γ)).integral_comp
            (gaugeStratumEquiv
              (fun m : ↥(posLinks (N := N)) => m.1)
              (layerGaugeLift γ)).measurableEmbedding
            (fun w => (posGaugeAvg μG f)
              (spliceTop hN w (layerGaugeAction γ u))
              * φ (tauBot hN w))).symm
      _ = ∫ z, (posGaugeAvg μG f) (spliceTop hN z u)
            * φ (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [spliceTop_gaugePosFun_lift hN γ z u,
              posGaugeAvg_gauge,
              tauBot_gaugePosFun_lift hN hN4 γ z])
      _ = ∫ z, (posGaugeAvg μG f) (spliceTop hN z u)
            * φ (tauBot hN (spliceTop hN z u))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [tauBot_spliceTop_of_four_le hN hN4])
  · -- Mirror conjunct: the twirl is `mirrorGaugeAvg`,
    -- the substitution is the mirror gauge substitution
    -- at the mirror lift `layerGaugeLiftMirror γ`.
    intro γ u
    rw [fiberAvgTop_eq_spliceTop μG hN _
          (layerGaugeAction γ u),
      fiberAvgTop_eq_spliceTop μG hN _ u]
    calc (∫ z, (mirrorGaugeAvg μG f) (spliceTop hN z
              (layerGaugeAction γ u))
            * φ (tauBot hN (spliceTop hN z
              (layerGaugeAction γ u)))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = ∫ z, (mirrorGaugeAvg μG f) (spliceTop hN z
              (layerGaugeAction γ u)) * φ (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [tauBot_spliceTop_of_four_le hN hN4])
      _ = ∫ z, (mirrorGaugeAvg μG f) (spliceTop hN
              (gaugeMirrorPos (layerGaugeLiftMirror γ) z)
              (layerGaugeAction γ u))
            * φ (tauBot hN
              (gaugeMirrorPos (layerGaugeLiftMirror γ) z))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          ((measurePreserving_mirrorGaugeEquiv μG
              (layerGaugeLiftMirror γ)).integral_comp
            (mirrorGaugeEquiv
              (layerGaugeLiftMirror γ)).measurableEmbedding
            (fun w => (mirrorGaugeAvg μG f)
              (spliceTop hN w (layerGaugeAction γ u))
              * φ (tauBot hN w))).symm
      _ = ∫ z, (mirrorGaugeAvg μG f) (spliceTop hN z u)
            * φ (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [spliceTop_gaugeMirrorPos_lift hN γ z u,
              mirrorGaugeAvg_gauge,
              tauBot_gaugeMirrorPos_lift hN hN4 γ z])
      _ = ∫ z, (mirrorGaugeAvg μG f) (spliceTop hN z u)
            * φ (tauBot hN (spliceTop hN z u))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [tauBot_spliceTop_of_four_le hN hN4])

/-- **All items of the re-pinned gate at `4 ≤ N`.**
Item 1 (G2c), discharged here, together with items 2/3
(G2a/G2b, top and bottom), consumed from GATE-2 by the
Consume brick: all five re-pinned gate Props are
theorems at `4 ≤ N`. -/
theorem repinGate_all_items_at_four_le
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) :
    fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4
        μG hN hN4
      ∧ seatPairing_pullTop_eq_pullTopPairingIter_gate4
          μG ρ hN hN4 β
      ∧ seatPairing_pullBot_eq_pullBotPairingIter_gate4
          μG ρ hN hN4 β
      ∧ seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4
          μG ρ hN hN4 β
      ∧ seatPairing_pullBot_eq_layerPairing_fiberAvg_gate4
          μG ρ hN hN4 β :=
  ⟨fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved
      μG hN hN4,
   seatPairing_pullTop_eq_pullTopPairingIter_gate4_of_integrable
      μG ρ hN hN4 β,
   seatPairing_pullBot_eq_pullBotPairingIter_gate4_of_integrable
      μG ρ hN hN4 β,
   seatPairing_pullTop_eq_layerPairing_fiberAvg_gate4_of_integrable_marg
      μG ρ hN hN4 β,
   seatPairing_pullBot_eq_layerPairing_fiberAvg_gate4_of_integrable_marg
      μG ρ hN hN4 β⟩

end Span3SeatSchurGateG2c

end ThetLogos
