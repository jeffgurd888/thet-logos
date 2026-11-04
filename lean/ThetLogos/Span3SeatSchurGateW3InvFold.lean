/-
# W3 REMAINDER R2c: `hInvFold` DISCHARGED at `4 ≤ N`

Brick R2c of the W3 remainder package (scoping dossier
`w3-remainder-scoping-2026-11-03.md` §2, correction 4).
GATE-0 item 6's assembly
(`gate4c_hyp6_of_named_inputs`,
`ThetLogos.Span3SeatSchurGateItem6`) consumes five
per-pair named inputs for GATE-4C hypothesis 6; this
module discharges the fifth, `hInvFold`: the
half-action-folded dressed top fiber average is a
gauge-invariant layer observable,

`GaugeInvariantLayerObs (fiberAvgTop μG hN (fun z =>
  (Real.exp (-(halfActionP ρ β z)) : ℂ)
    * (posGaugeAvg μG f) z * φ' (tauBot hN z)))`,

in exactly the form item 6's `P3`
(`seatPairing_dressed_folded_nonneg_of_cross`) takes
it as a hypothesis. The proof is G2c's discharged
pos-conjunct argument
(`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved`)
carrying one extra factor — the folded weight — and
the weight is invariant under exactly the action the
argument substitutes by (`halfActionP_gaugePosFun`,
landed in `ThetLogos.PlaneCrossingSeparate`, applied
with the G2c lift `layerGaugeLift γ`). No
integrability hypotheses are used, as in G2c: pointwise
identities plus measure-preserving substitution plus
the landed twirl and half-action invariances.
K-W3-INVFOLD does NOT fire: the folded average is not
moved by any layer gauge action, at any even `N` with
`4 ≤ N`, any `β`, any `f`, any `φ'`.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, on the face:** this discharges ONE of
item 6's five named inputs. `hMarg`, the two cross
identities (`hCross`, `hCrossFold`), and the two
dressed integrabilities remain open; hypothesis 6 is
NOT discharged; GATE-4C's frozen statement is
untouched; W3 (`seatSchurProductStepOpen`) remains
OPEN. This kill-shaped absence is a route fact only —
it is not K-F2-2, and nothing here certifies any
pairing's sign. The gate + W3 prove neither FACT nor
clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity
remain open.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGateItem6
import ThetLogos.PlaneCrossingSeparate

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateW3InvFold

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **R2c — `hInvFold` discharged at `4 ≤ N`.** The
half-action-folded dressed top fiber average is a
gauge-invariant layer observable, in the exact form
item 6's folded pairing (P3) and assembly (P4)
consume: for every strict-half observable `f` and
every layer function `φ'`, with no hypotheses on
either,

`GaugeInvariantLayerObs (fiberAvgTop μG hN (fun z =>
  (Real.exp (-(halfActionP ρ β z)) : ℂ)
    * (posGaugeAvg μG f) z * φ' (tauBot hN z)))`.

The proof is G2c's pos-conjunct lift argument with
the folded weight carried through the substitution:
the weight is invariant under the pos gauge action
of the lift (`halfActionP_gaugePosFun`), the twirl
under its own average (`posGaugeAvg_gauge`), and the
bottom extraction under both the splice
(`tauBot_spliceTop_of_four_le`) and the lift
(`tauBot_gaugePosFun_lift`). -/
theorem fiberAvgTop_gaugeInvariant_of_folded_twirled_mul_pullback_proved
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ) :
    GaugeInvariantLayerObs
      (fiberAvgTop μG hN
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ' (tauBot hN z))) := by
  intro γ u
  rw [fiberAvgTop_eq_spliceTop μG hN _
        (layerGaugeAction γ u),
    fiberAvgTop_eq_spliceTop μG hN _ u]
  calc (∫ z, (Real.exp
              (-(halfActionP ρ β
                (spliceTop hN z (layerGaugeAction γ u)))) : ℂ)
            * (posGaugeAvg μG f)
              (spliceTop hN z (layerGaugeAction γ u))
            * φ' (tauBot hN
              (spliceTop hN z (layerGaugeAction γ u)))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ z, (Real.exp
              (-(halfActionP ρ β
                (spliceTop hN z (layerGaugeAction γ u)))) : ℂ)
            * (posGaugeAvg μG f)
              (spliceTop hN z (layerGaugeAction γ u))
            * φ' (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [tauBot_spliceTop_of_four_le hN hN4])
    _ = ∫ z, (Real.exp
              (-(halfActionP ρ β
                (spliceTop hN
                  (gaugePosFun (layerGaugeLift γ) z)
                  (layerGaugeAction γ u)))) : ℂ)
            * (posGaugeAvg μG f)
              (spliceTop hN
                (gaugePosFun (layerGaugeLift γ) z)
                (layerGaugeAction γ u))
            * φ' (tauBot hN
              (gaugePosFun (layerGaugeLift γ) z))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          ((measurePreserving_gaugeStratumEquiv μG
              (fun m : ↥(posLinks (N := N)) => m.1)
              (layerGaugeLift γ)).integral_comp
            (gaugeStratumEquiv
              (fun m : ↥(posLinks (N := N)) => m.1)
              (layerGaugeLift γ)).measurableEmbedding
            (fun w => (Real.exp
                (-(halfActionP ρ β
                  (spliceTop hN w (layerGaugeAction γ u)))) : ℂ)
              * (posGaugeAvg μG f)
                (spliceTop hN w (layerGaugeAction γ u))
              * φ' (tauBot hN w))).symm
    _ = ∫ z, (Real.exp
              (-(halfActionP ρ β (spliceTop hN z u))) : ℂ)
            * (posGaugeAvg μG f) (spliceTop hN z u)
            * φ' (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [spliceTop_gaugePosFun_lift hN γ z u,
              halfActionP_gaugePosFun ρ hN β,
              posGaugeAvg_gauge,
              tauBot_gaugePosFun_lift hN hN4 γ z])
    _ = ∫ z, (Real.exp
              (-(halfActionP ρ β (spliceTop hN z u))) : ℂ)
            * (posGaugeAvg μG f) (spliceTop hN z u)
            * φ' (tauBot hN (spliceTop hN z u))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_congr_ae (ae_of_all _ fun z => by
            dsimp only
            rw [tauBot_spliceTop_of_four_le hN hN4])

end Span3SeatSchurGateW3InvFold

end ThetLogos
