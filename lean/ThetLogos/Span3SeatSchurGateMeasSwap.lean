/-
# GATE-3, Brick 2 — the measurability swap (BRIDGE-COR under `hρmeas`)

The measurability form of the BRIDGE-COR chain, landed beside
the continuity forms, nothing edited: the frozen GATE-3
statement `pullBotKernel_seatFactorApproxExpansion` is proved
here under the single hypothesis

  `hρmeas : Measurable fun g : G => repMatrix ρ g`

in place of `hρcont : Continuous fun g : G => repMatrix ρ g`.

Work order: the hρcont-consumption census of
`whitepaper/gate3-reg-audit-2026-11-04.md` (GATE3-REG-AUDIT).
That census found exactly ONE direct consumption of
continuity in the whole BRIDGE-COR cone — at the root,
`measurable_plaquetteDensity_lf` uses continuity exclusively
as `hρcont.measurable` — and every other in-cone site a
pass-through of `layerKernelFun_memLp` / an `hK` hypothesis,
plus the proof-irrelevant `MemLp` slot inside
`LayerKernelPosAll`. This module replays the chain site by
site under `hρmeas`:

  census #1  `measurable_plaquetteDensity_meas`     (root)
  census #2  `measurable_layerAction_meas`
  census #3  `layerKernelFun_memLp_meas`
  census #4  `LayerKernelPosAll_meas` (def) +
             `layerKernelPosAll_meas_eq` (the two indices
             are the SAME Prop: the slot is proof-irrelevant)
  census #5  `seat_stage_memLp_meas`
  census #6  `seat_stage_eLpNorm_meas`
  census #7  `seatFactorApproxExpansion_of_layerKernelPosAll_meas`
  census #8  `layerKernelPosAll_of_layerKernelPos_meas` (BRIDGE-MAIN)
  census #9  `seatFactorApproxExpansion_of_layerKernelPos_meas`
  census #10 `pullBotKernel_seatFactorApproxExpansion_of_meas`

Out of cone, deliberately not replayed: PB-2
`layerKernelOp_inner_gaugeAvg` (not called by BRIDGE-MAIN;
its content is inlined there — census, excluded sites).

## Scope fence

This lands GATE-3 **at every measurable ρ**. The frozen
statement `pullBotKernel_seatFactorApproxExpansion` itself
remains OPEN after this brick: its remaining gap is exactly
the wild class at β > 0 — seats where
`fun g : G => repMatrix ρ g` is not measurable — and within
that class exactly one lemma (the stratum Boltzmann factor
at a wild seat is not `AEStronglyMeasurable`). This brick
does not touch that lemma and does not claim the frozen
statement outright. NO CLAIM; dials 0/4.
-/

import ThetLogos.Span3SeatSchurPosBridge
import ThetLogos.Span3SeatSchurGateItem5
import ThetLogos.Span3SeatSchurGateItem6
import ThetLogos.LatticeLayerFactor

namespace ThetLogos

open MeasureTheory Finset Filter Topology ComplexInnerProductSpace
open scoped Matrix ENNReal NNReal ComplexOrder

section MeasSwap

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## Census #1 — the root: plaquette density under `hρmeas`

The ONLY direct consumption of regularity in the cone. The
continuity proof of `measurable_plaquetteDensity_lf` uses
`hρcont` exclusively through `hρcont.measurable`; here
`hρmeas` itself is the drop-in term of the same type. -/

omit [MeasurableInv G] in
/-- A single plaquette density is measurable in the ambient
configuration, under the measurability hypothesis
`hρmeas` alone (the `_meas` sibling of
`measurable_plaquetteDensity_lf`; the auto-included
`[MeasurableInv G]` instance is unused at this site and is
omitted — the Prop proved is identical). -/
theorem measurable_plaquetteDensity_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      plaquetteDensity (torusShift N) ρ U x μ ν := by
  have htr : Measurable fun U : Config (Fin 4 → ZMod N) G =>
      (Matrix.trace (repMatrix ρ (plaquette (torusShift N) U x μ ν))).re := by
    refine Complex.measurable_re.comp ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (hρmeas.comp (measurable_plaquette (torusShift N) x μ ν)))
  unfold plaquetteDensity
  exact measurable_const.sub (htr.div_const _)

/-! ## Census #2 — the layer action under `hρmeas`

Pass-through only in the original: it composes
`measurable_plaquetteDensity_lf` with the (regularity-free)
`measurable_layerConfig` and finite sums. -/

/-- The one-layer action is jointly measurable in the
stratum and the two layer data, under the measurability
hypothesis `hρmeas` alone (the `_meas` sibling of
`measurable_layerAction`). -/
theorem measurable_layerAction_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable (fun q : (LayerSite N → G) × (LayerLink N → G)
        × (LayerLink N → G) => layerAction ρ β q.1 q.2.1 q.2.2) := by
  have hsum : Measurable (fun q : (LayerSite N → G) × (LayerLink N → G)
        × (LayerLink N → G) => ∑ c : LayerSite N,
          ∑ ν ∈ Finset.Ioi (0 : Fin 4),
            plaquetteDensity (torusShift N) ρ
              (layerConfig q.1 q.2.1 q.2.2) c.1 0 ν) := by
    refine Finset.measurable_sum _ fun c _ => ?_
    refine Finset.measurable_sum _ fun ν _ => ?_
    exact (measurable_plaquetteDensity_meas ρ hρmeas
      c.1 0 ν).comp measurable_layerConfig
  unfold layerAction
  exact hsum.const_mul β

/-! ## Census #3 — the kernel's `MemLp` under `hρmeas`

One use of the action's measurability (the Boltzmann
factor), then `AEStronglyMeasurable.integral_prod_right'`
and `MemLp.of_bound` with the continuity-free pointwise
bound `layerKernel_norm_le`. -/

/-- The layer kernel is `MemLp 2` on the product layer
space, under the measurability hypothesis `hρmeas` alone
(the `_meas` sibling of `layerKernelFun_memLp`). -/
theorem layerKernelFun_memLp_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g) (β : ℝ) :
    MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
  classical
  have hAsm : Measurable (fun q :
      ((LayerLink N → G) × (LayerLink N → G))
        × (LayerSite N → G) =>
      (q.2, q.1.1, q.1.2)) :=
    measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction_meas ρ hρmeas β).neg))
  have hF : Measurable
      ((fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) =>
          (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
        (fun q : ((LayerLink N → G) × (LayerLink N → G))
              × (LayerSite N → G) =>
          (q.2, q.1.1, q.1.2))) :=
    h1.comp hAsm
  have hA := hF.aestronglyMeasurable.integral_prod_right'
    (μ := (Measure.pi fun _ : LayerLink N => μG).prod
      (Measure.pi fun _ : LayerLink N => μG))
    (ν := Measure.pi fun _ : LayerSite N => μG)
  refine MemLp.of_bound (hA.congr (ae_of_all
    ((Measure.pi fun _ : LayerLink N => μG).prod
      (Measure.pi fun _ : LayerLink N => μG)) fun p => ?_)) _
    (ae_of_all _ fun p => layerKernel_norm_le μG ρ β p.1 p.2)
  rfl

/-! ## Census #4 — `LayerKernelPosAll` under `hρmeas`

`hρcont` appears in the original definition only inside the
proof argument of `PosKernel`: the `MemLp` slot is a `Prop`,
hence proof-irrelevant. The `_meas` re-founding therefore
yields the SAME Prop, not merely an equivalent one —
`layerKernelPosAll_meas_eq` is `rfl`. -/

/-- **The all-of-`L²` positivity hypothesis, measurability
form**: the layer-kernel operator is positive on ALL of
`L²(layer)`, in `PosKernel` sense, founded on
`layerKernelFun_memLp_meas` (the `_meas` sibling of
`LayerKernelPosAll`; by `layerKernelPosAll_meas_eq` it is
the same Prop as any continuity-founded instance). -/
def LayerKernelPosAll_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g) (β : ℝ) :
    Prop :=
  PosKernel (layerKernelFun (N := N) μG ρ β)
    (layerKernelFun_memLp_meas (N := N) μG ρ hρmeas β)

/-- The measurability-founded and continuity-founded
all-of-`L²` positivity hypotheses are the same Prop: the
founding `MemLp` proof sits in a proof-irrelevant slot of
`PosKernel`. -/
theorem layerKernelPosAll_meas_eq
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρmeas : Measurable fun g : G => repMatrix ρ g) (β : ℝ) :
    LayerKernelPosAll_meas (N := N) μG ρ hρmeas β
      = LayerKernelPosAll (N := N) μG ρ hρcont β :=
  rfl

/-! ## Census #5 — one stage at the seat is `MemLp 2`,
under `hρmeas` (pass-through of census #3). -/

/-- **One stage at the seat is `MemLp 2`**, under the
measurability hypothesis `hρmeas` alone (the `_meas`
sibling of `seat_stage_memLp`). -/
theorem seat_stage_memLp_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (F : Finset ι) {m : ℕ} (v : Fin m → (↥F → ℂ)) :
    MemLp (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ k, ((1 : ℝ) : ℂ)
            * (⇑(gramFactor b F v k) (tauBot hN p.1)
              * (starRingEnd ℂ)
                (⇑(gramFactor b F v k) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  rw [seat_stage_fun_eq μG ρ hN β b F v]
  exact (((layerKernelFun_memLp_meas μG ρ hρmeas β).sub
    (gramKernelOf_memLp b F v)).comp_measurePreserving
    (measurePreserving_swapTauBot μG hN)).star

/-! ## Census #6 — one stage's HS distance at the seat,
under `hρmeas` (pass-through of census #3). -/

/-- **One stage's HS distance is the same at the seat as
at the layer**, under the measurability hypothesis
`hρmeas` alone (the `_meas` sibling of
`seat_stage_eLpNorm`). -/
theorem seat_stage_eLpNorm_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (F : Finset ι) {m : ℕ} (v : Fin m → (↥F → ℂ)) :
    (eLpNorm (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ k, ((1 : ℝ) : ℂ)
            * (⇑(gramFactor b F v k) (tauBot hN p.1)
              * (starRingEnd ℂ)
                (⇑(gramFactor b F v k) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal
    = (eLpNorm (fun q => layerKernelFun μG ρ β q
          - gramKernelOf b F v q)
        2 ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG))).toReal := by
  have hDiff : MemLp (fun q => layerKernelFun μG ρ β q
        - gramKernelOf b F v q) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) :=
    (layerKernelFun_memLp_meas μG ρ hρmeas β).sub
      (gramKernelOf_memLp b F v)
  rw [seat_stage_fun_eq μG ρ hN β b F v, eLpNorm_star,
    eLpNorm_comp_measurePreserving hDiff.aestronglyMeasurable
      (measurePreserving_swapTauBot μG hN)]

/-! ## Census #7 — the item-5 conditional headline under
`hρmeas`: the compression route with the `_meas` family
fed to the (regularity-free) `exists_seq_tendsto` and
`layerKernelFun_selfAdjoint` `hK` slots. -/

/-- **ITEM 5, conditional headline, measurability form**:
under the measurability hypothesis `hρmeas` and the
all-of-`L²` positivity hypothesis `LayerKernelPosAll_meas`,
the frozen `SeatFactorApproxExpansion` holds — at every
`Even N` (the `_meas` sibling of
`seatFactorApproxExpansion_of_layerKernelPosAll`). -/
theorem seatFactorApproxExpansion_of_layerKernelPosAll_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g)
    (hN : Even N) {β : ℝ}
    (hAll : LayerKernelPosAll_meas (N := N) μG ρ hρmeas β) :
    SeatFactorApproxExpansion μG ρ hN β := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG))
  obtain ⟨Fseq, mseq, vseq, hlim⟩ := exists_seq_tendsto
    (layerKernelFun_memLp_meas μG ρ hρmeas β) b hAll
    (layerKernelFun_selfAdjoint μG ρ hN β
      (layerKernelFun_memLp_meas μG ρ hρmeas β))
  refine ⟨fun n => Fin (mseq n), fun n => inferInstance,
    fun _ _ => 1,
    fun n k => ⇑(gramFactor b (Fseq n) (vseq n) k),
    fun n _i => zero_le_one, ?_, ?_⟩
  · intro n
    exact seat_stage_memLp_meas μG ρ hρmeas hN β b (Fseq n)
      (vseq n)
  · exact hlim.congr fun n =>
      (seat_stage_eLpNorm_meas μG ρ hρmeas hN β b (Fseq n)
        (vseq n)).symm

/-! ## Census #8 — BRIDGE-MAIN under `hρmeas`

One production (`hK := layerKernelFun_memLp_meas`); every
other step of the original (the `integralKernelOp_inner`
formula, the `layerPairingProd` transports with `hK` as
hypothesis, the `gaugeAvg` API,
`layerPairing_nonneg_of_layerKernelPos`) is regularity-free
and consumed unchanged. -/

/-- **BRIDGE-MAIN, measurability form**: positivity of the
layer pairing on gauge-invariant observables implies
positivity of the layer-kernel operator on ALL of
`L²(layer)` — `LayerKernelPos` (under `hρmeas`) implies
`LayerKernelPosAll_meas` (the `_meas` sibling of
`layerKernelPosAll_of_layerKernelPos`). -/
theorem layerKernelPosAll_of_layerKernelPos_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hPos : LayerKernelPos (N := N) μG ρ β) :
    LayerKernelPosAll_meas (N := N) μG ρ hρmeas β := by
  intro f
  obtain ⟨F', hF'sm, hF'ae⟩ :=
    MeasureTheory.Lp.aestronglyMeasurable f
  have hF'meas : Measurable F' := hF'sm.measurable
  have hF'Lp : MemLp F' 2
      (Measure.pi fun _ : LayerLink N => μG) := by
    show eLpNorm F' 2
      (Measure.pi fun _ : LayerLink N => μG) < ∞
    rw [← eLpNorm_congr_ae hF'ae]
    exact Lp.memLp f
  have hK : MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) :=
    layerKernelFun_memLp_meas μG ρ hρmeas β
  have e1 : ⟪f, integralKernelOp
        (layerKernelFun_memLp_meas μG ρ hρmeas β) f⟫
      = layerPairingProd μG ρ β F' :=
    (integralKernelOp_inner hK f f).trans
      (layerPairingProd_congr_ae μG ρ β hF'ae)
  have e2 : layerPairingProd μG ρ β F'
      = layerPairing μG ρ β (gaugeAvg μG F') :=
    (layerPairingProd_gaugeAvg μG ρ hN β hK hF'meas
      hF'Lp).trans
      (layerPairingProd_eq_layerPairing μG ρ hK
        (gaugeAvg_memLp μG hF'meas hF'Lp))
  have hnn : 0 ≤ (layerPairing μG ρ β (gaugeAvg μG F')).re :=
    layerPairing_nonneg_of_layerKernelPos μG ρ β hPos _
      (gaugeAvg_gauge_invariant μG F')
  rw [e1, e2]
  exact hnn

/-! ## Census #9 — BRIDGE-COR step under `hρmeas`:
pure composition of census #7 and census #8. -/

/-- **BRIDGE-COR step, measurability form**:
`SeatFactorApproxExpansion` under `LayerKernelPos` +
`hρmeas` alone (the `_meas` sibling of
`seatFactorApproxExpansion_of_layerKernelPos`). -/
theorem seatFactorApproxExpansion_of_layerKernelPos_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g)
    (hN : Even N) {β : ℝ}
    (hPos : LayerKernelPos (N := N) μG ρ β) :
    SeatFactorApproxExpansion μG ρ hN β :=
  seatFactorApproxExpansion_of_layerKernelPosAll_meas μG ρ
    hρmeas hN (layerKernelPosAll_of_layerKernelPos_meas μG ρ
      hρmeas hN β hPos)

/-! ## Census #10 — BRIDGE-COR, frozen form, under `hρmeas`:
pure composition of census #9. The frozen statement itself
is NOT claimed: the hypothesis `hρmeas` is exactly the
measurable-class half of its remaining gap. -/

/-- **BRIDGE-COR, frozen form, measurability form**: the
frozen GATE-0 item-5 headline
`pullBotKernel_seatFactorApproxExpansion` holds under
`hρmeas` — at every `Even N` and every `β ≥ 0`,
`LayerKernelPos` implies the approximating expansion, at
every measurable `ρ` (the `_meas` sibling of
`pullBotKernel_seatFactorApproxExpansion_of_cont`). -/
theorem pullBotKernel_seatFactorApproxExpansion_of_meas
    (hρmeas : Measurable fun g : G => repMatrix ρ g) :
    pullBotKernel_seatFactorApproxExpansion (N := N) μG ρ :=
  fun hN _β _hβ hPos =>
    seatFactorApproxExpansion_of_layerKernelPos_meas μG ρ
      hρmeas hN hPos

end MeasSwap

end ThetLogos
