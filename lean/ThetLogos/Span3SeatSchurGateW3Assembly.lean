/-
# W3 remainder R6: the final assembly at the factor class

R6 — the W3 final assembly, fired under Jeff's registered
decisions of 2026-11-03 (23:11: "R6 enters at the factor
class"; 23:14: "open it" — the gate fires when the cross
pair has landed and been integrated; it has). This module
assembles hypothesis 6's discharge AT THE FACTOR CLASS and
the resulting W3 expansion headline at exactly that scope.

## What is proved here

1. **Regularity of the fiber average** (the use-site
   infrastructure): for a strict-half observable in
   `MemLp 2` on the seat pi probability space, its top
   fiber average is a.e. strongly measurable and
   integrable on the layer pi space — fiber averaging is
   an `L¹` contraction, proved through the assemble
   transport (the coordinate split at the top finset,
   the pi-congruence along the embedding equivalence).

2. **P1 at the factor class**
   (`seatPairing_pullTop_eq_layerPairing₂_fiberAvg_factor`):
   item 6's off-diagonal fiber identity P1 with the
   banked `hMarg` — the ∀-form R1 KILLED as false in the
   non-integrable junk regime (K-W3-HMARG-FORM) — replaced
   by R1's re-pin `fiberAvgTop_marginal_of_integrable`,
   its integrability side condition DISCHARGED at each
   of P1's internal use sites (the inner kernel site,
   the outer conjugate site, and the final layer site)
   from the factor-class data (`MemLp 2` observables,
   the uniform layer-kernel bound, and the
   factor-class Cauchy–Schwarz core of R2d+R3a).
   This is the wiring R1's landing left to R6.

3. **Hypothesis 6 at the factor class**
   (`gate4c_hyp6_at_factor_class`): item 6's assembly
   P4 in shape, with all five of its per-pair named
   inputs discharged at the factor class — the
   marginal identity by R1's re-pin inside the
   P1-variant; the two dressed integrabilities in
   their exact consumption shapes by the
   factor-class Cauchy–Schwarz core at the dressed
   `MemLp 2` slots (the dressed observables'
   membership by R2d+R3a's factor pullback and
   bounded-multiple lemmas; R2d+R3a's packaged
   dressed integrabilities are an independent
   discharge of the same shapes); the two cross
   identities (R2b; consumption credit with R2b's
   module, R2a's independent proof also on the
   record); the folded invariance (R2c) — over
   standing `LayerKernelPos`, for every observable
   satisfying hypothesis 6's own prefix and every
   layer factor in the factor class (`MemLp 2` on
   the layer pi measure — the class item 5's
   expansion factors live in).

4. **The factor-class variant of the GATE-4C
   conditional's application**
   (`seatSchurTarget_of_approxProductStep_factor`): the
   discharged conditional
   `seatSchurTarget_of_approxProductStep_gate4c_proved`
   re-proved with hypothesis 6 required ONLY at the
   expansion's own factors (with their `MemLp 2`
   membership carried on the data). GATE-4C's proof
   applies `hPair` only at those factors; this variant
   is a NEW registry entry under a new name, per the
   K-GATE-4C-2 / K-F2-3 discipline: it is NOT item 6,
   NOT the frozen GATE-4, and it does not prove the
   frozen conditional's hypothesis 6 at ∀-generality.

5. **The headline**
   (`seatSchurProductStepOpen_discharge_gate4_factor`):
   at every even `N` with `4 ≤ N`, every `β`, at
   `0 < d`, under the representation-continuity
   hypothesis `hρcont`, the re-pinned W3 headline
   `seatSchurProductStepOpen` holds — with
   `SeatSchurTarget`'s own internal hypotheses
   (`0 ≤ β`, `LayerKernelPos`) consumed in its own
   registered form. The expansion data is item 5's own
   gram-factor data (the bridge
   `layerKernelPosAll_of_layerKernelPos` discharges
   `LayerKernelPosAll` from `LayerKernelPos` + `hρcont`;
   the compression sequence is re-derived in gram form
   so its factors' factor-class membership is on the
   face), hypothesis 4 comes from R2d+R3a's factor-class
   entry, hypothesis 5 from item 6 P5, hypothesis 6
   from (3) at the factors.

## Scope fences (on every face)

- The frozen ∀-forms of hypotheses 4 and 6 are NOT
  proved and NOT claimed: hypothesis 6 closes AT THE
  FACTOR CLASS ONLY; hypothesis 4 is consumed at the
  factor class (R2d+R3a's entry) and in item 6 P6's
  regular case elsewhere — arbitrary data is covered
  by neither, and that seam stands.
- `LayerKernelPos` and `hρcont` remain standing
  hypotheses, discharged nowhere in this module.
- W3's remaining item (hyps 4/5 beyond their landed
  scopes) is untouched except as the assembly states.
- GATE-3 untouched; GATE-4C's frozen statement and
  item 6's frozen statements UNEDITED.
- NO CLAIM; dials 0/4. Nothing here proves FACT,
  clause (a), `𝒜 ⪰ 0`, or uniformity.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGate4CProof
import ThetLogos.Span3SeatSchurGateItem6
import ThetLogos.Span3SeatSchurGateMarg
import ThetLogos.Span3SeatSchurGateW3FactorInt
import ThetLogos.Span3SeatSchurGateW3CrossFold
import ThetLogos.Span3SeatSchurGateW3InvFold
import ThetLogos.Span3SeatSchurPosBridge

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateW3Assembly

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## Kernel slices: measurability and the uniform bound -/

omit [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- The layer kernel against a fixed left layer
configuration, pulled back along the top extraction, is
a.e. strongly measurable on the seat: the kernel as a
pair function is `MemLp` (hence a.e. strongly
measurable) on the product layer space under `hρcont`,
composed with the measurable constant-pairing map. -/
theorem aestronglyMeasurable_layerKernel_tauTop_right
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) (x : LayerLink N → G) :
    AEStronglyMeasurable
      (fun z : ↥(posLinks (N := N)) → G =>
        layerKernel μG ρ β x (tauTop hN z))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hAsm : Measurable (fun q :
        ((↥(posLinks (N := N)) → G)) × (LayerSite N → G) =>
      (q.2, x, tauTop hN q.1)) :=
    measurable_snd.prodMk
      (measurable_const.prodMk
        ((measurable_tauTop hN).comp measurable_fst))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  have hF : AEStronglyMeasurable
      ((fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) =>
          (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
        (fun q : ((↥(posLinks (N := N)) → G))
              × (LayerSite N → G) =>
          (q.2, x, tauTop hN q.1)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : LayerSite N => μG)) :=
    (h1.comp hAsm).aestronglyMeasurable
  have hA := hF.integral_prod_right'
  refine hA.congr (ae_of_all _ fun z => ?_)
  rfl

omit [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- The layer kernel against a fixed right layer
configuration, as a function of the top extraction, is
a.e. strongly measurable on the seat. -/
theorem aestronglyMeasurable_layerKernel_tauTop_left
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) (y : LayerLink N → G) :
    AEStronglyMeasurable
      (fun z : ↥(posLinks (N := N)) → G =>
        layerKernel μG ρ β (tauTop hN z) y)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hAsm : Measurable (fun q :
        ((↥(posLinks (N := N)) → G)) × (LayerSite N → G) =>
      (q.2, tauTop hN q.1, y)) :=
    measurable_snd.prodMk
      (((measurable_tauTop hN).comp measurable_fst).prodMk
        measurable_const)
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  have hF : AEStronglyMeasurable
      ((fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) =>
          (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
        (fun q : ((↥(posLinks (N := N)) → G))
              × (LayerSite N → G) =>
          (q.2, tauTop hN q.1, y)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : LayerSite N => μG)) :=
    (h1.comp hAsm).aestronglyMeasurable
  have hA := hF.integral_prod_right'
  refine hA.congr (ae_of_all _ fun z => ?_)
  rfl

/-- **Use-site integrability, kernel slot.** An
`MemLp 2` seat observable times a pulled layer-kernel
slice is integrable on the seat pi probability space:
the observable is integrable (`L² ⊆ L¹` on a finite
measure space) and the slice is a.e. strongly
measurable and uniformly bounded
(`layerKernel_norm_le`). This discharges the
integrability side condition of R1's re-pin at the
kernel-shaped use sites inside P1. -/
theorem integrable_mul_layerKernel_tauTop_right
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {a : (↥(posLinks (N := N)) → G) → ℂ}
    (ha : MemLp a 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (x : LayerLink N → G) :
    Integrable
      (fun z : ↥(posLinks (N := N)) → G =>
        a z * layerKernel μG ρ β x (tauTop hN z))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
  (ha.integrable (by norm_num)).mul_bdd
    (aestronglyMeasurable_layerKernel_tauTop_right μG ρ
      hρcont hN β x)
    (ae_of_all _ fun z => layerKernel_norm_le μG ρ β x _)

/-- **Use-site integrability, conjugate slot.** The
conjugate of an `MemLp 2` seat observable times a
two-sided pulled layer-kernel slice is integrable on
the seat: the same bounded-multiple step, with the
slice read in the other variable. This discharges the
re-pin's side condition at P1's outer (conjugated)
use site after the product-space Fubini chain. -/
theorem integrable_conj_mul_layerKernel_pullTop
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {b : (↥(posLinks (N := N)) → G) → ℂ}
    (hb : MemLp b 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (z' : ↥(posLinks (N := N)) → G) :
    Integrable
      (fun z : ↥(posLinks (N := N)) → G =>
        (starRingEnd ℂ) (b z)
          * layerKernel μG ρ β (tauTop hN z) (tauTop hN z'))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hb2 : MemLp (fun z : ↥(posLinks (N := N)) → G =>
        (starRingEnd ℂ) (b z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    (memLp_congr_ae (Filter.Eventually.of_forall fun z =>
      (starRingEnd_apply _).symm)).mp hb.star
  have hK : AEStronglyMeasurable
      (fun z : ↥(posLinks (N := N)) → G =>
        layerKernel μG ρ β (tauTop hN z) (tauTop hN z'))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    aestronglyMeasurable_layerKernel_tauTop_left μG ρ
      hρcont hN β (tauTop hN z')
  exact (hb2.integrable (by norm_num)).mul_bdd hK
    (ae_of_all _ fun z =>
      layerKernel_norm_le μG ρ β (tauTop hN z) (tauTop hN z'))

/-! ## The assemble transport -/

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] in
/-- Assembly across the top split is the inverse of
the coordinate split: splitting an assembled
configuration returns its two data. -/
theorem splitEquiv_assembleTop (hN : Even N)
    (v : ↥(layerTopFinset hN) → G)
    (w : ↥(layerTopFinset hN)ᶜ → G) :
    splitEquiv (layerTopFinset hN) (assembleTop hN v w)
      = (v, w) := by
  apply Prod.ext
  · funext ℓ
    rw [splitEquiv_fst]
    exact assembleTop_apply_of_mem hN v w ℓ.2
  · funext ℓ
    rw [splitEquiv_snd]
    exact assembleTop_apply_of_not_mem hN v w
      (Finset.mem_compl.mp ℓ.2)

/-- **The assemble transport**: the measurable
equivalence from a layer configuration and the
complementary strict-half coordinates to the full
strict-half configuration — the pi-congruence along
the embedding equivalence on the top split, followed
by the inverse coordinate split. -/
noncomputable def assembleTransport (hN : Even N) :
    ((LayerLink N → G) × (↥(layerTopFinset hN)ᶜ → G))
      ≃ᵐ (↥(posLinks (N := N)) → G) :=
  (MeasurableEquiv.prodCongr
    (MeasurableEquiv.piCongrLeft
      (fun _ : LayerLink N => G)
      (embEquiv (embLayerTop hN)
        (embLayerTop_injective hN)).symm).symm
    (MeasurableEquiv.refl (↥(layerTopFinset hN)ᶜ → G))).trans
    (splitEquiv (layerTopFinset hN)).symm

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] in
/-- The assemble transport assembles: its value at a
layer datum and complementary coordinates is the
assembly across the top split of the transported
datum. -/
theorem assembleTransport_apply (hN : Even N)
    (u : LayerLink N → G)
    (w : ↥(layerTopFinset hN)ᶜ → G) :
    assembleTransport hN (u, w)
      = assembleTop hN
          (u ∘ (embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)).symm) w := by
  have hstep : assembleTransport hN (u, w)
      = (splitEquiv (layerTopFinset hN)).symm
          ((fun m : ↥(layerTopFinset hN) =>
            u ((embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)).symm m)), w) := by
    show (splitEquiv (layerTopFinset hN)).symm
        (MeasurableEquiv.prodCongr _ _ (u, w)) = _
    congr 1
  rw [hstep]
  have h2 : splitEquiv (layerTopFinset hN)
      (assembleTop hN
        (u ∘ (embEquiv (embLayerTop hN)
          (embLayerTop_injective hN)).symm) w)
      = ((fun m : ↥(layerTopFinset hN) =>
          u ((embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)).symm m)), w) :=
    splitEquiv_assembleTop hN _ w
  rw [← h2]
  exact (splitEquiv (layerTopFinset hN)).symm_apply_apply _

set_option linter.unusedSectionVars false in
/-- The assemble transport preserves the measure: the
product of the layer pi measure and the complementary
pi measure maps to the seat pi measure. -/
theorem measurePreserving_assembleTransport (hN : Even N) :
    MeasurePreserving (assembleTransport hN)
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  classical
  set s := layerTopFinset hN with hs
  set e : ↥s ≃ LayerLink N :=
    (embEquiv (embLayerTop hN) (embLayerTop_injective hN)).symm
    with he
  set q : (↥s → G) ≃ᵐ (LayerLink N → G) :=
    MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G) e
    with hq
  have hqmp : MeasurePreserving q
      (Measure.pi fun _ : ↥s => μG)
      (Measure.pi fun _ : LayerLink N => μG) :=
    measurePreserving_piCongrLeft (fun _ : LayerLink N => μG) e
  have hqsymm : MeasurePreserving q.symm
      (Measure.pi fun _ : LayerLink N => μG)
      (Measure.pi fun _ : ↥s => μG) := by
    refine ⟨q.symm.measurable, ?_⟩
    have h := congrArg (Measure.map ⇑q.symm) hqmp.map_eq
    have hcomp : ⇑q.symm ∘ ⇑q = id :=
      funext fun x => q.symm_apply_apply x
    rw [Measure.map_map q.symm.measurable q.measurable,
      hcomp, Measure.map_id] at h
    exact h.symm
  set E : (↥(posLinks (N := N)) → G)
      ≃ᵐ ((↥s → G) × (↥sᶜ → G)) := splitEquiv s with hE
  have hsplit : MeasurePreserving E.symm
      ((Measure.pi fun _ : ↥s => μG).prod
        (Measure.pi fun _ : ↥sᶜ => μG))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    refine ⟨E.symm.measurable, ?_⟩
    have h := congrArg (Measure.map ⇑E.symm)
      (measurePreserving_splitEquiv μG s).map_eq
    have hcomp : ⇑E.symm ∘ ⇑E = id :=
      funext fun x => E.symm_apply_apply x
    rw [Measure.map_map E.symm.measurable
      E.measurable, hcomp, Measure.map_id] at h
    exact h.symm
  have hprod : MeasurePreserving
      (MeasurableEquiv.prodCongr q.symm
        (MeasurableEquiv.refl (↥sᶜ → G)))
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : ↥sᶜ => μG))
      ((Measure.pi fun _ : ↥s => μG).prod
        (Measure.pi fun _ : ↥sᶜ => μG)) :=
    hqsymm.prod (MeasurePreserving.id
      (Measure.pi fun _ : ↥sᶜ => μG))
  exact hsplit.comp hprod

/-! ## Regularity of the fiber average -/

set_option linter.unusedSectionVars false in
/-- **Fiber averaging is regular (measurability).**
For an `MemLp 2` strict-half observable, the top fiber
average is a.e. strongly measurable on the layer pi
space: through R1's complementary-marginal form of
`fiberAvgTop`, it is the partial integral of the
observable composed with the measure-preserving
assemble transport, and partial integrals of a.e.
strongly measurable functions are a.e. strongly
measurable. -/
theorem aestronglyMeasurable_fiberAvgTop_of_memLp
    (hN : Even N)
    {a : (↥(posLinks (N := N)) → G) → ℂ}
    (ha : MemLp a 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    AEStronglyMeasurable (fiberAvgTop μG hN a)
      (Measure.pi fun _ : LayerLink N => μG) := by
  have hJ : AEStronglyMeasurable
      (fun p : (LayerLink N → G)
          × (↥(layerTopFinset hN)ᶜ → G) =>
        a (assembleTransport hN p))
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG)) :=
    ha.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_assembleTransport μG hN)
  have hpart := hJ.integral_prod_right'
  refine hpart.congr (ae_of_all _ fun u => ?_)
  rw [fiberAvgTop_eq_integral_compl μG hN a u]
  exact integral_congr_ae (ae_of_all _ fun w =>
    congrArg a (assembleTransport_apply hN u w))

set_option linter.unusedSectionVars false in
/-- **Fiber averaging is an `L¹` contraction.** For an
`MemLp 2` strict-half observable, the top fiber
average is integrable on the layer pi space: the
assembled integrand is integrable on the product
(transport of the observable's integrability along
the measure-preserving assemble transport), and
partial integrals of integrable functions are
integrable. -/
theorem integrable_fiberAvgTop_of_memLp
    (hN : Even N)
    {a : (↥(posLinks (N := N)) → G) → ℂ}
    (ha : MemLp a 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    Integrable (fiberAvgTop μG hN a)
      (Measure.pi fun _ : LayerLink N => μG) := by
  have hJ : Integrable
      (fun p : (LayerLink N → G)
          × (↥(layerTopFinset hN)ᶜ → G) =>
        a (assembleTransport hN p))
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG)) :=
    ((measurePreserving_assembleTransport μG hN).integrable_comp_emb
      (assembleTransport hN).measurableEmbedding).mpr
      (ha.integrable (by norm_num))
  have hpart := hJ.integral_prod_left
  refine hpart.congr (ae_of_all _ fun u => ?_)
  rw [fiberAvgTop_eq_integral_compl μG hN a u]
  exact integral_congr_ae (ae_of_all _ fun w =>
    congrArg a (assembleTransport_apply hN u w))

/-! ## P1 at the factor class -/

omit [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- The pulled layer kernel, as a function of a seat
configuration and a layer configuration, is a.e.
strongly measurable on the product: through the
kernel's site-integral form, it is the partial
integral of the jointly measurable Boltzmann factor
along the assembly `(w, u, tauTop z)`. -/
theorem aestronglyMeasurable_layerKernel_layer_tauTop
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    AEStronglyMeasurable
      (fun p : ((↥(posLinks (N := N)) → G)
          × (LayerLink N → G)) =>
        layerKernel μG ρ β p.2 (tauTop hN p.1))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
  have hAsm : Measurable (fun q :
        (((↥(posLinks (N := N)) → G) × (LayerLink N → G)))
          × (LayerSite N → G) =>
      (q.2, q.1.2, tauTop hN q.1.1)) :=
    measurable_snd.prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_tauTop hN).comp
          (measurable_fst.comp measurable_fst)))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  have hF : AEStronglyMeasurable
      ((fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) =>
          (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
        (fun q : (((↥(posLinks (N := N)) → G)
                × (LayerLink N → G))) × (LayerSite N → G) =>
          (q.2, q.1.2, tauTop hN q.1.1)))
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)).prod
        (Measure.pi fun _ : LayerSite N => μG)) :=
    (h1.comp hAsm).aestronglyMeasurable
  have hA := hF.integral_prod_right'
  refine hA.congr (ae_of_all _ fun p => ?_)
  rfl

set_option maxHeartbeats 1600000 in
/-- **P1 at the factor class.** Item 6's off-diagonal
fiber identity with the banked marginal hypothesis
`hMarg` REPLACED by R1's re-pin, its integrability
side condition discharged at each of P1's internal
use sites from the factor-class data: the inner
site by the kernel-slice integrability at the pulled
left configuration, the outer site by the two-sided
Fubini chain through the conjugate-slot
integrability, and the final site by the kernel-slice
integrability at the layer configuration. The
product integrability P1 carries as a hypothesis is
itself discharged here, by the factor-class
Cauchy–Schwarz core with slots `(a, conj ∘ b)`.
Conclusion verbatim P1's: the `pullTopKernel` seat
pairing of two `MemLp 2` observables is the
sesquilinear layer pairing of their top fiber
averages. -/
theorem seatPairing_pullTop_eq_layerPairing₂_fiberAvg_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (a b : (↥(posLinks (N := N)) → G) → ℂ)
    (ha : MemLp a 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hb : MemLp b 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    seatPairing μG (pullTopKernel μG ρ hN β) a b
      = layerPairing₂ μG ρ β (fiberAvgTop μG hN b)
          (fiberAvgTop μG hN a) := by
  classical
  have hbconj : MemLp (fun z : ↥(posLinks (N := N)) → G =>
        (starRingEnd ℂ) (b z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    (memLp_congr_ae (Filter.Eventually.of_forall fun z =>
      (starRingEnd_apply _).symm)).mp hb.star
  have hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        a p.1 * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (b p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    integrable_pullTopKernel_mul_of_memLp_slots μG ρ
      hρcont hN β ha hbconj
  rw [seatPairing_pullTop_eq_iter_of_integrable₂ μG ρ hN β a b hInt]
  have hinner : ∀ z : ↥(posLinks (N := N)) → G,
      (∫ z', (starRingEnd ℂ) (b z)
          * layerKernel μG ρ β (tauTop hN z) (tauTop hN z') * a z'
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = (starRingEnd ℂ) (b z) * ∫ u',
          layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN a u'
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    intro z
    calc (∫ z', (starRingEnd ℂ) (b z)
            * layerKernel μG ρ β (tauTop hN z) (tauTop hN z') * a z'
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = (starRingEnd ℂ) (b z) * ∫ z',
            a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun z' => by ring)
      _ = (starRingEnd ℂ) (b z) * ∫ u', fiberAvgTop μG hN a u'
            * layerKernel μG ρ β (tauTop hN z) u'
          ∂(Measure.pi fun _ : LayerLink N => μG) :=
          congrArg _
            (fiberAvgTop_marginal_of_integrable μG hN a
              (fun u' => layerKernel μG ρ β (tauTop hN z) u')
              (integrable_mul_layerKernel_tauTop_right μG ρ
                hρcont hN β ha (tauTop hN z)))
      _ = (starRingEnd ℂ) (b z) * ∫ u',
            layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN a u'
          ∂(Measure.pi fun _ : LayerLink N => μG) :=
          congrArg _ (integral_congr_ae (ae_of_all _ fun u' => mul_comm _ _))
  rw [integral_congr_ae (ae_of_all _ hinner)]
  have hmid : ∀ z : ↥(posLinks (N := N)) → G,
      (∫ z', a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u', layerKernel μG ρ β (tauTop hN z) u'
          * fiberAvgTop μG hN a u'
        ∂(Measure.pi fun _ : LayerLink N => μG) :=
    fun z =>
      (fiberAvgTop_marginal_of_integrable μG hN a
        (fun u' => layerKernel μG ρ β (tauTop hN z) u')
        (integrable_mul_layerKernel_tauTop_right μG ρ
          hρcont hN β ha (tauTop hN z))).trans
        (integral_congr_ae (ae_of_all _ fun u' => mul_comm _ _))
  have hI2 : Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (starRingEnd ℂ) (b p.1)
          * (a p.2 * layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    refine (integrable_pullTopKernel_mul_of_memLp_slots μG ρ
      hρcont hN β hbconj ha).congr
      (Filter.Eventually.of_forall fun p => ?_)
    show (starRingEnd ℂ) (b p.1)
        * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2) * a p.2)
      = (starRingEnd ℂ) (b p.1)
          * (a p.2 * layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2))
    ring
  have hI1 : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (LayerLink N → G) =>
        a p.1 * ((starRingEnd ℂ) (fiberAvgTop μG hN b p.2)
          * layerKernel μG ρ β p.2 (tauTop hN p.1)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
    have hprod1 : Integrable
        (fun p : (↥(posLinks (N := N)) → G) × (LayerLink N → G) =>
          a p.1 * (starRingEnd ℂ) (fiberAvgTop μG hN b p.2))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)) :=
      Integrable.mul_prod (ha.integrable (by norm_num))
        (((memLp_congr_ae (Filter.Eventually.of_forall fun u =>
            (starRingEnd_apply _).symm)).mp
          (memLp_one_iff_integrable.mpr
            (integrable_fiberAvgTop_of_memLp μG hN hb)).star).integrable
          (by norm_num))
    refine (Integrable.bdd_mul hprod1
      (aestronglyMeasurable_layerKernel_layer_tauTop μG ρ
        hρcont hN β)
      (Filter.Eventually.of_forall fun p =>
        layerKernel_norm_le μG ρ β _ _)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    show layerKernel μG ρ β p.2 (tauTop hN p.1)
        * (a p.1 * (starRingEnd ℂ) (fiberAvgTop μG hN b p.2))
      = a p.1 * ((starRingEnd ℂ) (fiberAvgTop μG hN b p.2)
          * layerKernel μG ρ β p.2 (tauTop hN p.1))
    ring
  have houter : (∫ z, (starRingEnd ℂ) (b z) * ∫ u',
        layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN a u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN b u) * ∫ u',
        layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG) := by
    calc (∫ z, (starRingEnd ℂ) (b z) * ∫ u',
          layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN a u'
        ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = ∫ z, ∫ z', (starRingEnd ℂ) (b z)
            * (a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          calc (starRingEnd ℂ) (b z) * ∫ u',
                layerKernel μG ρ β (tauTop hN z) u'
                  * fiberAvgTop μG hN a u'
              ∂(Measure.pi fun _ : LayerLink N => μG)
              = (starRingEnd ℂ) (b z) * ∫ z',
                  a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
                congrArg _ (hmid z).symm
            _ = ∫ z', (starRingEnd ℂ) (b z)
                  * (a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z'))
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
                (integral_const_mul _ _).symm
      _ = ∫ z', ∫ z, (starRingEnd ℂ) (b z)
            * (a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
          integral_integral_swap hI2
      _ = ∫ z', a z' * ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN b u)
            * layerKernel μG ρ β u (tauTop hN z')
          ∂(Measure.pi fun _ : LayerLink N => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          refine integral_congr_ae (ae_of_all _ fun z' => ?_)
          calc (∫ z, (starRingEnd ℂ) (b z)
                * (a z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
              = a z' * ∫ z, (starRingEnd ℂ) (b z)
                  * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
                rw [← integral_const_mul]
                exact integral_congr_ae (ae_of_all _ fun z => by ring)
            _ = a z' * ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN b u)
                  * layerKernel μG ρ β u (tauTop hN z')
                ∂(Measure.pi fun _ : LayerLink N => μG) := by
                congr 1
                have hr := fiberAvgTop_marginal_of_integrable μG hN
                  (fun z => (starRingEnd ℂ) (b z))
                  (fun u => layerKernel μG ρ β u (tauTop hN z'))
                  (integrable_conj_mul_layerKernel_pullTop μG ρ
                    hρcont hN β hb z')
                rwa [fiberAvgTop_conj μG hN b] at hr
      _ = ∫ z', ∫ u, a z'
            * ((starRingEnd ℂ) (fiberAvgTop μG hN b u)
              * layerKernel μG ρ β u (tauTop hN z'))
          ∂(Measure.pi fun _ : LayerLink N => μG)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          refine integral_congr_ae (ae_of_all _ fun z' => ?_)
          show a z' * ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN b u)
                * layerKernel μG ρ β u (tauTop hN z')
              ∂(Measure.pi fun _ : LayerLink N => μG)
            = ∫ u, a z' * ((starRingEnd ℂ) (fiberAvgTop μG hN b u)
                * layerKernel μG ρ β u (tauTop hN z'))
              ∂(Measure.pi fun _ : LayerLink N => μG)
          rw [← integral_const_mul]
      _ = ∫ u, ∫ z', a z'
            * ((starRingEnd ℂ) (fiberAvgTop μG hN b u)
              * layerKernel μG ρ β u (tauTop hN z'))
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : LayerLink N => μG) :=
          integral_integral_swap hI1
      _ = ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN b u) * ∫ u',
            layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
          ∂(Measure.pi fun _ : LayerLink N => μG) := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          calc (∫ z', a z' * ((starRingEnd ℂ) (fiberAvgTop μG hN b u)
                * layerKernel μG ρ β u (tauTop hN z'))
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
              = (starRingEnd ℂ) (fiberAvgTop μG hN b u)
                  * ∫ z', a z' * layerKernel μG ρ β u (tauTop hN z')
                ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
                rw [← integral_const_mul]
                exact integral_congr_ae (ae_of_all _ fun z' => by ring)
            _ = (starRingEnd ℂ) (fiberAvgTop μG hN b u) * ∫ u',
                  layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
                ∂(Measure.pi fun _ : LayerLink N => μG) :=
                congrArg _
                  ((fiberAvgTop_marginal_of_integrable μG hN a
                    (fun u' => layerKernel μG ρ β u u')
                    (integrable_mul_layerKernel_tauTop_right μG ρ
                      hρcont hN β ha u)).trans
                    (integral_congr_ae (ae_of_all _ fun u' => mul_comm _ _)))
  rw [houter]
  unfold layerPairing₂
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show (starRingEnd ℂ) (fiberAvgTop μG hN b u) * ∫ u',
        layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
    = ∫ u', (starRingEnd ℂ) (fiberAvgTop μG hN b u)
        * layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun u' => by ring)

/-! ## P2/P3 at the factor class, and the assembly -/

/-- **P2 at the factor class.** Item 6's marginal
dressed pairing with its per-pair named inputs
discharged at the factor class: `hMarg` by the
P1-variant (R1's re-pin at the use sites), `hInt` by
the factor-class slots core inside that variant at
the dressed `MemLp 2` slots (the dressed observables
are `MemLp 2` by the factor pullback and the
bounded-multiple lemma of R2d+R3a), `hCross` by
R2b's corollary. The remaining inputs are P2's own:
`LayerKernelPos`, the `4 ≤ N` domain, and G2c's
discharged invariance of the pos-dressed fiber
average. -/
theorem seatPairing_dressed_marginal_nonneg_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C)
    (hφ' : MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)) :
    0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
      (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
      (fun z => (mirrorGaugeAvg μG f) z
        * φ' (tauBot hN z))).re := by
  obtain ⟨C, hC⟩ := hfb
  have hΦ : MemLp (fun z : ↥(posLinks (N := N)) → G =>
        φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_factor_pullback μG hN hφ'
  have ha : MemLp
      (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_mul_of_aestronglyMeasurable_bounded μG
      (aestronglyMeasurable_posGaugeAvg μG f hf)
      (fun z => norm_posGaugeAvg_le μG C f hC z) hΦ
  have hb : MemLp
      (fun z => (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_mul_of_aestronglyMeasurable_bounded μG
      (aestronglyMeasurable_mirrorGaugeAvg μG f hf)
      (fun z => norm_mirrorGaugeAvg_le μG C f hC z) hΦ
  rw [seatPairing_pullTop_eq_layerPairing₂_fiberAvg_factor μG ρ
      hρcont hN β
      (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
      (fun z => (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) ha hb,
    ← fiberAvgTop_dressed_marginal_cross_proved μG hN f φ',
    layerPairing₂_self]
  exact layerPairing_nonneg_of_layerKernelPos μG ρ β hLKP _
    (fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved
      μG hN hN4 f φ' hf ⟨C, hC⟩).1

/-- **P3 at the factor class.** Item 6's folded
dressed pairing with its per-pair named inputs
discharged at the factor class: `hMarg` and `hIntFold`
by the P1-variant at the folded dressed `MemLp 2`
slots (the folded twirls are bounded multiples of
the factor pullback, by the half-action weight bound
and the twirl bounds), `hCrossFold` by R2b's
headline, `hInvFold` by R2c's headline — which
carries the `4 ≤ N` domain, so this variant takes
`hN4` where P3 itself took the invariance as a
hypothesis. -/
theorem seatPairing_dressed_folded_nonneg_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C)
    (hφ' : MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)) :
    0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (posGaugeAvg μG f) z * φ' (tauBot hN z))
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (mirrorGaugeAvg μG f) z
        * φ' (tauBot hN z))).re := by
  obtain ⟨C, hC⟩ := hfb
  have hΦ : MemLp (fun z : ↥(posLinks (N := N)) → G =>
        φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_factor_pullback μG hN hφ'
  have hw : Measurable
      (fun z : ↥(posLinks (N := N)) → G =>
        ((Real.exp (-(halfActionP ρ β z)) : ℂ))) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_halfActionP_lf ρ hρcont β).neg)
  have ha : MemLp
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (posGaugeAvg μG f) z * φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_mul_of_aestronglyMeasurable_bounded μG
      (hw.aestronglyMeasurable.mul
        (aestronglyMeasurable_posGaugeAvg μG f hf))
      (fun z => (norm_mul_le _ _).trans (mul_le_mul
        (norm_exp_neg_halfActionP_le ρ β z)
        (norm_posGaugeAvg_le μG C f hC z) (norm_nonneg _)
        (Real.exp_nonneg _))) hΦ
  have hb : MemLp
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_mul_of_aestronglyMeasurable_bounded μG
      (hw.aestronglyMeasurable.mul
        (aestronglyMeasurable_mirrorGaugeAvg μG f hf))
      (fun z => (norm_mul_le _ _).trans (mul_le_mul
        (norm_exp_neg_halfActionP_le ρ β z)
        (norm_mirrorGaugeAvg_le μG C f hC z) (norm_nonneg _)
        (Real.exp_nonneg _))) hΦ
  rw [seatPairing_pullTop_eq_layerPairing₂_fiberAvg_factor μG ρ
      hρcont hN β
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (posGaugeAvg μG f) z * φ' (tauBot hN z))
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) ha hb,
    ← fiberAvgTop_dressed_folded_cross_proved μG ρ hN β f φ',
    layerPairing₂_self]
  exact layerPairing_nonneg_of_layerKernelPos μG ρ β hLKP _
    (fiberAvgTop_gaugeInvariant_of_folded_twirled_mul_pullback_proved
      μG ρ hN hN4 β f φ')

/-- **Hypothesis 6 at the factor class** (the R6
assembly entry): GATE-4C hypothesis 6's verbatim
conclusion — both dressed pairings nonnegative in
real part — for every observable `f` satisfying
hypothesis 6's own prefix (a.e. strongly measurable,
pointwise bounded) and every layer factor `φ'` in
the factor class (`MemLp 2` on the layer pi
measure), at `4 ≤ N`, under `LayerKernelPos` and
`hρcont`. All five of item 6 P4's per-pair named
inputs are discharged: the two dressed
integrabilities and the re-pinned marginal inside
the P1-variant at the dressed slots, the two cross
identities by R2b, the folded invariance by R2c.
This is NOT the frozen ∀-form over bare `φ'`: the
quantification over `φ'` is restricted to the
factor class, exactly as registered. -/
theorem gate4c_hyp6_at_factor_class
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β) :
    ∀ (f : (↥(posLinks (N := N)) → G) → ℂ)
      (φ' : (LayerLink N → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG) →
      0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
        (fun z => (mirrorGaugeAvg μG f) z
          * φ' (tauBot hN z))).re
      ∧ 0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ' (tauBot hN z))
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (mirrorGaugeAvg μG f) z
          * φ' (tauBot hN z))).re := by
  intro f φ' hf hfb hφ'
  exact ⟨seatPairing_dressed_marginal_nonneg_factor μG ρ
      hρcont hN hN4 β hLKP f φ' hf hfb hφ',
    seatPairing_dressed_folded_nonneg_factor μG ρ
      hρcont hN hN4 β hLKP f φ' hf hfb hφ'⟩

/-! ## The variant conditional and the headline -/

/-- **The GATE-4C conditional at the factor class.**
GATE-4C's conditional with hypothesis 6 replaced by
its factor-class form: the expansion data
additionally carries `hφMem` (every factor `MemLp 2`
on the layer pi measure — the class item 5's
expansion factors live in), and the pair input
`hPairFac` is hypothesis 6 required ONLY at the
expansion's factors, with that membership in hand.
Hypotheses 4 and 5 are carried verbatim. The proof
is GATE-4C's discharged proof with the pair input
fed at the factors. This is a variant entry in the
K-GATE-4C-2 discipline: the frozen
`seatSchurTarget_of_approxProductStep_gate4c`, whose
hypothesis 6 quantifies over bare `φ'`, is NOT
proved here. -/
theorem seatSchurTarget_of_approxProductStep_factor
    (hN : Even N) (_hN4 : 4 ≤ N) (β : ℝ) (hd : 0 < d)
    (ι : ℕ → Type) (hfin : ∀ n, Fintype (ι n))
    (c : ∀ n, ι n → ℝ)
    (φ : ∀ n, ι n → (LayerLink N → G) → ℂ)
    (hc : ∀ n i, 0 ≤ c n i)
    (hMem : ∀ n, MemLp
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ i, (c n i : ℂ)
              * ((φ n i) (tauBot hN p.1)
                * (starRingEnd ℂ) ((φ n i) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hTend : Filter.Tendsto
      (fun n => (eLpNorm
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          pullBotKernel μG ρ hN β p.1 p.2
            - ∑ i, (c n i : ℂ)
                * ((φ n i) (tauBot hN p.1)
                  * (starRingEnd ℂ) ((φ n i) (tauBot hN p.2))))
        2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal)
      Filter.atTop (nhds 0))
    (hφMem : ∀ n i, MemLp (φ n i) 2
      (Measure.pi fun _ : LayerLink N => μG))
    (hIntStage : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      ∀ n i, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          ((posGaugeAvg μG f) r.1 * (φ n i) (tauBot hN r.1))
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2
                * (φ n i) (tauBot hN r.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      ∧ Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (((Real.exp (-(halfActionP ρ β r.1)) : ℂ)
              * (posGaugeAvg μG f) r.1)
              * (φ n i) (tauBot hN r.1))
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ)
                (((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
                    * (mirrorGaugeAvg μG f) r.2)
                  * (φ n i) (tauBot hN r.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hIntLim : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (posGaugeAvg μG f) r.1
            * (planeCrossingMarginal μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      ∧ Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          ((Real.exp (-(halfActionP ρ β r.1)) : ℂ)
              * (posGaugeAvg μG f) r.1)
            * (planeCrossingMarginal μG ρ hN β r.1 r.2
              * (starRingEnd ℂ)
                ((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
                  * (mirrorGaugeAvg μG f) r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hPairFac : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ)
      (φ' : (LayerLink N → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG) →
      0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
        (fun z => (mirrorGaugeAvg μG f) z
          * φ' (tauBot hN z))).re
      ∧ 0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ' (tauBot hN z))
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (mirrorGaugeAvg μG f) z
          * φ' (tauBot hN z))).re) :
    SeatSchurTarget μG ρ hN β := by
  let : ∀ n, Fintype (ι n) := hfin
  intro _hβ _hLKP f hf hfbdd
  obtain ⟨C, hC⟩ := hfbdd
  have hpair : ∀ (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) (C₁ C₂ : ℝ),
      (∀ z, ‖k₁ z‖ ≤ C₁) → (∀ z, ‖k₂ z‖ ≤ C₂) →
      (∀ n i, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (k₁ r.1 * (φ n i) (tauBot hN r.1))
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) (k₂ r.2 * (φ n i) (tauBot hN r.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) →
      (∀ n i, 0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
          (fun z => k₁ z * (φ n i) (tauBot hN z))
          (fun z => k₂ z * (φ n i) (tauBot hN z))).re) →
      Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) (k₂ r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
      0 ≤ (seatPairing μG (planeCrossingMarginal μG ρ hN β) k₁ k₂).re := by
    intro k₁ k₂ C₁ C₂ hk₁ hk₂ hI hT hIT
    have hStage : ∀ n, 0 ≤ (seatPairing μG
        (fun z z' => pullTopKernel μG ρ hN β z z'
          * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN z)
              * (starRingEnd ℂ) ((φ n i) (tauBot hN z')))))
        k₁ k₂).re := by
      intro n
      exact seatPairing_mul_nonneg_of_finiteRank μG
        (pullTopKernel μG ρ hN β)
        (fun z z' => ∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN z)
          * (starRingEnd ℂ) ((φ n i) (tauBot hN z'))))
        k₁ k₂ (c n) (hc n)
        (fun i z => (φ n i) (tauBot hN z))
        (fun i z => (φ n i) (tauBot hN z))
        (fun z z' => rfl) (hI n) (hT n)
    have hStageInt : ∀ n, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN r.1)
                * (starRingEnd ℂ) ((φ n i) (tauBot hN r.2))))
            * (starRingEnd ℂ) (k₂ r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
      intro n
      have hpt : ∀ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
              * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN r.1)
                  * (starRingEnd ℂ) ((φ n i) (tauBot hN r.2))))
              * (starRingEnd ℂ) (k₂ r.2))
            = ∑ i, (c n i : ℂ) * ((k₁ r.1 * (φ n i) (tauBot hN r.1))
                * (pullTopKernel μG ρ hN β r.1 r.2
                  * (starRingEnd ℂ) (k₂ r.2
                    * (φ n i) (tauBot hN r.2)))) := by
        intro r
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      rw [show (fun r : (↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G) =>
            k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
              * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN r.1)
                  * (starRingEnd ℂ) ((φ n i) (tauBot hN r.2))))
              * (starRingEnd ℂ) (k₂ r.2)))
          = (fun r : (↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G) =>
            ∑ i, (c n i : ℂ) * ((k₁ r.1 * (φ n i) (tauBot hN r.1))
                * (pullTopKernel μG ρ hN β r.1 r.2
                  * (starRingEnd ℂ) (k₂ r.2
                    * (φ n i) (tauBot hN r.2))))) from funext hpt]
      exact integrable_finsetSum Finset.univ
        (fun i _ => (hI n i).const_mul _)
    have hLim := seatPairing_pullTop_tendsto_of_kernel_approx μG ρ hN β
      k₁ k₂ C₁ C₂ hk₁ hk₂
      (fun n z z' => ∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN z)
        * (starRingEnd ℂ) ((φ n i) (tauBot hN z'))))
      hMem hTend hIT hStageInt
    have hLimRe := (Complex.continuous_re.tendsto _).comp hLim
    exact isClosed_Ici.mem_of_tendsto hLimRe
      (Filter.Eventually.of_forall hStage)
  have hW : ∀ z : ↥(posLinks (N := N)) → G,
      ‖((Real.exp (-(halfActionP ρ β z)) : ℂ))‖
        ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr
      ((neg_le_abs _).trans (GramAssemblyWord.abs_halfActionP_le ρ hd β z))
  have hmarg := hpair (posGaugeAvg μG f) (mirrorGaugeAvg μG f) C C
    (fun z => norm_posGaugeAvg_le μG C f hC z)
    (fun z => norm_mirrorGaugeAvg_le μG C f hC z)
    (fun n i => (hIntStage f hf ⟨C, hC⟩ n i).1)
    (fun n i => (hPairFac f (φ n i) hf ⟨C, hC⟩ (hφMem n i)).1)
    (hIntLim f hf ⟨C, hC⟩).1
  have hfold := hpair
    (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
      * (posGaugeAvg μG f) z)
    (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
      * (mirrorGaugeAvg μG f) z)
    (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) * C)
    (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) * C)
    (fun z => (norm_mul_le _ _).trans (mul_le_mul (hW z)
      (norm_posGaugeAvg_le μG C f hC z) (norm_nonneg _)
      (Real.exp_pos _).le))
    (fun z => (norm_mul_le _ _).trans (mul_le_mul (hW z)
      (norm_mirrorGaugeAvg_le μG C f hC z) (norm_nonneg _)
      (Real.exp_pos _).le))
    (fun n i => (hIntStage f hf ⟨C, hC⟩ n i).2)
    (fun n i => (hPairFac f (φ n i) hf ⟨C, hC⟩ (hφMem n i)).2)
    (hIntLim f hf ⟨C, hC⟩).2
  constructor
  · rw [planeAvgPairing_eq_seatPairing_marginal_fold μG ρ hN β
      (posGaugeAvg μG f) (mirrorGaugeAvg μG f)]
    exact hfold
  · exact hmarg

/-- **R6 HEADLINE — the W3 expansion at the factor
class.** At every `4 ≤ N` (with `Even N`), every
`β`, and every `0 < d`, under
`hρcont : Continuous fun g => repMatrix ρ g`:
`seatSchurProductStepOpen` — the W3 target — holds
modulo its own registered hypotheses
(`0 ≤ β` and `LayerKernelPos β`, intro'd inside the
target). The expansion data is item 5's, re-derived
in Gram form: the bridge
(`layerKernelPosAll_of_layerKernelPos`) turns the
target's `LayerKernelPos` into `LayerKernelPosAll`;
item 5's compression then produces the stages whose
factors are `Lp` elements, hence in the factor
class (`Lp.memLp`); hypothesis 4 at that data is
R2d+R3a's Gram-factor entry; hypothesis 5 is item
6's regular-case entry; hypothesis 6 is this
module's `gate4c_hyp6_at_factor_class`, required
only at the factors via the variant conditional.

SCOPE FENCES: this is the factor-class entry. The
frozen `seatSchurTarget_of_approxProductStep_gate4c`
(whose hypothesis 6 quantifies over bare `φ'`) and
the frozen Repin headline
`seatSchurProductStepOpen_discharge_gate4` are NOT
proved: the Repin headline carries neither `0 < d`
nor `hρcont`, and no route through the factor class
reaches it. `LayerKernelPos` itself is untouched —
it enters through the target's own hypothesis slot.
NO CLAIM; dials 0/4. -/
theorem seatSchurProductStepOpen_discharge_gate4_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ) (hd : 0 < d) :
    seatSchurProductStepOpen μG ρ hN β := by
  intro hβ hLKP
  have hAll : LayerKernelPosAll (N := N) μG ρ hρcont β :=
    layerKernelPosAll_of_layerKernelPos μG ρ hρcont hN β hLKP
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG))
  obtain ⟨Fseq, mseq, vseq, hlim⟩ := exists_seq_tendsto
    (layerKernelFun_memLp μG ρ hρcont β) b hAll
    (layerKernelFun_selfAdjoint μG ρ hN β
      (layerKernelFun_memLp μG ρ hρcont β))
  refine seatSchurTarget_of_approxProductStep_factor μG ρ
    hN hN4 β hd (fun n => Fin (mseq n)) (fun n => inferInstance)
    (fun _ _ => 1)
    (fun n k => ⇑(gramFactor b (Fseq n) (vseq n) k))
    (fun n _i => zero_le_one)
    (fun n => seat_stage_memLp μG ρ hρcont hN β b (Fseq n)
      (vseq n))
    (hlim.congr fun n =>
      (seat_stage_eLpNorm μG ρ hρcont hN β b (Fseq n)
        (vseq n)).symm)
    (fun n k => MeasureTheory.Lp.memLp _)
    (hIntStage_gramFactors μG ρ hρcont hN β b Fseq mseq vseq)
    (hIntLim_of_continuous_repMatrix μG ρ hN β hρcont)
    (gate4c_hyp6_at_factor_class μG ρ hρcont hN hN4 β hLKP)
    hβ hLKP

end Span3SeatSchurGateW3Assembly

end ThetLogos
