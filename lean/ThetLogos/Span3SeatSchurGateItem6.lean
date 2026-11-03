/-
# F2-GATE-ITEM-6: the pairings package feeding GATE-4C

Brick F2-GATE-ITEM-6 of the F2 weld line — GATE-0 item 6's
remaining package, commissioned by Jeff 2026-11-02
("run them") and re-fired 2026-11-03 ("build and run").
The GATE-4C conditional
(`seatSchurTarget_of_approxProductStep_gate4c`, discharged
in `ThetLogos.Span3SeatSchurGate4CProof`) consumes three
inputs this package addresses:

1. **Hypothesis 6 — the dressed factor pairings**
   (item 6's second antecedent, verbatim): the
   `pullTopKernel` pairings of the pos-dressed against
   the mirror-dressed observable, marginal and
   half-action-folded forms. This module proves the
   **off-diagonal fiber identity** (the sesquilinear
   G2b: a `pullTopKernel` seat pairing of two DIFFERENT
   observables is the sesquilinear layer pairing of
   their top fiber averages — GATE-2 landed only the
   diagonal), and discharges the pairings at `4 ≤ N`
   from `LayerKernelPos` + G2c (discharged) **modulo
   three named inputs not landed anywhere**: `hMarg`
   (the banked GATE-2 splice disintegration — carried
   here as a hypothesis of this module's theorems,
   exactly as GATE-2 banked it; it is NOT discharged
   here and NOT added to GATE-4C, whose statement is
   untouched), the **cross identity** (the two twirls'
   dressed fiber averages agree), and, for the folded
   form, the folded fiber averages' gauge invariance.
   The pairing verdict is therefore CONDITIONAL —
   PARTIAL at the package level (see the landing
   dossier). No pairing is restated to make it pass.
2. **`hIntLim` instances**: the GATE-4C target
   integrands are integrable at the seat, under the
   added hypothesis `Continuous fun g => repMatrix ρ g`
   (the regular case the GATE-4C dossier named for
   this future entry) — proved, no other input.
3. **`hIntStage` instances**: the per-stage dressed
   factor integrands are integrable at the seat, under
   the same `Continuous repMatrix` hypothesis plus
   factor measurability and boundedness carried on the
   data (item 1's frozen data carries neither — the
   GATE-4C pin finding; the instances here are for
   data that does carry them, as the compression
   route's finite stages would).

**`hMarg` fence, on the face:** `hMarg` is GATE-2's
second banked input and belongs to the pairings'
discharge route through G2b. This module does not
discharge it; where the fiber identity consumes it,
it appears as an explicit hypothesis of THIS module's
theorems only. GATE-4C's frozen statement is not
modified, and nothing here is stated as discharging
GATE-0 item 6 or any part of
`seatSchurProductStepOpen` (K-GATE-4C-2 respected).

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, restated:** even with every input above
supplied, GATE-4C would still need item 5's expansion
(GATE-3 — the core-chain decision, not this brick);
the gate + W3 prove neither FACT nor clause (a);
`LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity remain open.
No Gram factorization of `𝒜` appears or is used here.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGate4CProof
import ThetLogos.Span3SeatSchurGateG2c
import ThetLogos.GramAssemblyOcc
import ThetLogos.LatticeLayerFactor

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateItem6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## Utility: extraction measurability -/

set_option linter.unusedSectionVars false in
/-- The top extraction is measurable (a coordinate
restriction of the product configuration). -/
theorem measurable_tauTop (hN : Even N) :
    Measurable (tauTop (G := G) hN) :=
  Measurable.of_eval fun ℓ => measurable_pi_apply (embLayerTop hN ℓ)

set_option linter.unusedSectionVars false in
/-- The bottom extraction is measurable. -/
theorem measurable_tauBot (hN : Even N) :
    Measurable (tauBot (G := G) hN) :=
  Measurable.of_eval fun ℓ => measurable_pi_apply (embLayerBot hN ℓ)

/-! ## Utility: joint measurability of the layer kernel -/

set_option linter.unusedSectionVars false in
/-- The layer configuration assembly is jointly
measurable in the stratum and the two layer data: at
each fixed link the assembly reads a fixed coordinate
of one of the three inputs (the branch conditions
depend only on the link). -/
theorem measurable_layerConfig :
    Measurable (fun q : (LayerSite N → G) × (LayerLink N → G)
        × (LayerLink N → G) => layerConfig q.1 q.2.1 q.2.2) := by
  refine Measurable.of_eval fun ℓ => ?_
  by_cases hν : ℓ.2 = 0
  · by_cases ht : (ℓ.1 0).val = 0
    · have hfun : (fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) => layerConfig q.1 q.2.1 q.2.2 ℓ)
          = fun q => q.1 ⟨ℓ.1, ht⟩ := by
        funext q
        show layerConfig q.1 q.2.1 q.2.2 ℓ = q.1 ⟨ℓ.1, ht⟩
        unfold layerConfig
        rw [dite_eq_left hν, dite_eq_left ht]
      rw [hfun]
      exact (measurable_pi_apply _).comp measurable_fst
    · have hfun : (fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) => layerConfig q.1 q.2.1 q.2.2 ℓ)
          = fun _ => (1 : G) := by
        funext q
        show layerConfig q.1 q.2.1 q.2.2 ℓ = 1
        unfold layerConfig
        rw [dite_eq_left hν, dite_eq_right ht]
      rw [hfun]
      exact measurable_const
  · by_cases ht : (ℓ.1 0).val = 0
    · have hfun : (fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) => layerConfig q.1 q.2.1 q.2.2 ℓ)
          = fun q => q.2.1 ⟨ℓ, ht, hν⟩ := by
        funext q
        show layerConfig q.1 q.2.1 q.2.2 ℓ = q.2.1 ⟨ℓ, ht, hν⟩
        unfold layerConfig
        rw [dite_eq_right hν, dite_eq_left ht]
      rw [hfun]
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    · by_cases ht1 : (ℓ.1 0).val = 1
      · have hpt : ∀ q : (LayerSite N → G) × (LayerLink N → G)
              × (LayerLink N → G),
            layerConfig q.1 q.2.1 q.2.2 ℓ
              = q.2.2 ⟨((torusShift N 0).symm ℓ.1, ℓ.2), by
                  have h10 : ℓ.1 0 = 1 := by
                    rw [← ZMod.natCast_zmod_val (ℓ.1 0), ht1, Nat.cast_one]
                  show (((torusShift N 0).symm ℓ.1) 0).val = 0
                  rw [torusShift_symm_apply_coord, Pi.single_eq_same, h10,
                    sub_self]
                  exact ZMod.val_zero, hν⟩ := by
          intro q
          unfold layerConfig
          rw [dite_eq_right hν, dite_eq_right ht, dite_eq_left ht1]
        simp only [hpt]
        exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
      · have hfun : (fun q : (LayerSite N → G) × (LayerLink N → G)
              × (LayerLink N → G) => layerConfig q.1 q.2.1 q.2.2 ℓ)
            = fun _ => (1 : G) := by
          funext q
          show layerConfig q.1 q.2.1 q.2.2 ℓ = 1
          unfold layerConfig
          rw [dite_eq_right hν, dite_eq_right ht, dite_eq_right ht1]
        rw [hfun]
        exact measurable_const

/-- The one-layer action is jointly measurable in the
stratum and the two layer data, under the
representation-continuity hypothesis (the corpus's
kernel-measurability input). -/
theorem measurable_layerAction
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable (fun q : (LayerSite N → G) × (LayerLink N → G)
        × (LayerLink N → G) => layerAction ρ β q.1 q.2.1 q.2.2) := by
  have hsum : Measurable (fun q : (LayerSite N → G) × (LayerLink N → G)
        × (LayerLink N → G) => ∑ c : LayerSite N,
          ∑ ν ∈ Finset.Ioi (0 : Fin 4),
            plaquetteDensity (torusShift N) ρ
              (layerConfig q.1 q.2.1 q.2.2) c.1 0 ν) := by
    refine Finset.measurable_sum _ fun c _ => ?_
    refine Finset.measurable_sum _ fun ν _ => ?_
    exact (measurable_plaquetteDensity_lf ρ hρcont
      c.1 0 ν).comp measurable_layerConfig
  unfold layerAction
  exact hsum.const_mul β

set_option linter.unusedSectionVars false in
/-- **The pulled-back layer kernel is a.e. strongly
measurable on the product configuration space**,
under the representation-continuity hypothesis: joint
measurability of the Boltzmann factor (through
`measurable_layerAction` and the measurable
extractions), then the parametrized-integral
measurability lemma — the same step the corpus's
twirl measurability uses. This is the joint
measurability the GATE-4 pin finding found landed
nowhere at the pin's generality; it is landed here
under the added `Continuous repMatrix` hypothesis,
as the GATE-4C dossier scoped for this entry. -/
theorem aestronglyMeasurable_pullTopKernel
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    AEStronglyMeasurable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullTopKernel μG ρ hN β p.1 p.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  have hAsm : Measurable (fun q : ((↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G)) × (LayerSite N → G) =>
        (q.2, tauTop hN q.1.1, tauTop hN q.1.2)) :=
    measurable_snd.prodMk
      (((measurable_tauTop hN).comp
        (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_tauTop hN).comp
          (measurable_snd.comp measurable_fst)))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
        (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  have hF : Measurable
      ((fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) =>
          (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
        (fun q : ((↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G)) × (LayerSite N → G) =>
          (q.2, tauTop hN q.1.1, tauTop hN q.1.2))) :=
    h1.comp hAsm
  have hA := hF.aestronglyMeasurable.integral_prod_right'
    (μ := (Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (ν := Measure.pi fun _ : LayerSite N => μG)
  refine hA.congr (ae_of_all
    ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) fun p => ?_)
  rfl

/-! ## Utility: the half-action weight bound, unconditional in `d` -/

/-- **The half-action weight bound without the
`0 < d` side condition.** The landed
`GramAssemblyWord.abs_halfActionP_le` routes the
per-plaquette bound through `plaquetteDensity_mem_Icc`
(landed only at `0 < d`); the stage-1 bound
`abs_plaquetteDensity_le_two` gives the same
per-plaquette bound at every `d`, so the assembled
bound holds unconditionally. (GATE-4C's `hIntStage`
carries no `0 < d`; its folded integrability is what
consumes this.) -/
theorem abs_halfActionP_le_two (β : ℝ)
    (z : ↥(posLinks (N := N)) → G) :
    |halfActionP ρ β z|
      ≤ |β| * (2 * ((plaqIndex (N := N)).card : ℝ)) := by
  have hd2 : ∀ p : (Fin 4 → ZMod N) × Fin 4 × Fin 4,
      |plaquetteDensity (torusShift N) ρ (extendP z)
        p.1 p.2.1 p.2.2| ≤ 2 :=
    fun p => abs_plaquetteDensity_le_two ρ (extendP z) p.1 p.2.1 p.2.2
  unfold halfActionP wilsonActionPlus
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  refine ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p _ => hd2 p)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (((plaqIndex (N := N)).filter IsPosPlaq).card : ℝ)
      ≤ ((plaqIndex (N := N)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  linarith [hc]

/-- The folded weight is uniformly bounded by the
explicit exponential constant. -/
theorem norm_exp_neg_halfActionP_le (β : ℝ)
    (z : ↥(posLinks (N := N)) → G) :
    ‖((Real.exp (-(halfActionP ρ β z)) : ℂ))‖
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr
    ((neg_le_abs _).trans (abs_halfActionP_le_two ρ β z))

/-! ## P0/P1: the off-diagonal fiber identity -/

/-- **The sesquilinear layer pairing** (two-argument
form of the landed `layerPairing`): the first
observable sits in the conjugated slot, the second in
the plain slot. On the diagonal it is `layerPairing`
by definition. -/
noncomputable def layerPairing₂ (β : ℝ)
    (F₁ F₂ : (LayerLink N → G) → ℂ) : ℂ :=
  ∫ u : LayerLink N → G, ∫ u' : LayerLink N → G,
      (starRingEnd ℂ) (F₁ u) * layerKernel μG ρ β u u' * F₂ u'
    ∂(Measure.pi fun _ : LayerLink N => μG)
    ∂(Measure.pi fun _ : LayerLink N => μG)

set_option linter.unusedSectionVars false in
/-- The sesquilinear pairing on the diagonal is the
landed diagonal layer pairing, by definition. -/
theorem layerPairing₂_self (β : ℝ) (F : (LayerLink N → G) → ℂ) :
    layerPairing₂ μG ρ β F F = layerPairing μG ρ β F := rfl

/-- **Off-diagonal G2a engine, top.** The two-observable
form of the landed diagonal engine
(`seatPairing_pullTop_eq_iter_of_integrable`): under
the product-integrability hypothesis `hInt` for the
`(a, b)` integrand, the `pullTopKernel` seat pairing
of `a` against `b` is its iterated form — Fubini, the
iterated swap, and the landed per-stratum symmetry
`layerKernel_symm`. -/
theorem seatPairing_pullTop_eq_iter_of_integrable₂ (hN : Even N) (β : ℝ)
    (a b : (↥(posLinks (N := N)) → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        a p.1 * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (b p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :
    seatPairing μG (pullTopKernel μG ρ hN β) a b
      = ∫ z, ∫ z', (starRingEnd ℂ) (b z)
          * layerKernel μG ρ β (tauTop hN z) (tauTop hN z') * a z'
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hswap : ∀ z z' : ↥(posLinks (N := N)) → G,
      a z * (layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
          * (starRingEnd ℂ) (b z'))
        = (starRingEnd ℂ) (b z') * layerKernel μG ρ β (tauTop hN z')
            (tauTop hN z) * a z := by
    intro z z'
    rw [layerKernel_symm μG ρ hN β (tauTop hN z') (tauTop hN z)]
    ring
  unfold seatPairing pullTopKernel
  refine (integral_prod _ hInt).trans ?_
  refine (integral_integral_swap hInt).trans ?_
  exact integral_congr_ae (ae_of_all _ fun z' =>
    integral_congr_ae (ae_of_all _ fun z => hswap z z'))

/-- **P1 — the off-diagonal fiber identity (the
sesquilinear G2b).** Under `hInt` (the `(a, b)`
product integrability) and `hMarg` (GATE-2's banked
splice disintegration, carried here as a hypothesis
exactly as GATE-2 banked it — NOT discharged in this
package), the `pullTopKernel` seat pairing of two
DIFFERENT observables is the sesquilinear layer
pairing of their top fiber averages, with the second
observable's average in the conjugated slot. GATE-2
landed only the diagonal `a = b` form
(`seatPairing_pullTop_eq_layerPairing_fiberAvg_of_integrable_marg`);
this is the off-diagonal assembly the GATE-4C
hypothesis-6 pairings consume. -/
theorem seatPairing_pullTop_eq_layerPairing₂_fiberAvg_of_integrable_marg
    (hN : Even N) (β : ℝ) (a b : (↥(posLinks (N := N)) → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        a p.1 * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (b p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hMarg : ∀ (a' : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a' z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgTop μG hN a' u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG)) :
    seatPairing μG (pullTopKernel μG ρ hN β) a b
      = layerPairing₂ μG ρ β (fiberAvgTop μG hN b)
          (fiberAvgTop μG hN a) := by
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
          congrArg _ (hMarg a (fun u' => layerKernel μG ρ β (tauTop hN z) u'))
      _ = (starRingEnd ℂ) (b z) * ∫ u',
            layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN a u'
          ∂(Measure.pi fun _ : LayerLink N => μG) :=
          congrArg _ (integral_congr_ae (ae_of_all _ fun u' => mul_comm _ _))
  rw [integral_congr_ae (ae_of_all _ hinner)]
  have houter : (∫ z, (starRingEnd ℂ) (b z) * ∫ u',
        layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN a u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN b u) * ∫ u',
        layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG) := by
    have hm := hMarg (fun z => (starRingEnd ℂ) (b z))
      (fun u => ∫ u', layerKernel μG ρ β u u' * fiberAvgTop μG hN a u'
        ∂(Measure.pi fun _ : LayerLink N => μG))
    rw [fiberAvgTop_conj μG hN b] at hm
    exact hm
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

/-! ## P5: the `hIntLim` instances -/

/-- **P5 — the GATE-4C `hIntLim` hypothesis (hypothesis
5), discharged at the seat** under the added
representation-continuity hypothesis
`Continuous fun g => repMatrix ρ g` (the regular case
the GATE-4C dossier named for this entry): for every
a.e.-strongly-measurable bounded seat observable `f`,
both target integrands — the marginal form and the
half-action-folded form — are integrable on the
product configuration space. The marginal's
measurability is the corpus's
`measurable_planeCrossingMarginal`; the twirls' is the
corpus's twirl measurability; the bounds are the
twirl bound `C`, the kernel bound
`Real.exp (|β| * layerBoundConst N)` on each pulled
kernel (the marginal factors as top times bottom),
and the folded-weight bound of this module. The
statement is verbatim GATE-4C's hypothesis 5. -/
theorem hIntLim_of_continuous_repMatrix (hN : Even N) (β : ℝ)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    ∀ (f : (↥(posLinks (N := N)) → G) → ℂ),
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
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  intro f hf hfb
  obtain ⟨C, hC⟩ := hfb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => 1))
  set K : ℝ := Real.exp (|β| * layerBoundConst N) with hKdef
  have hK0 : 0 ≤ K := Real.exp_nonneg _
  set W : ℝ := Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
    with hWdef
  have hW0 : 0 ≤ W := Real.exp_nonneg _
  -- pointwise bounds on the pieces
  have hbTop : ∀ z z' : ↥(posLinks (N := N)) → G,
      ‖pullTopKernel μG ρ hN β z z'‖ ≤ K :=
    fun z z' => layerKernel_norm_le μG ρ β (tauTop hN z) (tauTop hN z')
  have hbBot : ∀ z z' : ↥(posLinks (N := N)) → G,
      ‖pullBotKernel μG ρ hN β z z'‖ ≤ K :=
    fun z z' => layerKernel_norm_le μG ρ β (tauBot hN z') (tauBot hN z)
  have hbMarg : ∀ z z' : ↥(posLinks (N := N)) → G,
      ‖planeCrossingMarginal μG ρ hN β z z'‖ ≤ K * K := by
    intro z z'
    rw [planeCrossingMarginal_eq_pull_mul μG ρ hN β z z']
    exact (norm_mul_le _ _).trans
      (mul_le_mul (hbTop z z') (hbBot z z') (norm_nonneg _) hK0)
  -- a.e. strong measurability of the pieces, on the product
  have hpos : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => (posGaugeAvg μG f) r.1)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (aestronglyMeasurable_posGaugeAvg μG f hf).comp_measurePreserving
      measurePreserving_fst
  have hmir : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => (mirrorGaugeAvg μG f) r.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (aestronglyMeasurable_mirrorGaugeAvg μG f hf).comp_measurePreserving
      measurePreserving_snd
  have hmarg : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        planeCrossingMarginal μG ρ hN β r.1 r.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (measurable_planeCrossingMarginal μG ρ hρcont hN β).aestronglyMeasurable
  have hw : Measurable
      (fun z : ↥(posLinks (N := N)) → G =>
        ((Real.exp (-(halfActionP ρ β z)) : ℂ))) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_halfActionP_lf ρ hρcont β).neg)
  have hw1 : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ((Real.exp (-(halfActionP ρ β r.1)) : ℂ)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (hw.comp measurable_fst).aestronglyMeasurable
  have hw2 : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ((Real.exp (-(halfActionP ρ β r.2)) : ℂ)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (hw.comp measurable_snd).aestronglyMeasurable
  have hconj : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    hmir.star.congr (ae_of_all _ fun r => (starRingEnd_apply _).symm)
  have hconjW : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (starRingEnd ℂ)
          (((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
            * (mirrorGaugeAvg μG f) r.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (hw2.mul hmir).star.congr
      (ae_of_all _ fun r => (starRingEnd_apply _).symm)
  constructor
  · refine Integrable.of_bound (hpos.mul (hmarg.mul hconj)) (C * (K * K * C))
      (ae_of_all _ fun r => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul
      (norm_posGaugeAvg_le μG C f hC r.1) ?_ (by positivity) ?_)
    · refine (norm_mul_le _ _).trans (mul_le_mul (hbMarg r.1 r.2) ?_
        (norm_nonneg _) (by positivity))
      rw [Complex.norm_conj]
      exact norm_mirrorGaugeAvg_le μG C f hC r.2
    · exact hC0
  · refine Integrable.of_bound
      ((hw1.mul hpos).mul (hmarg.mul hconjW)) ((W * C) * (K * K * (W * C)))
      (ae_of_all _ fun r => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (by positivity) ?_)
    · refine (norm_mul_le _ _).trans (mul_le_mul
        (norm_exp_neg_halfActionP_le ρ β r.1)
        (norm_posGaugeAvg_le μG C f hC r.1) (norm_nonneg _) hW0)
    · refine (norm_mul_le _ _).trans (mul_le_mul (hbMarg r.1 r.2) ?_
        (norm_nonneg _) (by positivity))
      rw [Complex.norm_conj]
      refine (norm_mul_le _ _).trans (mul_le_mul
        (norm_exp_neg_halfActionP_le ρ β r.2)
        (norm_mirrorGaugeAvg_le μG C f hC r.2) (norm_nonneg _) hW0)
    · exact mul_nonneg hW0 hC0

/-! ## P6: the `hIntStage` instances -/

/-- **P6 — the GATE-4C `hIntStage` hypothesis
(hypothesis 4), discharged at the seat** under the
added representation-continuity hypothesis
`Continuous fun g => repMatrix ρ g`, for factor data
whose factors are measurable and bounded on the layer
(`hφm`, `hφb` — carried on the data, as the GATE-4C
pin finding scoped: item 1's frozen data carries
neither, so this instance is for data that does, as
the compression route's finite stages would). For
every a.e.-strongly-measurable bounded seat
observable `f` and every stage factor `φ n i`, both
per-stage integrands — the plain form and the
half-action-folded form — are integrable on the
product configuration space. The pulled kernel's
joint measurability is this module's
`aestronglyMeasurable_pullTopKernel`; the factor
compositions use the measurable bottom extraction.
The inner statement is verbatim GATE-4C's
hypothesis 4. -/
theorem hIntStage_of_continuous_repMatrix (hN : Even N) (β : ℝ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (ι : ℕ → Type) (φ : ∀ n, ι n → (LayerLink N → G) → ℂ)
    (hφm : ∀ n i, Measurable (φ n i))
    (hφb : ∀ n i, ∃ C : ℝ, ∀ u, ‖φ n i u‖ ≤ C) :
    ∀ (f : (↥(posLinks (N := N)) → G) → ℂ),
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
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  intro f hf hfb
  obtain ⟨C, hC⟩ := hfb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => 1))
  set K : ℝ := Real.exp (|β| * layerBoundConst N) with hKdef
  have hK0 : 0 ≤ K := Real.exp_nonneg _
  set W : ℝ := Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
    with hWdef
  have hW0 : 0 ≤ W := Real.exp_nonneg _
  have hbK : ∀ z z' : ↥(posLinks (N := N)) → G,
      ‖pullTopKernel μG ρ hN β z z'‖ ≤ K :=
    fun z z' => layerKernel_norm_le μG ρ β (tauTop hN z) (tauTop hN z')
  have hpos : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => (posGaugeAvg μG f) r.1)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (aestronglyMeasurable_posGaugeAvg μG f hf).comp_measurePreserving
      measurePreserving_fst
  have hmir : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => (mirrorGaugeAvg μG f) r.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (aestronglyMeasurable_mirrorGaugeAvg μG f hf).comp_measurePreserving
      measurePreserving_snd
  have hK : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullTopKernel μG ρ hN β r.1 r.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    aestronglyMeasurable_pullTopKernel μG ρ hρcont hN β
  have hw : Measurable
      (fun z : ↥(posLinks (N := N)) → G =>
        ((Real.exp (-(halfActionP ρ β z)) : ℂ))) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_halfActionP_lf ρ hρcont β).neg)
  have hw1 : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ((Real.exp (-(halfActionP ρ β r.1)) : ℂ)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (hw.comp measurable_fst).aestronglyMeasurable
  have hw2 : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ((Real.exp (-(halfActionP ρ β r.2)) : ℂ)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (hw.comp measurable_snd).aestronglyMeasurable
  intro n i
  obtain ⟨Cφ, hCφ⟩ := hφb n i
  have hCφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ (fun _ => 1))
  have hφ₁ : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (φ n i) (tauBot hN r.1))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (((hφm n i).comp (measurable_tauBot hN)).comp
      measurable_fst).aestronglyMeasurable
  have hφ₂ : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (φ n i) (tauBot hN r.2))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (((hφm n i).comp (measurable_tauBot hN)).comp
      measurable_snd).aestronglyMeasurable
  have hconjφ : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2
          * (φ n i) (tauBot hN r.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (hmir.mul hφ₂).star.congr
      (ae_of_all _ fun r => (starRingEnd_apply _).symm)
  have hconjφW : AEStronglyMeasurable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (starRingEnd ℂ)
          (((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
              * (mirrorGaugeAvg μG f) r.2)
            * (φ n i) (tauBot hN r.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    ((hw2.mul hmir).mul hφ₂).star.congr
      (ae_of_all _ fun r => (starRingEnd_apply _).symm)
  constructor
  · refine Integrable.of_bound ((hpos.mul hφ₁).mul (hK.mul hconjφ))
      ((C * Cφ) * (K * (C * Cφ))) (ae_of_all _ fun r => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (by positivity) ?_)
    · refine (norm_mul_le _ _).trans (mul_le_mul
        (norm_posGaugeAvg_le μG C f hC r.1) (hCφ (tauBot hN r.1))
        (norm_nonneg _) hC0)
    · refine (norm_mul_le _ _).trans (mul_le_mul (hbK r.1 r.2) ?_
        (norm_nonneg _) hK0)
      rw [Complex.norm_conj]
      refine (norm_mul_le _ _).trans (mul_le_mul
        (norm_mirrorGaugeAvg_le μG C f hC r.2) (hCφ (tauBot hN r.2))
        (norm_nonneg _) hC0)
    · exact mul_nonneg hC0 hCφ0
  · refine Integrable.of_bound
      (((hw1.mul hpos).mul hφ₁).mul (hK.mul hconjφW))
      (((W * C) * Cφ) * (K * ((W * C) * Cφ)))
      (ae_of_all _ fun r => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (by positivity) ?_)
    · refine (norm_mul_le _ _).trans (mul_le_mul ?_ (hCφ (tauBot hN r.1))
        (norm_nonneg _) (by positivity))
      refine (norm_mul_le _ _).trans (mul_le_mul
        (norm_exp_neg_halfActionP_le ρ β r.1)
        (norm_posGaugeAvg_le μG C f hC r.1) (norm_nonneg _) hW0)
    · refine (norm_mul_le _ _).trans (mul_le_mul (hbK r.1 r.2) ?_
        (norm_nonneg _) hK0)
      rw [Complex.norm_conj]
      refine (norm_mul_le _ _).trans (mul_le_mul ?_ (hCφ (tauBot hN r.2))
        (norm_nonneg _) (by positivity))
      refine (norm_mul_le _ _).trans (mul_le_mul
        (norm_exp_neg_halfActionP_le ρ β r.2)
        (norm_mirrorGaugeAvg_le μG C f hC r.2) (norm_nonneg _) hW0)
    · exact mul_nonneg (mul_nonneg hW0 hC0) hCφ0

/-! ## P2/P3/P4: the dressed pairings and the assembly -/

/-- **P2 — the marginal dressed pairing** (GATE-4C
hypothesis 6, first conjunct). At `4 ≤ N`, under
`LayerKernelPos`, `hInt` (the dressed pair's product
integrability), `hMarg` (banked, carried as a
hypothesis), and the **cross identity** `hCross` —
the pos-dressed and mirror-dressed fiber averages
agree, a named input landed nowhere — the marginal
pairing's real part is nonnegative: the off-diagonal
fiber identity P1 rewrites it as the sesquilinear
layer pairing of the two dressed fiber averages,
`hCross` collapses it to the diagonal, and the
diagonal is nonnegative by `LayerKernelPos` plus the
discharged G2c invariance of the pos-dressed fiber
average. `hf`/`hfb` are hypothesis 6's own prefix. -/
theorem seatPairing_dressed_marginal_nonneg_of_cross
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        ((posGaugeAvg μG f) p.1 * φ' (tauBot hN p.1))
          * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) p.2
              * φ' (tauBot hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hMarg : ∀ (a' : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a' z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgTop μG hN a' u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG))
    (hCross : fiberAvgTop μG hN
        (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
      = fiberAvgTop μG hN
        (fun z => (mirrorGaugeAvg μG f) z * φ' (tauBot hN z))) :
    0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
      (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
      (fun z => (mirrorGaugeAvg μG f) z
        * φ' (tauBot hN z))).re := by
  rw [seatPairing_pullTop_eq_layerPairing₂_fiberAvg_of_integrable_marg
    μG ρ hN β
    (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
    (fun z => (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) hInt hMarg,
    ← hCross, layerPairing₂_self]
  exact layerPairing_nonneg_of_layerKernelPos μG ρ β hLKP _
    (fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4_proved
      μG hN hN4 f φ' hf hfb).1

/-- **P3 — the folded dressed pairing** (GATE-4C
hypothesis 6, second conjunct). Same shape as P2 for
the half-action-folded dressed observables, under
`LayerKernelPos`, `hIntFold`, `hMarg` (banked), the
folded cross identity `hCrossFold`, and the folded
fiber average's gauge invariance `hInvFold` — the
last two named inputs landed nowhere (G2c covers
only the unfolded dressed forms). -/
theorem seatPairing_dressed_folded_nonneg_of_cross
    (hN : Even N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hIntFold : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        (((Real.exp (-(halfActionP ρ β p.1)) : ℂ)
            * (posGaugeAvg μG f) p.1) * φ' (tauBot hN p.1))
          * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
            * (starRingEnd ℂ)
              (((Real.exp (-(halfActionP ρ β p.2)) : ℂ)
                  * (mirrorGaugeAvg μG f) p.2)
                * φ' (tauBot hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hMarg : ∀ (a' : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a' z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgTop μG hN a' u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG))
    (hCrossFold : fiberAvgTop μG hN
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ' (tauBot hN z))
      = fiberAvgTop μG hN
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)))
    (hInvFold : GaugeInvariantLayerObs
      (fiberAvgTop μG hN
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ' (tauBot hN z)))) :
    0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (posGaugeAvg μG f) z * φ' (tauBot hN z))
      (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (mirrorGaugeAvg μG f) z
        * φ' (tauBot hN z))).re := by
  rw [seatPairing_pullTop_eq_layerPairing₂_fiberAvg_of_integrable_marg
    μG ρ hN β
    (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
      * (posGaugeAvg μG f) z * φ' (tauBot hN z))
    (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
      * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) hIntFold hMarg,
    ← hCrossFold, layerPairing₂_self]
  exact layerPairing_nonneg_of_layerKernelPos μG ρ β hLKP _ hInvFold

/-- **P4 — the assembly: GATE-4C hypothesis 6 under
its named inputs.** At `4 ≤ N`, under `LayerKernelPos`
and the banked `hMarg`, hypothesis 6's verbatim
∀-statement (both dressed pairings nonnegative in
real part) holds for every `f`, `φ'` satisfying
hypothesis 6's own prefix AND the per-pair named
inputs: the two dressed product integrabilities, the
two cross identities, and the folded fiber average's
gauge invariance. Those five per-pair inputs are
exactly what remains unlanded for hypothesis 6; this
theorem restates none of them away. -/
theorem gate4c_hyp6_of_named_inputs
    (hN : Even N) (hN4 : 4 ≤ N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (hMarg : ∀ (a' : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a' z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgTop μG hN a' u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG)) :
    ∀ (f : (↥(posLinks (N := N)) → G) → ℂ)
      (φ' : (LayerLink N → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      Integrable
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          ((posGaugeAvg μG f) p.1 * φ' (tauBot hN p.1))
            * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) p.2
                * φ' (tauBot hN p.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
      fiberAvgTop μG hN
          (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
        = fiberAvgTop μG hN
          (fun z => (mirrorGaugeAvg μG f) z
            * φ' (tauBot hN z)) →
      Integrable
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (((Real.exp (-(halfActionP ρ β p.1)) : ℂ)
              * (posGaugeAvg μG f) p.1) * φ' (tauBot hN p.1))
            * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
              * (starRingEnd ℂ)
                (((Real.exp (-(halfActionP ρ β p.2)) : ℂ)
                    * (mirrorGaugeAvg μG f) p.2)
                  * φ' (tauBot hN p.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
      fiberAvgTop μG hN
          (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
            * (posGaugeAvg μG f) z * φ' (tauBot hN z))
        = fiberAvgTop μG hN
          (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
            * (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) →
      GaugeInvariantLayerObs
        (fiberAvgTop μG hN
          (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
            * (posGaugeAvg μG f) z * φ' (tauBot hN z))) →
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
  intro f φ' hf hfb hInt hCross hIntFold hCrossFold hInvFold
  exact ⟨seatPairing_dressed_marginal_nonneg_of_cross μG ρ hN hN4 β
      hLKP f φ' hf hfb hInt hMarg hCross,
    seatPairing_dressed_folded_nonneg_of_cross μG ρ hN β
      hLKP f φ' hIntFold hMarg hCrossFold hInvFold⟩

end Span3SeatSchurGateItem6

end ThetLogos
