/-
# GATE-3, Brick 3 — the wild class: vanishing, the zero-kernel
halves, and the composition modulo ONE named lemma

Commissioned by Jeff 2026-11-04 ("fire all", GATE-3 front,
Brick 3). Contract: `whitepaper/gate3-reg-audit-2026-11-04.md`
(GATE3-REG-AUDIT, Workstream 2). Landed beside the existing
statements, **nothing edited**: the frozen GATE-3 statement
`pullBotKernel_seatFactorApproxExpansion`
(`Span3SeatSchurGatePost`, item 5) and the Brick-2 sibling
`pullBotKernel_seatFactorApproxExpansion_of_meas` are
untouched.

## What this module lands

The audit reduced the whole wild class to one lemma — at a
wild seat (`¬ Measurable fun g : G => repMatrix ρ g`) and
`β > 0`, the stratum Boltzmann factor is not
`AEStronglyMeasurable` in the stratum variable. That lemma is
isolated here as the named Prop `Gate3WildLemma`, and
everything downstream of it is proved:

* `layerKernel_eq_zero_of_not_aestronglyMeasurable` —
  the vanishing (component 2): if the Boltzmann factor is
  not `AEStronglyMeasurable` for all layer data `u u'`, it
  is not `Integrable`, so the Bochner integral defining
  `layerKernel` is `0` by the pinned Mathlib convention
  (`integral_undef`).
* `pullBotKernel_eq_zero_of_not_aestronglyMeasurable` —
  the same for the pullback kernel (a plain pullback of
  `layerKernel`; no ratio form, per audit (a)).
* `layerKernel_eq_zero_of_gate3WildLemma` — the vanishing
  at a wild seat, from the named lemma.
* `layerKernelPos_of_layerKernel_eq_zero` — audit (c),
  first half: at `layerKernel ≡ 0`, `LayerKernelPos` is
  `0 ≤ 0` by its verbatim definition (the pairing
  integrand is pointwise `0`).
* `seatFactorApproxExpansion_of_pullBotKernel_eq_zero` —
  audit (c), second half: at `pullBotKernel ≡ 0`, the
  approximating expansion is the explicit zero Gram family
  (`ι n = PUnit`, `c = 0`, `φ = 0`); the difference kernel
  is identically `0`, hence `MemLp 2` with HS norm
  constantly `0`.
* `pullBotKernel_seatFactorApproxExpansion_of_gate3WildLemma`
  — the composition (component 4): **the frozen GATE-3
  headline follows from `Gate3WildLemma`**, by the case
  split — `β = 0` by the landed probe fence
  (`seatFactorApproxExpansion_zero`, unconditional);
  `β > 0` measurable `ρ` by Brick 2
  (`seatFactorApproxExpansion_of_layerKernelPos_meas`);
  `β > 0` wild `ρ` by the vanishing above, which
  discharges the conclusion outright (the
  `LayerKernelPos` hypothesis is not even consumed).

## What this module does NOT land — the obstruction, exactly

`Gate3WildLemma` itself (component 1) is **NOT proved
here**, and the failure is structural, not a shortage of
effort within the band. The audit's rigidity route is a
four-step reduction: Boltzmann factor `AEStronglyMeasurable`
for all `u u'` ⇒ (a.e. sections on the finite stratum
product) trace functions of `repMatrix ρ` are
`AEStronglyMeasurable` ⇒ (nondegeneracy of the trace form
on `span (range ρ)`, a finite-dimensional C*-algebra)
`repMatrix ρ` itself is `AEStronglyMeasurable` with respect
to `μG` ⇒ `repMatrix ρ` is measurable, contradicting
wildness. The last step is **automatic continuity**: a group
homomorphism a.e. equal (Haar) to a measurable function is
continuous, hence Borel measurable. That theorem is **not
in the pinned Mathlib** (grep-verified this session: no
occurrence of "automatic continuity", and no
a.e.-measurable ⇒ measurable result for group
homomorphisms). One leg of its classical proof does exist
in the library — the Steinhaus theorem for Haar measures
(`MeasureTheory/Measure/Haar/Basic.lean`) — but it is
stated for `[IsHaarMeasure μ]` with inner-regularity side
conditions, the remaining passage (Lusin + density: from
a.e.-measurability of the homomorphism to its continuity)
is not a library result, and the proof's Haar–Radon /
local-compactness hypotheses are in any case **not among
this module's frozen section hypotheses** — here `G` is
an abstract second-countable topological group and `μG`
an abstract invariant probability measure, carrying no
`IsHaarMeasure` at all. So in the frozen
generality the lemma is unproved, and the standard proof's
hypotheses are not all in the room. It is **not shown
false**: no counterexample seat is constructed (in the
classical Hausdorff locally-compact reading the lemma is
true, by the automatic-continuity theorem quoted above).

## Scope fence

The frozen GATE-3 statement remains **OPEN** after this
brick: along the vanishing route its remaining gap is now
exactly the one named Prop `Gate3WildLemma`. Even with that
lemma supplied, GATE-3's discharge would close only this
one hypothesis-gate inside item 5's seam: it does **not**
prove `LayerKernelPos`, does **not** close W3 at full
generality, and moves **no dial**. K-GATE-3 did NOT fire
(it fires only on a seat with `LayerKernelPos` proved and
the expansion refuted; no such seat is produced or
approached here).

NO CLAIM; dials 0/4.
-/

import ThetLogos.Span3SeatSchurGateMeasSwap
import ThetLogos.Span3SeatSchurGateProbe

namespace ThetLogos

open MeasureTheory Finset Filter Topology
open scoped Matrix ENNReal NNReal

section Gate3Wild

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## The named gap: the wild lemma itself (component 1,
isolated, NOT proved in this module — see the header for
the exact obstruction). -/

/-- **The GATE-3 wild lemma** — the single remaining lemma
of the wild class, isolated as a named Prop (NOT proved in
this module): at a wild seat (the representation matrix
function is not measurable) and every `β > 0`, the stratum
Boltzmann factor is not `AEStronglyMeasurable` in the
stratum variable, for every pair of layer data. The
composition theorem below proves the frozen GATE-3
headline from this Prop; the audit's rigidity route to the
Prop itself terminates at an automatic-continuity step
that is absent from the pinned Mathlib and whose classical
hypotheses are not all in this section's context. -/
def Gate3WildLemma : Prop :=
  ∀ (β : ℝ), 0 < β →
    (¬ Measurable (fun g : G => repMatrix ρ g)) →
    ∀ u u' : LayerLink N → G,
      ¬ AEStronglyMeasurable
        (fun α : LayerSite N → G =>
          (Real.exp (-(layerAction ρ β α u u')) : ℂ))
        (Measure.pi fun _ : LayerSite N => μG)

/-! ## Component 2 — the vanishing: a non-`AEStronglyMeasurable`
Boltzmann factor has vanishing Bochner integral, by the
pinned convention. The ambient topology/invariance/
probability instances of the section are not consumed by
the vanishing statement and are omitted at it (house
pattern; the Prop proved is identical). -/

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G]
  [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- **The vanishing (component 2)**: if the stratum
Boltzmann factor is not `AEStronglyMeasurable` for every
pair of layer data, then `layerKernel` is identically
`0` — a non-`AEStronglyMeasurable` function is not
`Integrable`, and the Bochner integral of a
non-`Integrable` function is `0` in the pinned convention
(`integral_undef`). -/
theorem layerKernel_eq_zero_of_not_aestronglyMeasurable
    {β : ℝ}
    (h : ∀ u u' : LayerLink N → G,
      ¬ AEStronglyMeasurable
        (fun α : LayerSite N → G =>
          (Real.exp (-(layerAction ρ β α u u')) : ℂ))
        (Measure.pi fun _ : LayerSite N => μG))
    (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u' = 0 := by
  unfold layerKernel
  exact integral_undef (fun hi => h u u' hi.aestronglyMeasurable)

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G]
  [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- **The vanishing for the pullback kernel**: `pullBotKernel`
is a plain pullback of `layerKernel` (audit (a): no ratio
form, no `0/0`), so the vanishing transports verbatim. -/
theorem pullBotKernel_eq_zero_of_not_aestronglyMeasurable
    (hN : Even N) {β : ℝ}
    (h : ∀ u u' : LayerLink N → G,
      ¬ AEStronglyMeasurable
        (fun α : LayerSite N → G =>
          (Real.exp (-(layerAction ρ β α u u')) : ℂ))
        (Measure.pi fun _ : LayerSite N => μG))
    (z z' : ↥(posLinks (N := N)) → G) :
    pullBotKernel μG ρ hN β z z' = 0 :=
  layerKernel_eq_zero_of_not_aestronglyMeasurable μG ρ h _ _

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G]
  [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- **The vanishing at a wild seat**, from the named wild
lemma: at `β > 0` with `repMatrix ρ` non-measurable,
`layerKernel` is identically `0`. -/
theorem layerKernel_eq_zero_of_gate3WildLemma
    (hW : Gate3WildLemma (N := N) μG ρ)
    {β : ℝ} (hβ : 0 < β)
    (hρ : ¬ Measurable (fun g : G => repMatrix ρ g))
    (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u' = 0 :=
  layerKernel_eq_zero_of_not_aestronglyMeasurable μG ρ
    (fun v v' => hW β hβ hρ v v') u u'

/-! ## Component 3 — the zero-kernel halves (audit (c)):
both sides of the frozen Prop hold at the zero kernel.
(The section's ambient instances are not consumed by the
first half and are omitted at it; the Prop proved is
identical.) -/

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G]
  [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- **Audit (c), first half**: at `layerKernel ≡ 0`,
`LayerKernelPos` holds — in its verbatim definition the
pairing integrand is pointwise `0`, both integrals are
`0`, and the inequality is `0 ≤ (0 : ℂ).re = 0`. -/
theorem layerKernelPos_of_layerKernel_eq_zero {β : ℝ}
    (h : ∀ u u' : LayerLink N → G, layerKernel μG ρ β u u' = 0) :
    LayerKernelPos (N := N) μG ρ β := by
  intro F _
  have h0 : (∫ u, ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG)) = 0 := by
    simp only [h, mul_zero, zero_mul, integral_zero]
  rw [h0]
  simp

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **Audit (c), second half**: at `pullBotKernel ≡ 0`,
`SeatFactorApproxExpansion` holds, discharged by the
explicit zero Gram family (`ι n = PUnit`, `c = 0`,
`φ = 0`): the difference kernel is identically `0`, hence
`MemLp 2`, and its HS norm is the constant sequence `0`. -/
theorem seatFactorApproxExpansion_of_pullBotKernel_eq_zero
    (hN : Even N) {β : ℝ}
    (h : ∀ z z' : ↥(posLinks (N := N)) → G,
      pullBotKernel μG ρ hN β z z' = 0) :
    SeatFactorApproxExpansion μG ρ hN β := by
  have hdiff : ∀ (n : ℕ)
      (p : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G)),
      pullBotKernel μG ρ hN β p.1 p.2
        - ∑ _i : PUnit, (0 : ℂ)
            * ((0 : (LayerLink N → G) → ℂ) (tauBot hN p.1)
              * (starRingEnd ℂ)
                ((0 : (LayerLink N → G) → ℂ) (tauBot hN p.2)))
        = 0 := by
    intro n p
    simp [h]
  refine ⟨fun _ => PUnit, fun _ => inferInstance, fun _ _ => 0,
    fun _ _ => 0, fun _ _ => le_refl 0, ?_, ?_⟩
  · intro n
    have hfun : (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ i : PUnit, ((fun _ _ => (0 : ℝ)) n i : ℂ)
              * (((fun _ _ => (0 : (LayerLink N → G) → ℂ)) n i)
                  (tauBot hN p.1)
                * (starRingEnd ℂ)
                  (((fun _ _ => (0 : (LayerLink N → G) → ℂ)) n i)
                    (tauBot hN p.2))))
        = fun _ => 0 := by
      funext p
      exact hdiff n p
    rw [hfun]
    exact memLp_const 0
  · refine Filter.Tendsto.congr (fun n => ?_) tendsto_const_nhds
    show (0 : ℝ) = (eLpNorm
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ _i : PUnit, (0 : ℂ)
              * ((0 : (LayerLink N → G) → ℂ) (tauBot hN p.1)
                * (starRingEnd ℂ)
                  ((0 : (LayerLink N → G) → ℂ) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal
    rw [eLpNorm_congr_ae
      (Filter.Eventually.of_forall (fun p => hdiff n p))]
    simp

/-! ## Component 4 (conditional) — the composition: the
frozen GATE-3 headline follows from the one named lemma. -/

/-- **The composition (component 4, conditional on the
named wild lemma)**: the frozen GATE-3 headline
`pullBotKernel_seatFactorApproxExpansion` — at every
`Even N` and every `β ≥ 0`, under `LayerKernelPos` — holds
whenever `Gate3WildLemma` does, by the three-way split:
`β = 0` by the landed probe fence
(`seatFactorApproxExpansion_zero`, unconditional, the
hypothesis not consumed); `β > 0` at a measurable `ρ` by
Brick 2 (`seatFactorApproxExpansion_of_layerKernelPos_meas`);
`β > 0` at a wild `ρ` by the vanishing, which discharges
the conclusion outright (the hypothesis again not
consumed). With this theorem, the frozen statement's
remaining gap along the vanishing route is exactly the
single named Prop `Gate3WildLemma`. -/
theorem pullBotKernel_seatFactorApproxExpansion_of_gate3WildLemma
    (hW : Gate3WildLemma (N := N) μG ρ) :
    pullBotKernel_seatFactorApproxExpansion (N := N) μG ρ := by
  intro hN β hβ hPos
  rcases eq_or_lt_of_le hβ with h0 | hβpos
  · subst h0
    exact seatFactorApproxExpansion_zero μG ρ hN
  · by_cases hmeas : Measurable (fun g : G => repMatrix ρ g)
    · exact seatFactorApproxExpansion_of_layerKernelPos_meas μG ρ
        hmeas hN hPos
    · exact seatFactorApproxExpansion_of_pullBotKernel_eq_zero μG ρ hN
        (fun z z' =>
          pullBotKernel_eq_zero_of_not_aestronglyMeasurable μG ρ hN
            (fun u u' => hW β hβpos hmeas u u') z z')

end Gate3Wild

end ThetLogos
