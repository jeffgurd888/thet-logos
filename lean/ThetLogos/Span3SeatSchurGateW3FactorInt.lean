/-
# W3 REMAINDER R2d+R3a (merged) — factor-class integrability

Brick R2d+R3a of the W3 remainder package (scoping
dossier `w3-remainder-scoping-2026-11-03.md` §2, merged
entry; price M–L, est. strict 20–45). Fired under
Jeff's full-send grant. This module discharges, at the
**factor class**, the two dressed integrability inputs
that GATE-0 item 6's assembly
(`gate4c_hyp6_of_named_inputs`,
`Span3SeatSchurGateItem6`) carries as per-pair named
inputs for GATE-4C hypothesis 6, and GATE-4C hypothesis
4 (`hIntStage`) for factor data of the same class:

- `hInt` — the plain dressed product integrand
  (pos-twirled observable dressed by `φ' ∘ tauBot hN`,
  against `pullTopKernel` and the conjugated
  mirror-dressed factor) is integrable on the product
  pi space;
- `hIntFold` — the same for the half-action-folded
  dressed integrand.

**The factor class.** As ∀-statements over a bare
layer function `φ'` these integrabilities are not
provable (scoping correction 2: hyp 6's prefix carries
no regularity on `φ'`; for `φ' ∉ L¹(layer)` the dressed
integrand is genuinely non-integrable — the same
junk-regime species as R1's K-W3-HMARG-FORM). The
honest class is the one the assembly actually
consumes: GATE-4C's proof applies its pairing
hypothesis only at `φ' = φ n i`, the expansion's own
factors, and item 5's expansion
(`seatFactorApproxExpansion_of_layerKernelPosAll`)
produces factors `⇑(gramFactor b F v k)` — coeﬃcients
of `Lp ℂ 2` elements, i.e. `MemLp 2` on the layer pi
measure. This module therefore proves both
integrabilities for every `φ'` with
`MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)`,
under the registered headline's seat hypothesis
`hρcont : Continuous fun g => repMatrix ρ g` (which
item 6's `aestronglyMeasurable_pullTopKernel`
consumes), and packages the conclusion in both
consumed shapes: item 6's per-pair input shapes and
GATE-4C hypothesis 4's verbatim ∀-shape restricted to
`MemLp 2` factor data (a factor-class variant entry —
the frozen `hIntStage`, quantified over arbitrary
factor data, is NOT proved here and is not claimed).

**Route** (the scoping's tensor bound): the factor
pullback `φ' ∘ tauBot hN` is `MemLp 2` on the
strict-half pi space (`measurePreserving_tauBot`);
each twirl is a.e. strongly measurable and pointwise
bounded by the observable's own bound, so each dressed
slot function is `MemLp 2` (bounded × `L²`); the
folded weight is a.e. strongly measurable under
`hρcont` and uniformly bounded
(`norm_exp_neg_halfActionP_le`, unconditional in
`d`), so the folded slot functions are `MemLp 2` the
same way; the two slot functions are Cauchy–Schwarz
integrable on the product probability space, and
multiplication by the uniformly bounded, a.e. strongly
measurable pulled kernel (`layerKernel_norm_le`,
`aestronglyMeasurable_pullTopKernel`) preserves
integrability.

**Fences.** This brick discharges the two
integrability INPUTS at the factor class only. It
does not discharge `hIntLim`/`hIntStage` in their
frozen forms (item 6's P5/P6 already discharged them
in the regular case for data carrying pointwise
factor regularity; the frozen `hIntStage` over
arbitrary factor data is a different, unproved
statement), and it does not touch hypotheses 4/5
beyond the regular case — hypotheses 4/5 at bare `ρ`
are off the critical path (scoping R3b, probe only).
Hypothesis 6 as a whole is NOT discharged: the cross
identities `hCross`/`hCrossFold` (R2a/R2b), the
folded invariance `hInvFold` (R2c, landed), the banked
`hMarg` (R1, landed as a re-pin), and the final
assembly (R6, with the parent's variant-entry
decision) remain exactly where the record puts them.
W3 is NOT closed by this brick. `LayerKernelPos`,
FACT, `𝒜 ⪰ 0`, clause (a), and uniformity are
untouched (K-F2-4).

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGateItem5
import ThetLogos.Span3SeatSchurGateItem6

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateW3FactorInt

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## The factor class: pullbacks and bounded multiples -/

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **The factor pullback is `MemLp 2`** on the
strict-half pi space: `tauBot hN` is measure-preserving
(item 5), and `MemLp` transports along it. This is the
single point where the factor class enters: the
expansion's factors are `L²` on the layer, hence their
pullbacks are `L²` at the seat. -/
theorem memLp_factor_pullback (hN : Even N)
    {φ' : (LayerLink N → G) → ℂ}
    (hφ : MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)) :
    MemLp (fun z : ↥(posLinks (N := N)) → G => φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
  hφ.comp_measurePreserving (measurePreserving_tauBot μG hN)

omit [Group G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **A bounded a.e.-strongly-measurable multiple of an
`L²` function is `L²`** (on the probability pi space):
the multiplier is `MemLp ∞` by its pointwise bound, and
Hölder at `(∞, 2, 2)` closes. This is the step that
replaces item 6 P6's pointwise boundedness of the
factor: here the *factor* is the `L²` side and the
*twirl/weight* is the bounded side. -/
theorem memLp_mul_of_aestronglyMeasurable_bounded
    {T Φ : (↥(posLinks (N := N)) → G) → ℂ} {C : ℝ}
    (hT : AEStronglyMeasurable T
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hTb : ∀ z, ‖T z‖ ≤ C)
    (hΦ : MemLp Φ 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    MemLp (fun z => T z * Φ z) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hTtop : MemLp T ∞ (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_top_of_bound hT C (Filter.Eventually.of_forall hTb)
  refine (memLp_congr_ae
    (Filter.Eventually.of_forall fun z => Pi.mul_apply T Φ z)).mp
    (hTtop.mul hΦ)

/-! ## The Cauchy–Schwarz core -/

/-- **Core: two `MemLp 2` slot functions pair
integrably against the pulled top kernel.** The slot
product is integrable on the product probability space
by Cauchy–Schwarz (`HolderTriple 2 2 1`, the corpus's
own instance pattern from `IntegralKernelHS`), and
the pulled kernel — a.e. strongly measurable under
`hρcont` (item 6) and uniformly bounded
(`layerKernel_norm_le`) — preserves integrability
under pointwise multiplication. -/
theorem integrable_pullTopKernel_mul_of_memLp_slots
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {A B : (↥(posLinks (N := N)) → G) → ℂ}
    (hA : MemLp A 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hB : MemLp B 2 (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        A p.1 * (pullTopKernel μG ρ hN β p.1 p.2 * B p.2))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hAfst : MemLp
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => A p.1) 2
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    hA.comp_measurePreserving measurePreserving_fst
  have hBsnd : MemLp
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => B p.2) 2
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    hB.comp_measurePreserving measurePreserving_snd
  have hprod : Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) => A p.1 * B p.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    (memLp_one_iff_integrable.mp (hAfst.mul hBsnd)).congr
      (Filter.Eventually.of_forall fun p => Pi.mul_apply _ _ p)
  have hK : AEStronglyMeasurable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullTopKernel μG ρ hN β p.1 p.2)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    aestronglyMeasurable_pullTopKernel μG ρ hρcont hN β
  have hKb : ∀ p : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G),
      ‖pullTopKernel μG ρ hN β p.1 p.2‖
        ≤ Real.exp (|β| * layerBoundConst N) :=
    fun p => layerKernel_norm_le μG ρ β _ _
  refine (hprod.bdd_mul hK (Filter.Eventually.of_forall hKb)).congr
    (Filter.Eventually.of_forall fun p => ?_)
  show pullTopKernel μG ρ hN β p.1 p.2 * (A p.1 * B p.2)
      = A p.1 * (pullTopKernel μG ρ hN β p.1 p.2 * B p.2)
  ring

/-! ## The two dressed integrabilities at the factor class -/

/-- **R2d — hyp 6's plain dressed integrability
(`hInt`) at the factor class.** For every observable
`f` satisfying hyp 6's own prefix (a.e. strongly
measurable, pointwise bounded) and every layer factor
`φ'` in the factor class (`MemLp 2` on the layer pi
measure — the class item 5's expansion factors live
in), the plain dressed product integrand of item 6's
`gate4c_hyp6_of_named_inputs` is integrable on the
product pi space, in the exact shape that assembly
consumes. This is NOT the frozen ∀-form over bare
`φ'`: that form is not provable (scoping correction
2). -/
theorem integrable_dressed_marginal_of_memLp_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C)
    (hφ : MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)) :
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ((posGaugeAvg μG f) p.1 * φ' (tauBot hN p.1))
          * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) p.2
              * φ' (tauBot hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  obtain ⟨C, hC⟩ := hfb
  have hΦ : MemLp (fun z : ↥(posLinks (N := N)) → G =>
        φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_factor_pullback μG hN hφ
  have hA : MemLp (fun z => (posGaugeAvg μG f) z
        * φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_mul_of_aestronglyMeasurable_bounded μG
      (aestronglyMeasurable_posGaugeAvg μG f hf)
      (fun z => norm_posGaugeAvg_le μG C f hC z) hΦ
  have hB : MemLp
      (fun z => (starRingEnd ℂ) ((mirrorGaugeAvg μG f) z
        * φ' (tauBot hN z))) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    have hB0 : MemLp (fun z => (mirrorGaugeAvg μG f) z
          * φ' (tauBot hN z)) 2
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
      memLp_mul_of_aestronglyMeasurable_bounded μG
        (aestronglyMeasurable_mirrorGaugeAvg μG f hf)
        (fun z => norm_mirrorGaugeAvg_le μG C f hC z) hΦ
    refine (memLp_congr_ae
      (Filter.Eventually.of_forall fun z =>
        (starRingEnd_apply _).symm)).mp hB0.star
  refine (integrable_pullTopKernel_mul_of_memLp_slots μG ρ
    hρcont hN β hA hB).congr (Filter.Eventually.of_forall
      fun p => ?_)
  rfl

/-- **R3a — hyp 6's folded dressed integrability
(`hIntFold`) at the factor class.** The same statement
for the half-action-folded dressed integrand, in the
exact shape item 6's assembly consumes. The folded
weight is a.e. strongly measurable under `hρcont`
(`measurable_halfActionP_lf`, the stock item 6's P5
uses) and uniformly bounded
(`norm_exp_neg_halfActionP_le`), so each folded slot
function is `MemLp 2` by the same bounded-multiple
step. -/
theorem integrable_dressed_folded_of_memLp_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C)
    (hφ : MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)) :
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
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  obtain ⟨C, hC⟩ := hfb
  have hΦ : MemLp (fun z : ↥(posLinks (N := N)) → G =>
        φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_factor_pullback μG hN hφ
  have hW : Measurable (fun z : ↥(posLinks (N := N)) → G =>
      ((Real.exp (-(halfActionP ρ β z)) : ℂ))) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_halfActionP_lf ρ hρcont β).neg)
  have hW0 : (0 : ℝ)
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) :=
    Real.exp_nonneg _
  have hbP : ∀ z, ‖((Real.exp (-(halfActionP ρ β z)) : ℂ))
        * (posGaugeAvg μG f) z‖
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) * C :=
    fun z => (norm_mul_le _ _).trans (mul_le_mul
      (norm_exp_neg_halfActionP_le ρ β z)
      (norm_posGaugeAvg_le μG C f hC z) (norm_nonneg _) hW0)
  have hbM : ∀ z, ‖((Real.exp (-(halfActionP ρ β z)) : ℂ))
        * (mirrorGaugeAvg μG f) z‖
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) * C :=
    fun z => (norm_mul_le _ _).trans (mul_le_mul
      (norm_exp_neg_halfActionP_le ρ β z)
      (norm_mirrorGaugeAvg_le μG C f hC z) (norm_nonneg _) hW0)
  have hA : MemLp (fun z =>
        ((Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z) * φ' (tauBot hN z)) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    memLp_mul_of_aestronglyMeasurable_bounded μG
      (hW.aestronglyMeasurable.mul
        (aestronglyMeasurable_posGaugeAvg μG f hf)) hbP hΦ
  have hB : MemLp
      (fun z => (starRingEnd ℂ)
        (((Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (mirrorGaugeAvg μG f) z) * φ' (tauBot hN z))) 2
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
    have hB0 : MemLp (fun z =>
          ((Real.exp (-(halfActionP ρ β z)) : ℂ)
            * (mirrorGaugeAvg μG f) z) * φ' (tauBot hN z)) 2
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
      memLp_mul_of_aestronglyMeasurable_bounded μG
        (hW.aestronglyMeasurable.mul
          (aestronglyMeasurable_mirrorGaugeAvg μG f hf)) hbM hΦ
    refine (memLp_congr_ae
      (Filter.Eventually.of_forall fun z =>
        (starRingEnd_apply _).symm)).mp hB0.star
  refine (integrable_pullTopKernel_mul_of_memLp_slots μG ρ
    hρcont hN β hA hB).congr (Filter.Eventually.of_forall
      fun p => ?_)
  rfl

/-- **The pair of hyp-6 integrability inputs at the
factor class, packaged** in the order item 6's
assembly `gate4c_hyp6_of_named_inputs` consumes them
(third and fifth per-pair inputs). With this landing,
hypothesis 6's remaining unlanded per-pair inputs at
the factor class are exactly the two cross identities
and (outside the factor-class reading) the re-pinned
`hMarg` consumption — the folded invariance is
discharged by R2c. -/
theorem gate4c_hyp6_integrability_inputs_of_memLp_factor
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C)
    (hφ : MemLp φ' 2 (Measure.pi fun _ : LayerLink N => μG)) :
    Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        ((posGaugeAvg μG f) p.1 * φ' (tauBot hN p.1))
          * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) p.2
              * φ' (tauBot hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    ∧ Integrable
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
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
  ⟨integrable_dressed_marginal_of_memLp_factor μG ρ hρcont
      hN β f φ' hf hfb hφ,
    integrable_dressed_folded_of_memLp_factor μG ρ hρcont
      hN β f φ' hf hfb hφ⟩

/-! ## GATE-4C hypothesis 4 at the factor class -/

/-- **GATE-4C hypothesis 4 (`hIntStage`) for `MemLp 2`
factor data — a factor-class variant entry.** The
conclusion is hypothesis 4's verbatim ∀-shape (both
dressed stage integrands, in `pullTopKernel` form),
proved for expansion data whose every factor is
`MemLp 2` on the layer pi measure, under `hρcont`.
The frozen `hIntStage` quantifies over arbitrary
factor data and is NOT proved here: item 6's P6
discharged it in the regular case for data carrying
pointwise measurability and boundedness; this entry
discharges it for the disjoint regularity class the
compression route actually produces (`Lp` factors,
item 5), where pointwise boundedness fails in
general. The two entries together still do not cover
arbitrary data — that gap is the registered seam, and
closing it is not this brick's claim. -/
theorem hIntStage_of_memLp_factors
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (ι : ℕ → Type)
    (φ : ∀ n, ι n → (LayerLink N → G) → ℂ)
    (hφ : ∀ n i, MemLp (φ n i) 2
      (Measure.pi fun _ : LayerLink N => μG)) :
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
  intro f hf hfb n i
  refine ⟨?_, ?_⟩
  · refine (integrable_dressed_marginal_of_memLp_factor μG ρ
        hρcont hN β f (φ n i) hf hfb (hφ n i)).congr
      (Filter.Eventually.of_forall fun r => ?_)
    rfl
  · refine (integrable_dressed_folded_of_memLp_factor μG ρ
        hρcont hN β f (φ n i) hf hfb (hφ n i)).congr
      (Filter.Eventually.of_forall fun r => ?_)
    rfl

/-- **Hypothesis 4 for item 5's own factor data.** The
expansion produced by item 5's conditional headline
(`seatFactorApproxExpansion_of_layerKernelPosAll`) has
factors `⇑(gramFactor b (Fseq n) (vseq n) k)` — `Lp`
coeﬃcients, hence in the factor class — so hypothesis
4's stage integrabilities hold for that data verbatim,
under `hρcont`, by the variant entry above. (Feeding
this into GATE-4C's discharged conditional is R6's
wiring, not this brick's.) -/
theorem hIntStage_gramFactors
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (Fseq : ℕ → Finset ι) (mseq : ℕ → ℕ)
    (vseq : ∀ n, Fin (mseq n) → (↥(Fseq n) → ℂ)) :
    ∀ (f : (↥(posLinks (N := N)) → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      ∀ n k, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          ((posGaugeAvg μG f) r.1
              * (⇑(gramFactor b (Fseq n) (vseq n) k))
                (tauBot hN r.1))
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2
                * (⇑(gramFactor b (Fseq n) (vseq n) k))
                  (tauBot hN r.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      ∧ Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (((Real.exp (-(halfActionP ρ β r.1)) : ℂ)
              * (posGaugeAvg μG f) r.1)
              * (⇑(gramFactor b (Fseq n) (vseq n) k))
                (tauBot hN r.1))
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ)
                (((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
                    * (mirrorGaugeAvg μG f) r.2)
                  * (⇑(gramFactor b (Fseq n) (vseq n) k))
                    (tauBot hN r.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
  hIntStage_of_memLp_factors μG ρ hρcont hN β
    (fun n => Fin (mseq n))
    (fun n k => ⇑(gramFactor b (Fseq n) (vseq n) k))
    (fun _ _ => MeasureTheory.Lp.memLp _)

end Span3SeatSchurGateW3FactorInt

end ThetLogos
