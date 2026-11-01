/-
# F2-GATE-0: the F2-W3 gate interface pin (weld line)

Brick F2-GATE-0 of the F2 weld line, per the governing
scoping dossier `whitepaper/f2w3-gate-scoping-2026-11-01.md`
(esp. section 2 the discharge requirements, section 3 the
kills, section 4 the sub-line table and the pack-ready
statement list at its end) and pack
`routeb-general-scratch/pack-gate-0.md`.

**Target.** This module FREEZES the interface of the
F2-W3 gate — the discharge of the landed open Prop
`seatSchurProductStepOpen` (`ThetLogos.Span3SeatSchur`,
F2-W2, landed PARTIAL) — as Prop-valued definitions. It
discharges NOTHING: every definition below is a target
statement, asserted nowhere in this module, and no theorem
below proves any of them.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. **The fence, on the
face:** even a completed gate (GATE-0 through GATE-4) plus
F2-W3 proves neither FACT nor clause (a); it would prove
only a machine link between two open statements
(`LayerKernelPos` ⇒ clause (a)) at fixed `(β, N)`.
`LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity remain open
before and after. This is K-F2-4, registered below.

## The gate state, as frozen here

- W0/W1 FULL; W2 PARTIAL at `seatSchurProductStepOpen`.
- GATE-1 LANDED (BR1-028): the falsity probe proved
  impossibility for the faithful finite class — the
  UNDRESSED pairing's nonnegativity follows from
  `LayerKernelPos` alone, via per-copy gauge invariance of
  the fibre average of the twirled observable (the fibre
  average is invariant under the layer gauge action
  applied to each copy separately). K-GATE-1 did NOT
  fire; it is silent beyond the undressed pairing — it
  does not prove the concrete `SeatSchurTarget`.
- The DRESSED pairings (G2c, item 4 below:
  `fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback`)
  remain the LIVE FORK, untested by the probe.

## Kills armed on the face

- **K-F2-2** (invariance confinement): a certified
  negative dressed pairing, or G2c proved false, ⇒ the
  weld route dies at that seat; sequel only as a NEW
  entry under a strengthened hypothesis.
- **K-F2-3** (as registered in the weld line's memos:
  generality creep / vacuity — no abstract positive-kernel
  restatement, no finite-seat retreat, no landing under
  the weld headline at a narrower seat).
- **K-F2-4** (as registered: buy inflation — no sentence
  may describe gate or weld progress as progress on FACT,
  `𝒜 ⪰ 0`, clause (a), or uniformity).
- **K-GATE-2**: GATE-2's decision goes negative (the
  dressed fiber-average invariance, G2c, fails).
- **K-GATE-3**: the adapted HS-convergence lemma (the
  compression expansions of GATE-3 converging to
  `pullBotKernel` in HS norm) is false as needed.
- Also void on sight, per the dossier: any draft citing a
  spectral expansion for a compact operator on an
  infinite-dimensional space as if it were pinned-Mathlib
  stock (Blocker G-α), and any draft feeding an
  approximating sequence into the landed exact-finite
  conditional `seatSchurTarget_of_finiteRankProductStep`
  as if it were the exact finite expansion that theorem
  consumes — the limit form is item 6 below, a separate
  named Prop.

## Blockers, named

- **G-α (API):** no landed self-adjointness for
  `layerKernel` or its pullbacks, and no
  infinite-dimensional compact self-adjoint spectral
  theorem in the pinned Mathlib (finite-dimensional
  only). The dressed route must not silently assume one;
  the priced route is the compression engine, not the
  spectral engine.
- **G-β (the G2c fork):** the factor pairings the product
  step consumes are pairings of DRESSED observables;
  landed stage-2 positivity covers only pullbacks of
  gauge-invariant layer observables in iterated form.
  Their confinement to the class `LayerKernelPos`
  controls rests on item 4 below, unproved.

## The §2.2 audit point, on the face

The expansion frozen in item 1 is of FACTORS pulled back
from layer functions. A Gram expansion of `𝒜` itself is
FORBIDDEN and VOID: it would smuggle the conclusion (via
the landed Gram positivity it would prove
`LayerKernelPos` outright — the `𝒜 ⪰ 0` core, not a weld
brick). If a produced factor Gram ever satisfies the
`MemLp` hypotheses after section pullback, the landing
has proved a strictly stronger object than the weld
assumes and must be re-tiered and re-audited as a core
result, not shipped as a weld brick.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchur

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGate

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## The fiber averages (GATE-2 vocabulary, frozen here)

The fiber average of a strict-half observable `g` over the
complementary strict-half links: the layer coordinates
(the image of the landed embedding `embLayerTop` /
`embLayerBot`) are held at the layer datum `u`, the
complementary coordinates are integrated out against the
product probability measure. This is the conditional
expectation onto the layer coordinates, in splice form. -/

/-- **The top fiber average.** For a strict-half
observable `g` and a layer datum `u`, the average of `g`
over the strict-half configurations whose top extraction
is held at `u`: at links in the image of `embLayerTop`
the configuration reads `u` (transported along the
embedding), at all other strict-half links it is
integrated over. -/
noncomputable def fiberAvgTop (hN : Even N)
    (g : (↥(posLinks (N := N)) → G) → ℂ)
    (u : LayerLink N → G) : ℂ :=
  ∫ z : ↥(posLinks (N := N)) → G,
      g (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
        then u (Classical.choose h) else z m)
    ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)

/-- **The bottom fiber average.** The bottom analogue of
`fiberAvgTop`: the bottom extraction (the image of
`embLayerBot`) is held at `u`, the complementary
strict-half links are integrated out. -/
noncomputable def fiberAvgBot (hN : Even N)
    (g : (↥(posLinks (N := N)) → G) → ℂ)
    (u : LayerLink N → G) : ℂ :=
  ∫ z : ↥(posLinks (N := N)) → G,
      g (fun m => if h : ∃ ℓ, embLayerBot hN ℓ = m
        then u (Classical.choose h) else z m)
    ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)

/-! ## Item 1 (GATE-3 target): the approximating expansion -/

/-- **Item 1, `SeatFactorApproxExpansion` — the
approximating-expansion target for `pullBotKernel`
(GATE-3's object), frozen as a Prop; asserted nowhere.**
There is a sequence of finite Gram-shaped expansions:
finite types `ι n`, real coefficients `c n i ≥ 0`, layer
functions `φ n i`, and factors on strict-half
configurations `a n i = φ n i ∘ tauBot hN` — factors
PULLED BACK FROM LAYER FUNCTIONS, per the §2.2 audit
point on this module's face (a Gram expansion of `𝒜`
itself is forbidden and void) — such that the HS norm
(the `MemLp 2` norm `(eLpNorm · 2 (μ.prod μ)).toReal` on
the product probability space, the corpus's HS norm of
`IntegralKernelHS`) of the difference kernel
`pullBotKernel − Σ i, c i • (a i ⊗ conj (a i))` tends to
`0`, each difference kernel being `MemLp 2`. -/
def SeatFactorApproxExpansion (hN : Even N) (β : ℝ) : Prop :=
  ∃ (ι : ℕ → Type) (_ : ∀ n, Fintype (ι n))
    (c : ∀ n, ι n → ℝ)
    (φ : ∀ n, ι n → (LayerLink N → G) → ℂ),
    (∀ n i, 0 ≤ c n i) ∧
    (∀ n, MemLp
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ i, (c n i : ℂ)
              * ((φ n i) (tauBot hN p.1)
                * (starRingEnd ℂ) ((φ n i) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) ∧
    Filter.Tendsto
      (fun n => (eLpNorm
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          pullBotKernel μG ρ hN β p.1 p.2
            - ∑ i, (c n i : ℂ)
                * ((φ n i) (tauBot hN p.1)
                  * (starRingEnd ℂ) ((φ n i) (tauBot hN p.2))))
        2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal)
      Filter.atTop (nhds 0)

/-! ## Item 2 (G2a): product ↔ iterated identification -/

/-- **Item 2, top (G2a), frozen as a Prop; asserted
nowhere.** For every layer observable `F` bounded and
measurable at the seat, the product-integral `seatPairing`
of `pullTopKernel` on the pulled-back observables equals
its iterated form, the landed `pullTopPairingIter`. -/
def seatPairing_pullTop_eq_pullTopPairingIter (hN : Even N)
    (β : ℝ) : Prop :=
  ∀ F : (LayerLink N → G) → ℂ,
    AEStronglyMeasurable F
      (Measure.pi fun _ : LayerLink N => μG) →
    (∃ C : ℝ, ∀ u, ‖F u‖ ≤ C) →
    seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => F (tauTop hN z)) (fun z => F (tauTop hN z))
      = pullTopPairingIter μG ρ hN β F

/-- **Item 2, bottom (G2a), frozen as a Prop; asserted
nowhere.** The bottom analogue: the product-integral
`seatPairing` of `pullBotKernel` on the pulled-back
observables equals the landed `pullBotPairingIter`. -/
def seatPairing_pullBot_eq_pullBotPairingIter (hN : Even N)
    (β : ℝ) : Prop :=
  ∀ F : (LayerLink N → G) → ℂ,
    AEStronglyMeasurable F
      (Measure.pi fun _ : LayerLink N => μG) →
    (∃ C : ℝ, ∀ u, ‖F u‖ ≤ C) →
    seatPairing μG (pullBotKernel μG ρ hN β)
        (fun z => F (tauBot hN z)) (fun z => F (tauBot hN z))
      = pullBotPairingIter μG ρ hN β F

/-! ## Item 3 (G2b): the fiber-average identities -/

/-- **Item 3, top (G2b), frozen as a Prop; asserted
nowhere.** For every bounded measurable strict-half
observable `g`, the `pullTopKernel` seat pairing of `g`
with itself is the `layerPairing` of its top fiber
average `fiberAvgTop g`. -/
def seatPairing_pullTop_eq_layerPairing_fiberAvg
    (hN : Even N) (β : ℝ) : Prop :=
  ∀ g : (↥(posLinks (N := N)) → G) → ℂ,
    AEStronglyMeasurable g
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
    (∃ C : ℝ, ∀ z, ‖g z‖ ≤ C) →
    seatPairing μG (pullTopKernel μG ρ hN β) g g
      = layerPairing μG ρ β (fiberAvgTop μG hN g)

/-- **Item 3, bottom (G2b), frozen as a Prop; asserted
nowhere.** The bottom analogue: the `pullBotKernel` seat
pairing of `g` with itself is the `layerPairing` of its
bottom fiber average `fiberAvgBot g`. -/
def seatPairing_pullBot_eq_layerPairing_fiberAvg
    (hN : Even N) (β : ℝ) : Prop :=
  ∀ g : (↥(posLinks (N := N)) → G) → ℂ,
    AEStronglyMeasurable g
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
    (∃ C : ℝ, ∀ z, ‖g z‖ ≤ C) →
    seatPairing μG (pullBotKernel μG ρ hN β) g g
      = layerPairing μG ρ β (fiberAvgBot μG hN g)

/-! ## Item 4 (G2c): the decision lemma — the live fork -/

/-- **Item 4, the G2c decision lemma, frozen as a Prop;
asserted nowhere. THE LIVE FORK (Blocker G-β; its
failure is K-F2-2 firing / K-GATE-2).** For every bounded
measurable strict-half observable `f` and every layer
function `φ`, the top fiber average of the twirled
observable dressed by the pulled-back factor,
`(posGaugeAvg f) · (φ ∘ tauBot)`, is a
`GaugeInvariantLayerObs` — and likewise for the
mirror/twirled variant, `(mirrorGaugeAvg f) ·
(φ ∘ tauBot)`. Only under this lemma do the dressed
factor pairings of the product step fall inside the
class `LayerKernelPos` controls. -/
def fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback
    (hN : Even N) : Prop :=
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

/-! ## Item 5 (GATE-3 headline) -/

/-- **Item 5, the GATE-3 headline, frozen as a ∀-Prop;
asserted nowhere.** At every `Even N`, every `β ≥ 0`,
under the assumed `LayerKernelPos`, the bottom pullback
kernel admits the approximating expansion of item 1. -/
def pullBotKernel_seatFactorApproxExpansion : Prop :=
  ∀ (hN : Even N) (β : ℝ), 0 ≤ β →
    LayerKernelPos (N := N) μG ρ β →
    SeatFactorApproxExpansion μG ρ hN β

/-! ## Item 6 (GATE-4): the limit-form conditional -/

/-- **Item 6, the limit-form conditional, frozen as a
Prop; asserted nowhere.** This is the limit analogue of
the landed exact-finite conditional
`seatSchurTarget_of_finiteRankProductStep`, which must
NOT be fed an approximating sequence (exact-finite
smuggling, void on sight): IF `pullBotKernel` admits
the approximating expansion of item 1, AND GATE-2's
factor pairing nonnegativity holds — for every bounded
measurable `f` and layer factor `φ`, the dressed factor
pairings of `pullTopKernel` are nonnegative in their
real part, in both the twirled (marginal) form and the
half-action-folded form — THEN `SeatSchurTarget` holds
in its exact registered form. -/
def seatSchurTarget_of_approxProductStep : Prop :=
  ∀ (hN : Even N) (β : ℝ),
    SeatFactorApproxExpansion μG ρ hN β →
    (∀ (f : (↥(posLinks (N := N)) → G) → ℂ)
      (φ : (LayerLink N → G) → ℂ),
      AEStronglyMeasurable f
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
      (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
      0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (posGaugeAvg μG f) z * φ (tauBot hN z))
        (fun z => (mirrorGaugeAvg μG f) z
          * φ (tauBot hN z))).re
      ∧ 0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (posGaugeAvg μG f) z * φ (tauBot hN z))
        (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (mirrorGaugeAvg μG f) z
          * φ (tauBot hN z))).re) →
    SeatSchurTarget μG ρ hN β

/-! ## Item 7 (GATE-4 headline): the discharge target -/

/-- **Item 7, the GATE-4 headline, frozen as a Prop;
asserted nowhere.** Its type is EXACTLY the landed open
Prop `seatSchurProductStepOpen` (F2-W2's registered
remainder), universally over `Even N` and `β` — hence,
by that Prop's definition, `SeatSchurTarget μG ρ hN β`
in the pin's registered form. Discharging this Prop is
the whole gate; even then, per the fence on this
module's face, neither FACT nor clause (a) is proved. -/
def seatSchurProductStepOpen_discharge : Prop :=
  ∀ (hN : Even N) (β : ℝ),
    seatSchurProductStepOpen μG ρ hN β

end Span3SeatSchurGate

end ThetLogos
