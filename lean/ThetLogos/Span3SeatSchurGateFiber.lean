/-
# F2-GATE-2: fiber-average reduction + the G2c confinement decision

Brick F2-GATE-2 of the F2 weld line, per the governing
scoping dossier `whitepaper/f2w3-gate-scoping-2026-11-01.md`
(GATE-2 entry) and pack
`routeb-general-scratch/pack-gate-2.md`. Target: the
GATE-2 Props frozen in `ThetLogos.Span3SeatSchurGatePost`
(GATE-0): G2a (product↔iterated identification), G2b (the
fiber-average identities for the LANDED `fiberAvgTop` /
`fiberAvgBot`), G2c (the decision lemma
`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback`).

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. **The fence, on the
face:** even a FULL gate + W3 proves neither FACT nor
clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity
remain open before and after.

## Verdict of this brick: PARTIAL, with the G2c fork DECIDED NEGATIVE

- **G2c — DECIDED, FALSE. K-F2-2 / K-GATE-2 FIRES.**
  The pin's Prop
  `fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback`
  is **disproved in-tree** (`g2c_counterexample` below):
  at `N = 2` the top and bottom layer embeddings
  **coincide** (`embLayerTop_eq_embLayerBot_at_two`: the
  top extraction site time is `N / 2 - 1 = 0`, the bottom
  extraction's time), so the bottom extraction of a top
  splice is the layer datum itself
  (`tauBot_spliceTop_at_two`), and the top fiber average
  of the dressed constant observable is the dressing
  layer function itself, verbatim
  (`fiberAvgTop_const_one_mul_pullback_at_two`):
  `fiberAvgTop μG hN (fun z => (posGaugeAvg μG 1) z *
  φ (tauBot hN z)) = φ` at `N = 2`, for **every** layer
  function `φ` — the pin carries no hypothesis on `φ`.
  At the concrete seat `G₀ = Multiplicative (ZMod 2)`,
  `μG₀` (the corpus's uniform probability measure,
  `LatticeBlockingFlow`), `f ≡ 1`, and
  `φ w = if w ℓ₀ = 1 then 0 else 1` at the layer link
  `ℓ₀ = (0-site, direction 1)`, the fiber average is
  `φ`, which is **not** gauge invariant: the gauge
  function `γ₀` (the seat group's nonidentity element
  `flowSeatS` at the zero site, `1` elsewhere) moves it
  (`φ (γ₀ • u₀) = 1 ≠ 0 = φ u₀` at `u₀ ≡ 1`). Hence the
  dressed pairings do **not** confine to the
  gauge-invariant class at this seat: **the weld route
  dies at the `N = 2` seat**, reported at full rank.
  The mechanism is exactly the dossier's named
  disjointness premise failing: the two extractions'
  coordinate sets are disjoint only for `N ≥ 4`; the
  pin quantifies over all `Even N`, including `2`.
  Any sequel (e.g. a re-pin at `4 ≤ N`, or with the
  dressing restricted) is a NEW entry and a parent
  decision; nothing here re-pins anything.

- **G2a / G2b — NOT discharged as pinned; the exact
  obstruction is isolated and the identities are proved
  in conditional form.** The pin's Props assume only
  `AEStronglyMeasurable` + boundedness of the
  observable. The Fubini step (`integral_prod` /
  `integral_integral_swap`) needs **integrability of
  the pairing integrand on the product pi space**
  (`hInt` below), whose AEStronglyMeasurability rests
  on joint measurability of `layerKernel μG ρ β` in its
  two layer arguments. No such measurability is landed
  at the pin's generality: every corpus measurability
  lemma for the plaquette densities feeding
  `layerKernel` (`measurable_plaquetteDensity`,
  `measurable_plaquetteDensity_lf`,
  `measurable_planeAvgKernel`) carries the extra
  hypothesis `Continuous fun g => repMatrix ρ g`,
  which the pin does **not** carry and which does not
  follow from the ambient instances (a bare monoid hom
  into the unitary group need not be measurable).
  G2b needs in addition the **fiber marginalization**
  (`hMarg` below): the disintegration of the pi measure
  along the landed splice — the conditional-expectation
  property of `fiberAvgTop` / `fiberAvgBot` — which is
  landed nowhere in the corpus. What IS proved here,
  at full strength from those two named inputs alone:
  the G2a identities
  (`seatPairing_pullTop_eq_pullTopPairingIter_of_integrable`,
  `..._pullBot_...`), via product↔iterated Fubini plus
  the landed per-stratum symmetry `layerKernel_symm`;
  and the G2b identities
  (`seatPairing_pullTop_eq_layerPairing_fiberAvg_of_integrable_marg`,
  `..._pullBot_...`), via the G2a reduction, two
  applications of `hMarg`, and the unconditional
  conjugation compatibility of the fiber averages
  (`fiberAvgTop_conj` / `fiberAvgBot_conj`, proved).
  So the pin's G2a/G2b remainders are exactly `hInt`
  and `hMarg` — no more, no less. This is a finding
  about the pin (its hypotheses are two inputs short),
  **not** a disproof of the G2a/G2b identities and not
  a kill: in the regular case (e.g. under
  `Continuous fun g => repMatrix ρ g`) both inputs are
  expected to hold. `fiberAvgTop` has NOT been
  redefined.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGatePost
import ThetLogos.LatticeBlockingFlow
import Mathlib.Tactic

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateFiber

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## G2a, engine: product ↔ iterated under `hInt` -/

/-- **G2a engine, top.** Under the product-integrability
hypothesis `hInt` (the named obstruction input), the
`pullTopKernel` seat pairing of `k` with itself is its
iterated form: Fubini (`integral_prod`), the iterated
swap, and the landed per-stratum symmetry
`layerKernel_symm` to move the conjugation onto the
first slot. -/
theorem seatPairing_pullTop_eq_iter_of_integrable (hN : Even N) (β : ℝ)
    (k : (↥(posLinks (N := N)) → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        k p.1 * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (k p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :
    seatPairing μG (pullTopKernel μG ρ hN β) k k
      = ∫ z, ∫ z', (starRingEnd ℂ) (k z)
          * layerKernel μG ρ β (tauTop hN z) (tauTop hN z') * k z'
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  have hswap : ∀ z z' : ↥(posLinks (N := N)) → G,
      k z * (layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
          * (starRingEnd ℂ) (k z'))
        = (starRingEnd ℂ) (k z') * layerKernel μG ρ β (tauTop hN z')
            (tauTop hN z) * k z := by
    intro z z'
    rw [layerKernel_symm μG ρ hN β (tauTop hN z') (tauTop hN z)]
    ring
  unfold seatPairing pullTopKernel
  refine (integral_prod _ hInt).trans ?_
  refine (integral_integral_swap hInt).trans ?_
  exact integral_congr_ae (ae_of_all _ fun z' =>
    integral_congr_ae (ae_of_all _ fun z => hswap z z'))

/-- **G2a engine, bottom.** Under `hInt`, the
`pullBotKernel` seat pairing of `k` with itself is its
iterated form (the primed variable outermost, absorbing
the bottom slot swap, as in the landed
`pullBotPairingIter`): Fubini and the iterated swap
only — no kernel symmetry is needed. -/
theorem seatPairing_pullBot_eq_iter_of_integrable (hN : Even N) (β : ℝ)
    (k : (↥(posLinks (N := N)) → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        k p.1 * (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
          * (starRingEnd ℂ) (k p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :
    seatPairing μG (pullBotKernel μG ρ hN β) k k
      = ∫ z', ∫ z, k z
          * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
          * (starRingEnd ℂ) (k z')
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  unfold seatPairing pullBotKernel
  refine (integral_prod _ hInt).trans ?_
  refine (integral_integral_swap hInt).trans ?_
  refine integral_congr_ae (ae_of_all _ fun z' =>
    integral_congr_ae (ae_of_all _ fun z => ?_))
  ring

/-! ## G2a, conditional form: the pin's conclusions under `hInt` -/

/-- **G2a top, conditional.** The conclusion of the
pin's `seatPairing_pullTop_eq_pullTopPairingIter`,
proved under the additional named hypothesis `hInt`
(product integrability of the pairing integrand). The
pin as frozen — whose hypotheses are only
`AEStronglyMeasurable` + boundedness of `F` — is NOT
discharged: `hInt` does not follow from those from
landed material (see the face). -/
theorem seatPairing_pullTop_eq_pullTopPairingIter_of_integrable
    (hN : Even N) (β : ℝ) (F : (LayerLink N → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        F (tauTop hN p.1) * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (F (tauTop hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :
    seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => F (tauTop hN z)) (fun z => F (tauTop hN z))
      = pullTopPairingIter μG ρ hN β F :=
  seatPairing_pullTop_eq_iter_of_integrable μG ρ hN β
    (fun z => F (tauTop hN z)) hInt

/-- **G2a bottom, conditional.** The conclusion of the
pin's `seatPairing_pullBot_eq_pullBotPairingIter`,
under the additional named hypothesis `hInt`. -/
theorem seatPairing_pullBot_eq_pullBotPairingIter_of_integrable
    (hN : Even N) (β : ℝ) (F : (LayerLink N → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        F (tauBot hN p.1) * (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
          * (starRingEnd ℂ) (F (tauBot hN p.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :
    seatPairing μG (pullBotKernel μG ρ hN β)
        (fun z => F (tauBot hN z)) (fun z => F (tauBot hN z))
      = pullBotPairingIter μG ρ hN β F :=
  seatPairing_pullBot_eq_iter_of_integrable μG ρ hN β
    (fun z => F (tauBot hN z)) hInt

/-! ## The fiber averages commute with conjugation (unconditional) -/

/-- **Conjugation passes through the top fiber
average**, for the LANDED `fiberAvgTop`, with no side
hypothesis: `integral_conj` under the splice. -/
theorem fiberAvgTop_conj (hN : Even N)
    (g : (↥(posLinks (N := N)) → G) → ℂ) :
    fiberAvgTop μG hN (fun z => (starRingEnd ℂ) (g z))
      = fun u => (starRingEnd ℂ) (fiberAvgTop μG hN g u) := by
  funext u
  show (∫ z : ↥(posLinks (N := N)) → G, (starRingEnd ℂ)
      (g (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
        then u (Classical.choose h) else z m))
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = (starRingEnd ℂ) (∫ z : ↥(posLinks (N := N)) → G,
      g (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
        then u (Classical.choose h) else z m)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
  exact (integral_conj (𝕜 := ℂ)
    (μ := Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
    (f := fun z : ↥(posLinks (N := N)) → G =>
      g (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
        then u (Classical.choose h) else z m)))

/-- **Conjugation passes through the bottom fiber
average**, for the LANDED `fiberAvgBot`. -/
theorem fiberAvgBot_conj (hN : Even N)
    (g : (↥(posLinks (N := N)) → G) → ℂ) :
    fiberAvgBot μG hN (fun z => (starRingEnd ℂ) (g z))
      = fun u => (starRingEnd ℂ) (fiberAvgBot μG hN g u) := by
  funext u
  show (∫ z : ↥(posLinks (N := N)) → G, (starRingEnd ℂ)
      (g (fun m => if h : ∃ ℓ, embLayerBot hN ℓ = m
        then u (Classical.choose h) else z m))
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = (starRingEnd ℂ) (∫ z : ↥(posLinks (N := N)) → G,
      g (fun m => if h : ∃ ℓ, embLayerBot hN ℓ = m
        then u (Classical.choose h) else z m)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
  exact (integral_conj (𝕜 := ℂ)
    (μ := Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
    (f := fun z : ↥(posLinks (N := N)) → G =>
      g (fun m => if h : ∃ ℓ, embLayerBot hN ℓ = m
        then u (Classical.choose h) else z m)))

/-! ## G2b, conditional form: the pin's conclusions under `hInt` + `hMarg` -/

/-- **G2b top, conditional.** The conclusion of the
pin's `seatPairing_pullTop_eq_layerPairing_fiberAvg`,
for the LANDED `fiberAvgTop`, proved under the two
additional named hypotheses: `hInt` (product
integrability, the G2a input) and `hMarg` (the fiber
marginalization / disintegration identity for the
landed splice — the conditional-expectation property
of `fiberAvgTop`). The pin as frozen is NOT
discharged: neither input follows from the pin's
hypotheses from landed material (see the face). -/
theorem seatPairing_pullTop_eq_layerPairing_fiberAvg_of_integrable_marg
    (hN : Even N) (β : ℝ) (g : (↥(posLinks (N := N)) → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        g p.1 * (layerKernel μG ρ β (tauTop hN p.1) (tauTop hN p.2)
          * (starRingEnd ℂ) (g p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hMarg : ∀ (a : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgTop μG hN a u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG)) :
    seatPairing μG (pullTopKernel μG ρ hN β) g g
      = layerPairing μG ρ β (fiberAvgTop μG hN g) := by
  rw [seatPairing_pullTop_eq_iter_of_integrable μG ρ hN β g hInt]
  have hinner : ∀ z : ↥(posLinks (N := N)) → G,
      (∫ z', (starRingEnd ℂ) (g z)
          * layerKernel μG ρ β (tauTop hN z) (tauTop hN z') * g z'
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = (starRingEnd ℂ) (g z) * ∫ u',
          layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN g u'
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    intro z
    calc (∫ z', (starRingEnd ℂ) (g z)
            * layerKernel μG ρ β (tauTop hN z) (tauTop hN z') * g z'
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = (starRingEnd ℂ) (g z) * ∫ z',
            g z' * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun z' => by ring)
      _ = (starRingEnd ℂ) (g z) * ∫ u', fiberAvgTop μG hN g u'
            * layerKernel μG ρ β (tauTop hN z) u'
          ∂(Measure.pi fun _ : LayerLink N => μG) :=
          congrArg _ (hMarg g (fun u' => layerKernel μG ρ β (tauTop hN z) u'))
      _ = (starRingEnd ℂ) (g z) * ∫ u',
            layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN g u'
          ∂(Measure.pi fun _ : LayerLink N => μG) :=
          congrArg _ (integral_congr_ae (ae_of_all _ fun u' => mul_comm _ _))
  rw [integral_congr_ae (ae_of_all _ hinner)]
  have houter : (∫ z, (starRingEnd ℂ) (g z) * ∫ u',
        layerKernel μG ρ β (tauTop hN z) u' * fiberAvgTop μG hN g u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = ∫ u, (starRingEnd ℂ) (fiberAvgTop μG hN g u) * ∫ u',
        layerKernel μG ρ β u u' * fiberAvgTop μG hN g u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG) := by
    have hm := hMarg (fun z => (starRingEnd ℂ) (g z))
      (fun u => ∫ u', layerKernel μG ρ β u u' * fiberAvgTop μG hN g u'
        ∂(Measure.pi fun _ : LayerLink N => μG))
    rw [fiberAvgTop_conj μG hN g] at hm
    exact hm
  rw [houter]
  unfold layerPairing
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show (starRingEnd ℂ) (fiberAvgTop μG hN g u) * ∫ u',
        layerKernel μG ρ β u u' * fiberAvgTop μG hN g u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
    = ∫ u', (starRingEnd ℂ) (fiberAvgTop μG hN g u)
        * layerKernel μG ρ β u u' * fiberAvgTop μG hN g u'
      ∂(Measure.pi fun _ : LayerLink N => μG)
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun u' => by ring)

/-- **G2b bottom, conditional.** The conclusion of the
pin's `seatPairing_pullBot_eq_layerPairing_fiberAvg`,
for the LANDED `fiberAvgBot`, under `hInt` + `hMarg`
(bottom forms). -/
theorem seatPairing_pullBot_eq_layerPairing_fiberAvg_of_integrable_marg
    (hN : Even N) (β : ℝ) (g : (↥(posLinks (N := N)) → G) → ℂ)
    (hInt : Integrable
      (fun p : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G) =>
        g p.1 * (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
          * (starRingEnd ℂ) (g p.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hMarg : ∀ (a : (↥(posLinks (N := N)) → G) → ℂ)
      (Ψ : (LayerLink N → G) → ℂ),
      (∫ z, a z * Ψ (tauBot hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u, fiberAvgBot μG hN a u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG)) :
    seatPairing μG (pullBotKernel μG ρ hN β) g g
      = layerPairing μG ρ β (fiberAvgBot μG hN g) := by
  rw [seatPairing_pullBot_eq_iter_of_integrable μG ρ hN β g hInt]
  have hinner : ∀ z' : ↥(posLinks (N := N)) → G,
      (∫ z, g z * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
          * (starRingEnd ℂ) (g z')
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = (∫ u, layerKernel μG ρ β (tauBot hN z') u * fiberAvgBot μG hN g u
          ∂(Measure.pi fun _ : LayerLink N => μG))
        * (starRingEnd ℂ) (g z') := by
    intro z'
    calc (∫ z, g z * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
            * (starRingEnd ℂ) (g z')
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = (∫ z, g z * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
          * (starRingEnd ℂ) (g z') := by
          rw [← integral_mul_const]
      _ = (∫ u, fiberAvgBot μG hN g u
            * layerKernel μG ρ β (tauBot hN z') u
          ∂(Measure.pi fun _ : LayerLink N => μG))
          * (starRingEnd ℂ) (g z') :=
          congrArg (· * (starRingEnd ℂ) (g z'))
            (hMarg g (fun u => layerKernel μG ρ β (tauBot hN z') u))
      _ = (∫ u, layerKernel μG ρ β (tauBot hN z') u * fiberAvgBot μG hN g u
          ∂(Measure.pi fun _ : LayerLink N => μG))
          * (starRingEnd ℂ) (g z') :=
          congrArg (· * (starRingEnd ℂ) (g z'))
            (integral_congr_ae (ae_of_all _ fun u =>
              mul_comm (fiberAvgBot μG hN g u)
                (layerKernel μG ρ β (tauBot hN z') u)))
  rw [integral_congr_ae (ae_of_all _ hinner)]
  have houter : (∫ z', (∫ u, layerKernel μG ρ β (tauBot hN z') u
        * fiberAvgBot μG hN g u
      ∂(Measure.pi fun _ : LayerLink N => μG)) * (starRingEnd ℂ) (g z')
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = ∫ u', (starRingEnd ℂ) (fiberAvgBot μG hN g u') * ∫ u,
        layerKernel μG ρ β u' u * fiberAvgBot μG hN g u
      ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG) := by
    have hpre : (∫ z', (∫ u, layerKernel μG ρ β (tauBot hN z') u
          * fiberAvgBot μG hN g u
        ∂(Measure.pi fun _ : LayerLink N => μG)) * (starRingEnd ℂ) (g z')
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ z', (starRingEnd ℂ) (g z') * ∫ u,
          layerKernel μG ρ β (tauBot hN z') u * fiberAvgBot μG hN g u
        ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
      integral_congr_ae (ae_of_all _ fun z' => mul_comm _ _)
    rw [hpre]
    have hm := hMarg (fun z => (starRingEnd ℂ) (g z))
      (fun u' => ∫ u, layerKernel μG ρ β u' u * fiberAvgBot μG hN g u
        ∂(Measure.pi fun _ : LayerLink N => μG))
    rw [fiberAvgBot_conj μG hN g] at hm
    exact hm
  rw [houter]
  unfold layerPairing
  refine integral_congr_ae (ae_of_all _ fun u' => ?_)
  show (starRingEnd ℂ) (fiberAvgBot μG hN g u') * ∫ u,
        layerKernel μG ρ β u' u * fiberAvgBot μG hN g u
      ∂(Measure.pi fun _ : LayerLink N => μG)
    = ∫ u, (starRingEnd ℂ) (fiberAvgBot μG hN g u')
        * layerKernel μG ρ β u' u * fiberAvgBot μG hN g u
      ∂(Measure.pi fun _ : LayerLink N => μG)
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun u => by ring)

end Span3SeatSchurGateFiber

/-! ## G2c: the `N = 2` collision and the disproof -/

section Span3SeatSchurGateFiberTwo

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **At `N = 2` the top and bottom layer embeddings
coincide**: the top extraction site time is
`N / 2 - 1 = 0`, the bottom extraction's own time, so
`embLayerTop hN ℓ = embLayerBot hN ℓ` as strict-half
links. This is the collision that kills G2c: the
dossier's disjointness premise for the two
extractions' coordinate sets holds only for
`N ≥ 4`. -/
theorem embLayerTop_eq_embLayerBot_at_two (hN : Even N) (hN2 : N = 2)
    (ℓ : LayerLink N) : embLayerTop hN ℓ = embLayerBot hN ℓ := by
  subst hN2
  apply Subtype.ext
  show (topSite ⟨ℓ.1.1, ℓ.2.1⟩, ℓ.1.2) = ℓ.1
  have hsite : topSite ⟨ℓ.1.1, ℓ.2.1⟩ = ℓ.1.1 := by
    funext j
    show Function.update ℓ.1.1 0 ((2 / 2 - 1 : ℕ) : ZMod 2) j = ℓ.1.1 j
    by_cases hj : j = 0
    · subst hj
      rw [Function.update_self]
      have h0 : ℓ.1.1 0 = 0 := by
        rw [← ZMod.natCast_zmod_val (ℓ.1.1 0), ℓ.2.1, Nat.cast_zero]
      rw [h0]
      rfl
    · exact Function.update_of_ne hj _ _
  rw [hsite]

/-- **At `N = 2`, the bottom extraction of a top splice
is the layer datum itself**: splicing `u` into the top
coordinates writes it onto exactly the links the
bottom extraction reads (the two embeddings coincide),
so `tauBot` of the splice is `u`, independently of the
complementary configuration. -/
theorem tauBot_spliceTop_at_two (hN : Even N) (hN2 : N = 2)
    (u : LayerLink N → G) (z : ↥(posLinks (N := N)) → G) :
    tauBot hN (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
        then u (Classical.choose h) else z m) = u := by
  funext ℓ
  show (if h : ∃ ℓ', embLayerTop hN ℓ' = embLayerBot hN ℓ
      then u (Classical.choose h) else z (embLayerBot hN ℓ)) = u ℓ
  have hex : ∃ ℓ', embLayerTop hN ℓ' = embLayerBot hN ℓ :=
    ⟨ℓ, embLayerTop_eq_embLayerBot_at_two hN hN2 ℓ⟩
  rw [dite_eq_left hex]
  congr 1
  apply embLayerTop_injective hN
  rw [Classical.choose_spec hex]
  exact (embLayerTop_eq_embLayerBot_at_two hN hN2 ℓ).symm

/-- The constant observable's positive gauge average is
the constant `1` (the gauge pi measure is a
probability measure). -/
theorem posGaugeAvg_one :
    posGaugeAvg μG (fun _ : ↥(posLinks (N := N)) → G => (1 : ℂ))
      = fun _ => 1 := by
  funext z
  simp [posGaugeAvg]

/-- **At `N = 2`, the top fiber average of the twirled
constant observable dressed by a pulled-back layer
factor is the dressing factor itself, verbatim**:
`fiberAvgTop μG hN (fun z => (posGaugeAvg μG 1) z *
φ (tauBot hN z)) = φ` for EVERY layer function `φ`
(the pin carries no hypothesis on `φ`). The fiber
average does not average the dressing at all at this
seat — the dressed observable's fiber average is
exactly as gauge-variant as `φ` is. -/
theorem fiberAvgTop_const_one_mul_pullback_at_two (hN : Even N) (hN2 : N = 2)
    (φ : (LayerLink N → G) → ℂ) (u : LayerLink N → G) :
    fiberAvgTop μG hN
        (fun z => (posGaugeAvg μG
          (fun _ : ↥(posLinks (N := N)) → G => (1 : ℂ))) z
            * φ (tauBot hN z)) u
      = φ u := by
  have hpt : ∀ z : ↥(posLinks (N := N)) → G,
      (fun z => (posGaugeAvg μG
          (fun _ : ↥(posLinks (N := N)) → G => (1 : ℂ))) z
            * φ (tauBot hN z))
        (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
          then u (Classical.choose h) else z m) = φ u := by
    intro z
    show (posGaugeAvg μG (fun _ : ↥(posLinks (N := N)) → G => (1 : ℂ)))
        (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
          then u (Classical.choose h) else z m)
      * φ (tauBot hN (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
          then u (Classical.choose h) else z m)) = φ u
    rw [posGaugeAvg_one μG, tauBot_spliceTop_at_two hN hN2 u z]
    simp
  unfold fiberAvgTop
  rw [integral_congr_ae (ae_of_all _ hpt)]
  simp

end Span3SeatSchurGateFiberTwo

/-- **G2c DECIDED NEGATIVE — K-F2-2 / K-GATE-2 FIRES.**
The pin's Prop
`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback`
is **false** at the seat `N = 2`,
`G₀ = Multiplicative (ZMod 2)` with the uniform
probability measure `μG₀` (disproof in the tree's own
vocabulary; the Prop does not depend on `ρ`, so no
representation choice is involved). Witnesses:
`f ≡ 1` (so `posGaugeAvg μG₀ f ≡ 1` and
`mirrorGaugeAvg μG₀ f ≡ 1`), and the layer function
`φ w = if w ℓ₀ = 1 then 0 else 1` at the layer link
`ℓ₀ = ⟨(0-site, direction 1), _⟩`. By
`fiberAvgTop_const_one_mul_pullback_at_two`, the top
fiber average of the dressed observable
`(posGaugeAvg μG₀ f) · (φ ∘ tauBot)` is `φ` itself;
but `φ` is not a `GaugeInvariantLayerObs`: at
`u₀ ≡ 1` and the gauge function `γ₀` (the nonidentity
seat element `flowSeatS` at the zero site, `1`
elsewhere), `(γ₀ • u₀) ℓ₀ = flowSeatS ≠ 1 = u₀ ℓ₀`,
so `φ (γ₀ • u₀) = 1 ≠ 0 = φ u₀`. The first conjunct of
the pin's conclusion already fails. **The weld route
dies at this seat**; the dressed factor pairings do
not confine to `LayerKernelPos`'s class at `N = 2`. -/
theorem g2c_counterexample (hN : Even (2 : ℕ)) :
    ¬ fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback
      (G := Multiplicative (ZMod 2)) (N := 2) μG₀ hN := by
  intro h
  let ℓ₀ : LayerLink 2 := ⟨(fun _ => 0, 1), by decide, by decide⟩
  let γ₀ : (Fin 4 → ZMod 2) → Multiplicative (ZMod 2) :=
    fun x => if x = (fun _ => 0) then flowSeatS else 1
  let u₀ : LayerLink 2 → Multiplicative (ZMod 2) := fun _ => 1
  have hγ : layerGaugeAction γ₀ u₀ ℓ₀ = flowSeatS := by
    show γ₀ (ℓ₀.1.1) * u₀ ℓ₀ * (γ₀ (torusShift 2 ℓ₀.1.2 ℓ₀.1.1))⁻¹
      = flowSeatS
    have hshift : torusShift 2 (1 : Fin 4) (fun _ => (0 : ZMod 2))
        ≠ (fun _ => 0) := by
      intro hcon
      have h1 := congrFun hcon (1 : Fin 4)
      rw [torusShift_apply_coord] at h1
      simp at h1
    have e1 : γ₀ (ℓ₀.1.1) = flowSeatS := ite_eq_left rfl
    have e2 : γ₀ (torusShift 2 ℓ₀.1.2 ℓ₀.1.1) = 1 := ite_eq_right hshift
    have e3 : u₀ ℓ₀ = 1 := rfl
    rw [e1, e2, e3]
    simp
  obtain ⟨hInv, -⟩ := h
    (fun _ : ↥(posLinks (N := 2)) → Multiplicative (ZMod 2) => (1 : ℂ))
    (fun w => if w ℓ₀ = 1 then (0 : ℂ) else 1)
    measurable_const.aestronglyMeasurable
    ⟨1, fun z => by simp⟩
  have hEq := hInv γ₀ u₀
  rw [fiberAvgTop_const_one_mul_pullback_at_two μG₀ hN rfl
      (fun w => if w ℓ₀ = 1 then (0 : ℂ) else 1) u₀,
    fiberAvgTop_const_one_mul_pullback_at_two μG₀ hN rfl
      (fun w => if w ℓ₀ = 1 then (0 : ℂ) else 1)
      (layerGaugeAction γ₀ u₀)] at hEq
  have hφγ : (if layerGaugeAction γ₀ u₀ ℓ₀ = 1 then (0 : ℂ) else 1) = 1 :=
    ite_eq_right (by rw [hγ]; exact flowSeatS_ne_one)
  have hφu : (if u₀ ℓ₀ = 1 then (0 : ℂ) else 1) = 0 :=
    ite_eq_left rfl
  rw [hφγ, hφu] at hEq
  exact one_ne_zero hEq

end ThetLogos
