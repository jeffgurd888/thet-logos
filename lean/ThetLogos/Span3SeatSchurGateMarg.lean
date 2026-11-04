/-
# W3 REMAINDER R1: the `hMarg` discharge (top form) — K-W3-HMARG-FORM

Brick R1 of the W3 remainder package (scoping dossier
`w3-remainder-scoping-2026-11-03.md` §2, entry R1), fired
under Jeff's full-send grant 2026-11-03. Target: the top
form of `hMarg` — GATE-2's banked splice disintegration,
carried as a hypothesis by item 6's P1
(`seatPairing_pullTop_eq_layerPairing₂_fiberAvg_of_integrable_marg`)
and by both hyp-6 pairings: for every strict-half
observable `a` and layer function `Ψ`,

  `∫ z, a z * Ψ (tauTop hN z) = ∫ u, fiberAvgTop μG hN a u * Ψ u`.

**Verdict on the banked ∀-form: FALSE as stated —
K-W3-HMARG-FORM fires** (the pre-registered form kill of
the scoping dossier; NOT K-W3-HMARG, whose genuinely-
integrable-pair counterexample does not exist: on the
integrable class the identity is a theorem, proved
below). The ∀-form fails only in the non-integrable
junk regime, where the two sides' Bochner junk
conventions diverge: the left side junk-kills the whole
integral when `a * (Ψ ∘ tauTop)` is non-integrable over
the strict-half product, while the right side first
averages over the fibers — where `a` can be honestly
integrable with cancellation — and the resulting layer
function can be honestly integrable with nonzero
integral. Explicit counterexample (decisive write-up in
the landing dossier): at the Circle seat, with `m₀` a
frozen top-image link, `m₁` a free strict-half link,
`c(x) = ‖x − 1‖⁻¹` (Haar-nonintegrable), and
`a z = c (z m₀) * z m₁ + 1`, `Ψ ≡ 1`: fiberwise the
integrand is bounded and the free coordinate integrates
to `0`, so `fiberAvgTop a ≡ 1` and the right side is
`1`; but `∫ ‖a‖ = ∞` by Tonelli, so the left side is
the junk value `0`. In a finite-product model the
∀-form holds (every function is integrable there),
which is why the scoping dossier's finite audit could
not detect this: the failure is purely the junk regime.

**Disposition (per the pre-registered kill): re-pin.**
The banked ∀-form is named below as the definition
`hMargTopStatement` (so the kill and the consumers'
hypothesis have one in-tree address), and the re-pinned
entry `fiberAvgTop_marginal_of_integrable` proves the
identity under the single side condition that the
product integrand `fun z => a z * Ψ (tauTop hN z)` is
integrable over the strict-half product — the
admissible class the scoping dossier named. The proof
is the dossier's route: the coordinate split of the
strict-half links into the image of `embLayerTop` and
its complement (the landed `splitEquiv` /
`integral_pi_restrict` stock), one Fubini step
(`integral_prod`) under the integrability hypothesis,
and the measure-preserving extraction transport
(`integral_comp_emb`). Every other step is junk-safe
(holds for arbitrary integrands). The bottom form of
`hMarg` is NOT built here: the scoping dossier's
correction 1 stands — only the top form is on W3's
critical path.

Frozen statements elsewhere (`hMarg` as carried by
GATE-2's and item 6's theorems) are NOT edited; this
module is a new entry. Consuming the re-pin in place of
the banked hypothesis is R6's wiring.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGatePost
import ThetLogos.LatticeCorrelations
import ThetLogos.PlaneCrossingCube

namespace ThetLogos

open MeasureTheory Finset

section Span3SeatSchurGateMargPure

variable {G : Type*} {N : ℕ} [NeZero N]

/-- **The top coordinate split.** The strict-half links
in the image of the landed embedding `embLayerTop`, as a
finset of the strict-half link type: the coordinates the
top fiber average freezes. -/
abbrev layerTopFinset (hN : Even N) :
    Finset ↥(posLinks (N := N)) :=
  Finset.univ.image (embLayerTop hN)

/-- **Assembly across the top split.** The strict-half
configuration whose top-split coordinates are `v` and
whose complementary coordinates are `w`. -/
def assembleTop (hN : Even N)
    (v : ↥(layerTopFinset hN) → G)
    (w : ↥(layerTopFinset hN)ᶜ → G) :
    ↥(posLinks (N := N)) → G :=
  fun m => if h : m ∈ layerTopFinset hN then v ⟨m, h⟩
    else w ⟨m, Finset.mem_compl.mpr h⟩

theorem assembleTop_apply_of_mem (hN : Even N)
    (v : ↥(layerTopFinset hN) → G)
    (w : ↥(layerTopFinset hN)ᶜ → G)
    {m : ↥(posLinks (N := N))} (hm : m ∈ layerTopFinset hN) :
    assembleTop hN v w m = v ⟨m, hm⟩ :=
  dite_eq_left hm

theorem assembleTop_apply_of_not_mem (hN : Even N)
    (v : ↥(layerTopFinset hN) → G)
    (w : ↥(layerTopFinset hN)ᶜ → G)
    {m : ↥(posLinks (N := N))} (hm : m ∉ layerTopFinset hN) :
    assembleTop hN v w m = w ⟨m, Finset.mem_compl.mpr hm⟩ :=
  dite_eq_right hm

/-- Assembly of a configuration's own two restrictions
is the configuration itself. -/
theorem assembleTop_restrict_self (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) :
    assembleTop hN (fun ℓ : ↥(layerTopFinset hN) => z ℓ.1)
        (fun ℓ : ↥(layerTopFinset hN)ᶜ => z ℓ.1) = z := by
  funext m
  by_cases hm : m ∈ layerTopFinset hN
  · rw [assembleTop_apply_of_mem hN _ _ hm]
  · rw [assembleTop_apply_of_not_mem hN _ _ hm]

/-- A configuration's top-split restriction, transported
along the embedding equivalence, is its top extraction. -/
theorem restrictTop_comp_embEquiv (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) :
    (fun ℓ : ↥(layerTopFinset hN) => z ℓ.1)
        ∘ (embEquiv (embLayerTop hN) (embLayerTop_injective hN))
      = tauTop hN z := by
  funext ℓ
  show z ((embEquiv (embLayerTop hN) (embLayerTop_injective hN)) ℓ).1
    = z (embLayerTop hN ℓ)
  rw [embEquiv_apply]

/-- The splice inside `fiberAvgTop` is assembly across
the top split: the frozen coordinates are the layer
datum transported along the embedding equivalence, the
free coordinates are the configuration's own. -/
theorem spliceTop_eq_assembleTop (hN : Even N)
    (u : LayerLink N → G) (z : ↥(posLinks (N := N)) → G) :
    (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
        then u (Classical.choose h) else z m)
      = assembleTop hN
          (u ∘ (embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)).symm)
          (fun ℓ : ↥(layerTopFinset hN)ᶜ => z ℓ.1) := by
  funext m
  show (if h : ∃ ℓ, embLayerTop hN ℓ = m
      then u (Classical.choose h) else z m)
    = assembleTop hN
        (u ∘ (embEquiv (embLayerTop hN)
          (embLayerTop_injective hN)).symm)
        (fun ℓ : ↥(layerTopFinset hN)ᶜ => z ℓ.1) m
  by_cases hm : m ∈ layerTopFinset hN
  · have hex : ∃ ℓ, embLayerTop hN ℓ = m := by
      obtain ⟨ℓ, _, hℓ⟩ := Finset.mem_image.mp hm
      exact ⟨ℓ, hℓ⟩
    rw [dite_eq_left hex, assembleTop_apply_of_mem hN _ _ hm]
    congr 1
    apply (embLayerTop_injective hN)
    have h2 : embLayerTop hN
        ((embEquiv (embLayerTop hN)
          (embLayerTop_injective hN)).symm ⟨m, hm⟩) = m :=
      congrArg Subtype.val
        (Equiv.apply_symm_apply
          (embEquiv (embLayerTop hN) (embLayerTop_injective hN))
          ⟨m, hm⟩)
    rw [h2]
    exact Classical.choose_spec hex
  · have hnex : ¬ ∃ ℓ, embLayerTop hN ℓ = m := by
      rintro ⟨ℓ, hℓ⟩
      exact hm (Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ ℓ, hℓ⟩)
    rw [dite_eq_right hnex, assembleTop_apply_of_not_mem hN _ _ hm]

end Span3SeatSchurGateMargPure

section Span3SeatSchurGateMarg

variable {G : Type*} [Group G] [MeasurableSpace G]
  [TopologicalSpace G] [SecondCountableTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  {N : ℕ} [NeZero N]

omit [TopologicalSpace G] [SecondCountableTopology G] in
/-- **The fiber average is the complementary marginal.**
`fiberAvgTop` at a layer datum `u` is the integral of
`a` over the complementary coordinates alone, with the
top-split coordinates held at the transported `u`. No
hypotheses: the identity is junk-safe on both sides
(it is the landed `integral_pi_restrict` after the
splice is recognized as assembly). -/
theorem fiberAvgTop_eq_integral_compl (hN : Even N)
    (a : (↥(posLinks (N := N)) → G) → ℂ)
    (u : LayerLink N → G) :
    fiberAvgTop μG hN a u
      = ∫ w : ↥(layerTopFinset hN)ᶜ → G,
          a (assembleTop hN
            (u ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)).symm) w)
        ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG) := by
  have e1 : (∫ z : ↥(posLinks (N := N)) → G,
        a (fun m => if h : ∃ ℓ, embLayerTop hN ℓ = m
          then u (Classical.choose h) else z m)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ z : ↥(posLinks (N := N)) → G,
          (fun w => a (assembleTop hN
            (u ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)).symm) w))
            (fun ℓ : ↥(layerTopFinset hN)ᶜ => z ℓ.1)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
    integral_congr_ae (ae_of_all _ fun z =>
      congrArg a (spliceTop_eq_assembleTop hN u z))
  show fiberAvgTop μG hN a u = _
  unfold fiberAvgTop
  rw [e1]
  exact integral_pi_restrict μG (layerTopFinset hN)ᶜ
    (fun w => a (assembleTop hN
      (u ∘ (embEquiv (embLayerTop hN)
        (embLayerTop_injective hN)).symm) w))

/-- **The banked ∀-form of `hMarg` (top), as a named
statement.** This is the hypothesis GATE-2 banked and
item 6's P1 carries. It is FALSE as stated —
K-W3-HMARG-FORM (see the module face): it holds exactly
on the admissible (integrable) class, which is the
re-pinned entry `fiberAvgTop_marginal_of_integrable`
below. The definition is landed so the kill and the
consumers' hypothesis share one in-tree address;
nothing in this module proves this ∀-form, and no
landed theorem is restated. -/
def hMargTopStatement (hN : Even N) : Prop :=
  ∀ (a : (↥(posLinks (N := N)) → G) → ℂ)
    (Ψ : (LayerLink N → G) → ℂ),
    (∫ z, a z * Ψ (tauTop hN z)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = ∫ u, fiberAvgTop μG hN a u * Ψ u
      ∂(Measure.pi fun _ : LayerLink N => μG)

/-- **R1, the re-pinned `hMarg` (top form): the splice
disintegration on the admissible class.** For every
strict-half observable `a` and layer function `Ψ` whose
product integrand `fun z => a z * Ψ (tauTop hN z)` is
integrable over the strict-half product, integrating
against the pulled-back layer function equals
integrating the top fiber average against it:

  `∫ z, a z * Ψ (tauTop hN z) = ∫ u, fiberAvgTop μG hN a u * Ψ u`.

This is the conditional-expectation property of the
landed `fiberAvgTop` under the product pi measure,
proved by the coordinate split, one Fubini step under
the integrability hypothesis, and the measure-
preserving extraction transport; every other step is
junk-safe. It replaces the banked ∀-form
(`hMargTopStatement`), which is false in the
non-integrable junk regime (K-W3-HMARG-FORM). -/
theorem fiberAvgTop_marginal_of_integrable (hN : Even N)
    (a : (↥(posLinks (N := N)) → G) → ℂ)
    (Ψ : (LayerLink N → G) → ℂ)
    (hInt : Integrable (fun z => a z * Ψ (tauTop hN z))
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :
    (∫ z, a z * Ψ (tauTop hN z)
      ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    = ∫ u, fiberAvgTop μG hN a u * Ψ u
      ∂(Measure.pi fun _ : LayerLink N => μG) := by
  classical
  -- The split integrand on the product of the two halves.
  set F : (↥(layerTopFinset hN) → G) × (↥(layerTopFinset hN)ᶜ → G)
      → ℂ :=
    fun p => a (assembleTop hN p.1 p.2)
      * Ψ (p.1 ∘ (embEquiv (embLayerTop hN)
          (embLayerTop_injective hN))) with hF
  -- Pointwise: the split integrand composed with the
  -- splitting equiv is the original integrand.
  have hcomp : ∀ z : ↥(posLinks (N := N)) → G,
      F (splitEquiv (layerTopFinset hN) z)
        = a z * Ψ (tauTop hN z) := by
    intro z
    rw [hF]
    show a (assembleTop hN (splitEquiv (layerTopFinset hN) z).1
          (splitEquiv (layerTopFinset hN) z).2)
        * Ψ ((splitEquiv (layerTopFinset hN) z).1
          ∘ (embEquiv (embLayerTop hN) (embLayerTop_injective hN)))
      = a z * Ψ (tauTop hN z)
    rw [splitEquiv_fst, splitEquiv_snd,
      assembleTop_restrict_self, restrictTop_comp_embEquiv]
  -- Integrability transports across the splitting equiv.
  have hIntF : Integrable F
      ((Measure.pi fun _ : ↥(layerTopFinset hN) => μG).prod
        (Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG)) := by
    have hiff := (measurePreserving_splitEquiv μG
      (layerTopFinset hN)).integrable_comp_emb
      (splitEquiv (layerTopFinset hN)).measurableEmbedding (g := F)
    exact hiff.mp (hInt.congr (ae_of_all _ fun z => (hcomp z).symm))
  -- Step 1: transport the left side across the split.
  have step1 : (∫ z, a z * Ψ (tauTop hN z)
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ p : (↥(layerTopFinset hN) → G)
          × (↥(layerTopFinset hN)ᶜ → G), F p
        ∂((Measure.pi fun _ : ↥(layerTopFinset hN) => μG).prod
          (Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG)) := by
    have e1 : (∫ z, a z * Ψ (tauTop hN z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
        = ∫ z, F (splitEquiv (layerTopFinset hN) z)
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG) :=
      integral_congr_ae (ae_of_all _ fun z => (hcomp z).symm)
    rw [e1]
    exact (measurePreserving_splitEquiv μG
      (layerTopFinset hN)).integral_comp
      (splitEquiv (layerTopFinset hN)).measurableEmbedding F
  -- Step 2: the one Fubini step, under `hIntF`.
  have step2 : (∫ p : (↥(layerTopFinset hN) → G)
          × (↥(layerTopFinset hN)ᶜ → G), F p
        ∂((Measure.pi fun _ : ↥(layerTopFinset hN) => μG).prod
          (Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG)))
      = ∫ v : ↥(layerTopFinset hN) → G,
          (∫ w : ↥(layerTopFinset hN)ᶜ → G,
            a (assembleTop hN v w)
            ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
          * Ψ (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
        ∂(Measure.pi fun _ : ↥(layerTopFinset hN) => μG) := by
    rw [integral_prod F hIntF]
    apply integral_congr_ae
    filter_upwards with v
    rw [hF]
    show (∫ w : ↥(layerTopFinset hN)ᶜ → G,
        a (assembleTop hN v w)
          * Ψ (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
        ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
      = (∫ w : ↥(layerTopFinset hN)ᶜ → G,
          a (assembleTop hN v w)
          ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
        * Ψ (v ∘ (embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)))
    rw [integral_mul_const]
  -- Step 3: the inner integral at `v ∘ ê` is the fiber
  -- average, and the outer transport is `integral_comp_emb`.
  have step3 : (∫ v : ↥(layerTopFinset hN) → G,
          (∫ w : ↥(layerTopFinset hN)ᶜ → G,
            a (assembleTop hN v w)
            ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
          * Ψ (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
        ∂(Measure.pi fun _ : ↥(layerTopFinset hN) => μG))
      = ∫ u, fiberAvgTop μG hN a u * Ψ u
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    have hG : ∀ v : ↥(layerTopFinset hN) → G,
        (∫ w : ↥(layerTopFinset hN)ᶜ → G,
            a (assembleTop hN v w)
            ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
          * Ψ (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
          = (fun u => fiberAvgTop μG hN a u * Ψ u)
            (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN))) := by
      intro v
      have htr : (v ∘ (embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)))
          ∘ (embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)).symm = v := by
        funext m
        show v ((embEquiv (embLayerTop hN)
          (embLayerTop_injective hN))
          ((embEquiv (embLayerTop hN)
            (embLayerTop_injective hN)).symm m)) = v m
        rw [Equiv.apply_symm_apply]
      show (∫ w : ↥(layerTopFinset hN)ᶜ → G,
            a (assembleTop hN v w)
            ∂(Measure.pi fun _ : ↥(layerTopFinset hN)ᶜ => μG))
          * Ψ (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
        = fiberAvgTop μG hN a
            (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
          * Ψ (v ∘ (embEquiv (embLayerTop hN)
              (embLayerTop_injective hN)))
      rw [fiberAvgTop_eq_integral_compl μG hN a
        (v ∘ (embEquiv (embLayerTop hN)
          (embLayerTop_injective hN))), htr]
    rw [integral_congr_ae (ae_of_all _ hG)]
    exact integral_comp_emb μG
      (embEquiv (embLayerTop hN) (embLayerTop_injective hN))
      (Equiv.injective _)
      (fun u => fiberAvgTop μG hN a u * Ψ u)
  rw [step1, step2, step3]

end Span3SeatSchurGateMarg

end ThetLogos
