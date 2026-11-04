/-
# W3 REMAINDER R2a: `hCross` DISCHARGED — the two twirls agree

Brick R2a (build stage) of the W3 remainder package
(scoping dossier `w3-remainder-scoping-2026-11-03.md`
§2; falsity probe
`w3-r2a-hcross-probe-report-2026-11-03.md`, exhausted
with no counterexample). GATE-0 item 6's assembly
(`gate4c_hyp6_of_named_inputs`,
`ThetLogos.Span3SeatSchurGateItem6`) consumes five
per-pair named inputs for GATE-4C hypothesis 6; this
module discharges `hCross`: the pos-dressed
and mirror-dressed top fiber averages agree,

`fiberAvgTop μG hN (fun z => (posGaugeAvg μG f) z
    * φ' (tauBot hN z))
  = fiberAvgTop μG hN (fun z => (mirrorGaugeAvg μG f) z
    * φ' (tauBot hN z))`,

in exactly the form item 6's `P2`
(`seatPairing_dressed_marginal_nonneg_of_cross`)
takes as a hypothesis and its assembly (P4) consumes
per pair. No hypotheses on `f` or `φ'` are used, and
none of `hN`'s evenness beyond the fiber average's own
argument: the identity is proved at the level of the
twirls themselves.

**Route** (the probe's §4 mechanism, verified here in
corpus vocabulary — probe grade there, theorem here):
the mirror action on a strict-half configuration is
the plain linkwise gauge action of the *reflected*
gauge function, `gaugeMirrorPos g
= gaugePosFun (g ∘ reflSite)`, pointwise at every
link — in direction `≠ 0` by the spatial commutation
`reflSite_torusShift_of_ne`, in direction `0` by
`reflSite_torusShift_zero`, where the mirror's
inversion branch is exactly what the reflected
parametrization produces — and precomposition with
`reflSite` preserves the product Haar measure on
gauge functions (`MeasurableEquiv.piCongrLeft` at the
site permutation). Hence `mirrorGaugeAvg
= posGaugeAvg` as functions, and `hCross` follows by
congruence. K-W3-CROSS does NOT fire: the identity
holds at every even `N` (indeed the twirl equality
needs no evenness at all), for the corpus's general
`(G, μG)`.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4.
**The fence, on the face:** this discharges ONE of
item 6's five named inputs. `hCrossFold` (R2b), the
two dressed integrabilities (R2d+R3a), and — for the
assembly — the `hMarg` re-pin consumption (R6's wiring
question) remain open; hypothesis 6 is NOT discharged;
GATE-4C's frozen statement is untouched; W3
(`seatSchurProductStepOpen`) remains OPEN. This is a
route fact only — it is not K-F2-2, and nothing here
certifies any pairing's sign. The gate + W3 prove
neither FACT nor clause (a); `LayerKernelPos`,
`𝒜 ⪰ 0`, and uniformity remain open.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGatePost
import ThetLogos.PlaneCrossingSeparate
import ThetLogos.PlaneCrossingSymm
import ThetLogos.PlaneCrossingCube
import ThetLogos.LatticeReflection

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateW3Cross

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §1. The site permutation and the reflected
reparametrization of gauge-function space -/

/-- The site reflection as a permutation of the site
torus (the involution `reflSite`, packaged). -/
def reflSitePerm : Equiv.Perm (Fin 4 → ZMod N) :=
  Function.Involutive.toPerm _ reflSite_involutive

@[simp]
theorem reflSitePerm_apply (x : Fin 4 → ZMod N) :
    reflSitePerm x = reflSite x :=
  rfl

/-- Precomposition with the site reflection, as a
measurable equivalence of gauge-function space: the
`piCongrLeft` transport at the site permutation,
symmetrized so that it sends `g` to `g ∘ reflSite`. -/
def gaugeReflPrecompEquiv :
    ((Fin 4 → ZMod N) → G) ≃ᵐ ((Fin 4 → ZMod N) → G) :=
  (MeasurableEquiv.piCongrLeft (fun _ : (Fin 4 → ZMod N) => G)
    reflSitePerm).symm

omit [Group G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem gaugeReflPrecompEquiv_apply
    (g : (Fin 4 → ZMod N) → G) (x : Fin 4 → ZMod N) :
    gaugeReflPrecompEquiv g x = g (reflSite x) :=
  rfl

omit [Group G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem gaugeReflPrecompEquiv_apply_fun
    (g : (Fin 4 → ZMod N) → G) :
    gaugeReflPrecompEquiv g = g ∘ reflSite :=
  funext fun x => gaugeReflPrecompEquiv_apply g x

omit [Group G] [MeasurableInv G] [IsTopologicalGroup G]
  [BorelSpace G] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- **Step 2 — the pushforward.** Precomposition with
the site reflection preserves the product Haar measure
on gauge functions: the pi-measure is invariant under
reindexing its factors by a permutation of the index
set, here the site reflection itself. -/
theorem measurePreserving_gaugeReflPrecompEquiv :
    MeasurePreserving gaugeReflPrecompEquiv
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
  MeasurePreserving.symm _
    (measurePreserving_piCongrLeft
      (fun _ : (Fin 4 → ZMod N) => μG) reflSitePerm)

/-! ## §2. Step 1: the mirror action is the reflected
plain action -/

omit [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- **Step 1, link level.** The mirror's linkwise value
at a link `(x, μ)` — inversion branch included — is
the plain linkwise gauge value at the same link of the
reflected gauge function `g ∘ reflSite`. In direction
`μ ≠ 0` both sides read `g (reflSite x) * v
* (g (reflSite (shift x)))⁻¹` by the spatial
commutation of reflection and shift; in direction
`0` the reflected link is based at
`(σ₀)⁻¹ (reflSite x)`, the outer inversion of the
mirror branch turns `g y * v⁻¹ * (g (σ₀ y))⁻¹` into
`g (reflSite x) * v * (g y)⁻¹`, and
`reflSite_torusShift_zero` identifies the reflected
shifted site with that same base `y`. -/
theorem gaugeLinkVal_reflLink (g : (Fin 4 → ZMod N) → G)
    (x : Fin 4 → ZMod N) (μ : Fin 4) (v : G) :
    (if μ = 0 then (gaugeLinkVal g (reflLink (x, μ)) v⁻¹)⁻¹
      else gaugeLinkVal g (reflLink (x, μ)) v)
      = gaugeLinkVal (g ∘ reflSite) (x, μ) v := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [ite_eq_left rfl, reflLink_zero]
    show (g ((torusShift N 0).symm (reflSite x)) * v⁻¹
          * (g (torusShift N 0
              ((torusShift N 0).symm (reflSite x))))⁻¹)⁻¹
        = g (reflSite x) * v
          * (g (reflSite (torusShift N 0 x)))⁻¹
    rw [Equiv.apply_symm_apply, reflSite_torusShift_zero]
    group
  · rw [ite_eq_right hμ, reflLink_of_ne hμ]
    show g (reflSite x) * v
          * (g (torusShift N μ (reflSite x)))⁻¹
        = g (reflSite x) * v
          * (g (reflSite (torusShift N μ x)))⁻¹
    rw [reflSite_torusShift_of_ne hμ]

omit [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- **Step 1 — the mirror action is the reflected
plain action.** For every gauge function `g` and every
strict-half configuration `z`, the mirror transport
of the gauge action agrees with the plain linkwise
action of the reflected gauge function:
`gaugeMirrorPos g z = gaugePosFun (g ∘ reflSite) z`,
at every strict-half link, the direction-`0`
inversion branch included. -/
theorem gaugeMirrorPos_eq_gaugePosFun_reflComp
    (g : (Fin 4 → ZMod N) → G)
    (z : ↥(posLinks (N := N)) → G) :
    gaugeMirrorPos g z = gaugePosFun (g ∘ reflSite) z := by
  funext m
  obtain ⟨⟨x, μ⟩, hm⟩ := m
  exact gaugeLinkVal_reflLink g x μ (z ⟨⟨x, μ⟩, hm⟩)

/-! ## §3. The twirls agree, and `hCross` -/

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **Step 3, the engine — the two twirls agree.**
The mirror gauge average of any strict-half observable
equals its plain gauge average: substitute the
reflected gauge function in the mirror average (step
1), then change variables by the reflected
reparametrization, which preserves the product Haar
measure (step 2). No hypothesis on the observable, and
no evenness or size condition on `N`. -/
theorem posGaugeAvg_eq_mirrorGaugeAvg
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (z : ↥(posLinks (N := N)) → G) :
    posGaugeAvg μG f z = mirrorGaugeAvg μG f z := by
  have hsub : ∀ h : (Fin 4 → ZMod N) → G,
      f (gaugeMirrorPos h z)
        = f (gaugePosFun (gaugeReflPrecompEquiv h) z) := by
    intro h
    rw [gaugeReflPrecompEquiv_apply_fun,
      gaugeMirrorPos_eq_gaugePosFun_reflComp]
  unfold mirrorGaugeAvg posGaugeAvg
  rw [integral_congr_ae (ae_of_all _ hsub)]
  exact ((measurePreserving_gaugeReflPrecompEquiv μG).integral_comp
    gaugeReflPrecompEquiv.measurableEmbedding
    (fun g => f (gaugePosFun g z))).symm

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **R2a — `hCross` discharged.** The pos-dressed and
mirror-dressed top fiber averages agree, in the exact
form item 6's marginal pairing (P2,
`seatPairing_dressed_marginal_nonneg_of_cross`) takes
as its `hCross` hypothesis and the assembly (P4,
`gate4c_hyp6_of_named_inputs`) consumes per pair: for
every even `N`, every strict-half observable `f` and
every layer function `φ'`, with no hypotheses on
either,

`fiberAvgTop μG hN (fun z => (posGaugeAvg μG f) z
    * φ' (tauBot hN z))
  = fiberAvgTop μG hN (fun z => (mirrorGaugeAvg μG f) z
    * φ' (tauBot hN z))`.

The two dressed integrands differ only in the twirl,
and the twirls are the same function
(`posGaugeAvg_eq_mirrorGaugeAvg`). -/
theorem fiberAvgTop_twirled_mul_pullback_cross_proved
    (hN : Even N)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (φ' : (LayerLink N → G) → ℂ) :
    fiberAvgTop μG hN
        (fun z => (posGaugeAvg μG f) z * φ' (tauBot hN z))
      = fiberAvgTop μG hN
        (fun z => (mirrorGaugeAvg μG f) z * φ' (tauBot hN z)) := by
  congr 1
  funext z
  rw [posGaugeAvg_eq_mirrorGaugeAvg]

end Span3SeatSchurGateW3Cross

end ThetLogos
