/-
# POSITIVITY BRIDGE — the core-chain run after item 5

Brick: the positivity bridge priced by
`~/workspace/your_files/positivity-bridge-scoping-2026-11-03.md`
(PB-1 BRIDGE-SEP, PB-2 operator transport, PB-3 strictification
+ assembly), commissioned under Jeff's full-send 2026-11-03.
The `𝒜 ⪰ 0` core chain is SINGLE LANE ALWAYS; this module is
that lane's landing. Built in the isolated worktree
`~/workspace/thet-logos-posbridge`, branch `posbridge-lane`,
from main-tree HEAD `4e35329` (the item-5 ceremony commit);
NOT integrated — the parent runs the ceremony.

## VERDICT (on the face): FULL BRIDGE

PB-1 BRIDGE-SEP stands (`layerKernel_gauge_invariant`: the
layer kernel is invariant under independent gauge actions
in its two slots separately). PB-2 stands (the kernel
representative of the layer operator is exactly
gauge-invariant; the form identity
`layerKernelOp_inner_gaugeAvg`). PB-3 stands with NO
strictification seam: the gauge average is an exactly
invariant representative (`gaugeAvg_gauge_invariant`), the
master identity `layerPairingProd_gaugeAvg` holds, and
BRIDGE-MAIN `layerKernelPosAll_of_layerKernelPos` proves
`LayerKernelPos` (under `hρcont`) ⇒ `LayerKernelPosAll`.
BRIDGE-COR fires item 5's conditional headline at the
frozen generality: `SeatFactorApproxExpansion` under
`LayerKernelPos` + `hρcont`, including the frozen ∀-form
`pullBotKernel_seatFactorApproxExpansion`
(`pullBotKernel_seatFactorApproxExpansion_of_cont`).
K-POS-BRIDGE did NOT fire. `LayerKernelPos` itself stays
OPEN — the bridge is an implication. Full record:
`whitepaper/positivity-bridge-landing-2026-11-03.md`.

## ERRATUM (on the face)

Item 5's module header (and `Span3SeatSchurGateItem5`'s face)
states that `layerKernel` "is not separately first-slot
invariant in general (G2c dossier obstruction)". PB-1 below
PROVES separate invariance of `layerKernel` in each slot
(`layerKernel_gauge_invariant`): the sentence is **incorrect
as stated** for the layer gauge action. The G2c obstruction on
record concerns dressed *fiber averages* of observables, not
invariance of the kernel. The landed item-5 module is NOT
edited; this erratum rides this module's header, the landing
dossier, and the ceremony record.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. `LayerKernelPos` itself
stays OPEN: the bridge is an implication between open
statements, never a proof of `LayerKernelPos`, `𝒜 ⪰ 0`,
FACT, or clause (a) (K-F2-4).

This module is NOT in the root import list of the library;
it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGateItem5
import ThetLogos.LayerKernelPos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace ThetLogos

open MeasureTheory Finset Filter Topology ComplexInnerProductSpace
open scoped Matrix ENNReal NNReal

section PosBridge

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## PB-1 — BRIDGE-SEP: separate invariance of the layer kernel -/

omit [MeasurableSpace G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [NeZero N] in
/-- The layer gauge action read at a layer link over `c` in
direction `ν`: the two-sided link value. -/
theorem layerGaugeAction_apply_linkOf
    (g : (Fin 4 → ZMod N) → G) (u : LayerLink N → G)
    (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    layerGaugeAction g u (layerLinkOf c ν hν)
      = g c.1 * u (layerLinkOf c ν hν)
        * (g (torusShift N ν c.1))⁻¹ :=
  rfl

/-- The stratum substitution of BRIDGE-SEP, as a function:
`α ↦ (c ↦ (g c)⁻¹ · α c · g' c)` — the inverse substitution,
taken as the measurable equivalence's forward map so the
Haar integral over the stratum can be transported along it. -/
def stratumSubstFun (g g' : (Fin 4 → ZMod N) → G)
    (α : LayerSite N → G) : LayerSite N → G :=
  fun c => (g c.1)⁻¹ * α c * g' c.1

/-- The stratum substitution as a measurable equivalence of
the pi-Haar stratum space (per-coordinate two-sided
translation). -/
def stratumSubstEquiv (g g' : (Fin 4 → ZMod N) → G) :
    (LayerSite N → G) ≃ᵐ (LayerSite N → G) where
  toFun := stratumSubstFun g g'
  invFun α c := g c.1 * α c * (g' c.1)⁻¹
  left_inv α := by
    funext c
    show g c.1 * ((g c.1)⁻¹ * α c * g' c.1) * (g' c.1)⁻¹ = α c
    group
  right_inv α := by
    funext c
    show (g c.1)⁻¹ * (g c.1 * α c * (g' c.1)⁻¹) * g' c.1 = α c
    group
  measurable_toFun := by
    refine measurable_pi_iff.mpr fun c => ?_
    show Measurable (fun α : LayerSite N → G =>
      (g c.1)⁻¹ * α c * g' c.1)
    exact (measurable_const.mul (measurable_pi_apply c)).mul
      measurable_const
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun c => ?_
    show Measurable (fun α : LayerSite N → G =>
      g c.1 * α c * (g' c.1)⁻¹)
    exact (measurable_const.mul (measurable_pi_apply c)).mul
      measurable_const

omit [MeasurableInv G] [μG.IsInvInvariant] in
/-- The stratum substitution preserves the pi-Haar measure
(the landed `measurePreserving_pi` idiom, as in
`measurePreserving_gaugeStratumEquiv`). -/
theorem measurePreserving_stratumSubst
    (g g' : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (stratumSubstFun g g')
      (Measure.pi fun _ : LayerSite N => μG)
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine measurePreserving_pi
    (f := fun c v => (g c.1)⁻¹ * v * g' c.1)
    (fun _ : LayerSite N => μG) (fun _ : LayerSite N => μG)
    fun c => ?_
  show MeasurePreserving (fun v : G => (g c.1)⁻¹ * v * g' c.1)
    μG μG
  exact (measurePreserving_mul_right μG _).comp
    (measurePreserving_mul_left μG _)

/-- **The word computation of BRIDGE-SEP**: under the joint
transformation — stratum by the forward substitution
`α ↦ (c ↦ g c · α c · (g' c)⁻¹)`, first slot by `g`, second
slot by `g'` — every one-layer plaquette word conjugates by
`g c`. -/
theorem plaquette_layerConfig_gauge (hN : Even N)
    (g g' : (Fin 4 → ZMod N) → G) (α : LayerSite N → G)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) :
    plaquette (torusShift N)
        (layerConfig (fun c => g c.1 * α c * (g' c.1)⁻¹)
          (layerGaugeAction g u) (layerGaugeAction g' u'))
        c.1 0 ν
      = g c.1 * plaquette (torusShift N) (layerConfig α u u')
          c.1 0 ν * (g c.1)⁻¹ := by
  rw [plaquette_layerConfig hN, plaquette_layerConfig hN,
    layerGaugeAction_apply_linkOf g u c ν hν,
    layerGaugeAction_apply_linkOf g' u' c ν hν]
  show g c.1 * α c * (g' c.1)⁻¹
      * (g' c.1 * u' (layerLinkOf c ν hν)
        * (g' (torusShift N ν c.1))⁻¹)
      * (g (torusShift N ν c.1) * α (layerShift ν hν c)
        * (g' (torusShift N ν c.1))⁻¹)⁻¹
      * (g c.1 * u (layerLinkOf c ν hν)
        * (g (torusShift N ν c.1))⁻¹)⁻¹
    = g c.1 * (α c * u' (layerLinkOf c ν hν)
        * (α (layerShift ν hν c))⁻¹
        * (u (layerLinkOf c ν hν))⁻¹) * (g c.1)⁻¹
  group

/-- The one-layer action is invariant under the joint
transformation of BRIDGE-SEP (each plaquette word conjugates,
and `plaquetteDensity` sees the word only through
`Re tr ρ(·)`). -/
theorem layerAction_gauge (hN : Even N)
    (g g' : (Fin 4 → ZMod N) → G) (β : ℝ) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    layerAction ρ β (fun c => g c.1 * α c * (g' c.1)⁻¹)
        (layerGaugeAction g u) (layerGaugeAction g' u')
      = layerAction ρ β α u u' := by
  unfold layerAction
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Finset.mem_Ioi] at hν
  unfold plaquetteDensity
  rw [plaquette_layerConfig_gauge hN g g' α u u' c ν
    (ne_of_gt hν), trace_repMatrix_conj]

omit [μG.IsInvInvariant] in
/-- **PB-1, BRIDGE-SEP**: the layer kernel is invariant under
INDEPENDENT gauge actions in its two slots separately. At
every `Even N`, every `β` (no sign hypothesis), all gauge
functions `g g'`, all layer data `u u'`. -/
theorem layerKernel_gauge_invariant (hN : Even N) (β : ℝ)
    (g g' : (Fin 4 → ZMod N) → G) (u u' : LayerLink N → G) :
    layerKernel μG ρ β (layerGaugeAction g u)
        (layerGaugeAction g' u')
      = layerKernel μG ρ β u u' := by
  have key : ∀ α : LayerSite N → G,
      layerAction ρ β α (layerGaugeAction g u)
          (layerGaugeAction g' u')
        = layerAction ρ β (stratumSubstFun g g' α) u u' := by
    intro α
    have h := layerAction_gauge ρ hN g g' β
      (stratumSubstFun g g' α) u u'
    have hinv : (fun c => g c.1 * (stratumSubstFun g g' α) c
        * (g' c.1)⁻¹) = α := by
      funext c
      show g c.1 * ((g c.1)⁻¹ * α c * g' c.1) * (g' c.1)⁻¹
        = α c
      group
    rwa [hinv] at h
  have hmp : MeasurePreserving (⇑(stratumSubstEquiv g g'))
      (Measure.pi fun _ : LayerSite N => μG)
      (Measure.pi fun _ : LayerSite N => μG) :=
    measurePreserving_stratumSubst μG g g'
  have hcomp : (∫ α : LayerSite N → G,
        (Real.exp (-(layerAction ρ β α u u')) : ℂ)
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α : LayerSite N → G,
        (Real.exp (-(layerAction ρ β
          (stratumSubstFun g g' α) u u')) : ℂ)
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (hmp.integral_comp (stratumSubstEquiv g g').measurableEmbedding
      (fun α => (Real.exp (-(layerAction ρ β α u u')) : ℂ))).symm
  unfold layerKernel
  rw [hcomp]
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  show (Real.exp (-(layerAction ρ β α (layerGaugeAction g u)
      (layerGaugeAction g' u'))) : ℂ)
    = (Real.exp (-(layerAction ρ β (stratumSubstFun g g' α)
        u u')) : ℂ)
  rw [key α]

omit [MeasurableSpace G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [NeZero N] in
/-- The trivial gauge function acts trivially on layer data. -/
theorem layerGaugeAction_one (u : LayerLink N → G) :
    layerGaugeAction (fun _ => 1) u = u := by
  funext ℓ
  show (1 : G) * u ℓ * ((1 : G))⁻¹ = u ℓ
  simp

omit [μG.IsInvInvariant] in
/-- BRIDGE-SEP, first slot only. -/
theorem layerKernel_gauge_invariant_fst (hN : Even N) (β : ℝ)
    (g : (Fin 4 → ZMod N) → G) (u u' : LayerLink N → G) :
    layerKernel μG ρ β (layerGaugeAction g u) u'
      = layerKernel μG ρ β u u' := by
  have h := layerKernel_gauge_invariant μG ρ hN β g
    (fun _ => 1) u u'
  rwa [layerGaugeAction_one] at h

omit [μG.IsInvInvariant] in
/-- BRIDGE-SEP, second slot only. -/
theorem layerKernel_gauge_invariant_snd (hN : Even N) (β : ℝ)
    (g' : (Fin 4 → ZMod N) → G) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u (layerGaugeAction g' u')
      = layerKernel μG ρ β u u' := by
  have h := layerKernel_gauge_invariant μG ρ hN β
    (fun _ => 1) g' u u'
  rwa [layerGaugeAction_one] at h

/-! ## PB-2 — operator transport -/

omit [μG.IsInvInvariant] in
/-- The kernel-defined representative of the layer operator
is unchanged at a gauge-transformed point (BRIDGE-SEP, first
slot, inside the integral that defines the representative). -/
theorem integralKernelFun_layerKernelFun_gauge (hN : Even N)
    (β : ℝ) (F : (LayerLink N → G) → ℂ)
    (g : (Fin 4 → ZMod N) → G) (x : LayerLink N → G) :
    integralKernelFun (Measure.pi fun _ : LayerLink N => μG)
        (layerKernelFun μG ρ β) F (layerGaugeAction g x)
      = integralKernelFun
          (Measure.pi fun _ : LayerLink N => μG)
          (layerKernelFun μG ρ β) F x := by
  unfold integralKernelFun
  refine integral_congr_ae (ae_of_all _ fun u' => ?_)
  show layerKernel μG ρ β (layerGaugeAction g x) u' * F u'
    = layerKernel μG ρ β x u' * F u'
  rw [layerKernel_gauge_invariant_fst μG ρ hN β g x u']

omit [μG.IsInvInvariant] in
/-- The kernel-defined representative of the layer operator
is an exactly gauge-invariant layer observable. -/
theorem gaugeInvariantLayerObs_integralKernelFun
    (hN : Even N) (β : ℝ) (F : (LayerLink N → G) → ℂ) :
    GaugeInvariantLayerObs
      (integralKernelFun (Measure.pi fun _ : LayerLink N => μG)
        (layerKernelFun μG ρ β) F) :=
  fun g x => integralKernelFun_layerKernelFun_gauge μG ρ hN β
    F g x

omit [μG.IsInvInvariant] in
/-- **PB-2, range inside invariants**: for every `f : Lp`,
the class `integralKernelOp hK f` has an exactly
gauge-invariant representative — its kernel-defined
representative (`coeFn_integralKernelOp`). -/
theorem exists_gaugeInvariantLayerObs_rep (hN : Even N)
    (β : ℝ)
    (hK : MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)))
    (f : Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)) :
    ∃ H : (LayerLink N → G) → ℂ, GaugeInvariantLayerObs H ∧
      ⇑(integralKernelOp hK f)
        =ᵐ[Measure.pi fun _ : LayerLink N => μG] H :=
  ⟨integralKernelFun (Measure.pi fun _ : LayerLink N => μG)
      (layerKernelFun μG ρ β) ⇑f,
    gaugeInvariantLayerObs_integralKernelFun μG ρ hN β ⇑f,
    coeFn_integralKernelOp hK f⟩

/-! ## PB-3 — strictification by gauge averaging, and assembly -/

omit [MeasurableSpace G] [MeasurableInv G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [NeZero N] in
/-- Composition law for the layer gauge action: acting by
`h` then by `g` is acting by the pointwise product. -/
theorem layerGaugeAction_comp (g h : (Fin 4 → ZMod N) → G)
    (u : LayerLink N → G) :
    layerGaugeAction g (layerGaugeAction h u)
      = layerGaugeAction (fun x => g x * h x) u := by
  funext ℓ
  show g ℓ.1.1 * (h ℓ.1.1 * u ℓ
      * (h (torusShift N ℓ.1.2 ℓ.1.1))⁻¹)
      * (g (torusShift N ℓ.1.2 ℓ.1.1))⁻¹
    = (g ℓ.1.1 * h ℓ.1.1) * u ℓ
      * (g (torusShift N ℓ.1.2 ℓ.1.1)
        * h (torusShift N ℓ.1.2 ℓ.1.1))⁻¹
  rw [mul_inv_rev]
  group

/-- Right multiplication of gauge functions, as a measurable
equivalence of the gauge group. -/
def gaugeMulEquiv (γ₀ : (Fin 4 → ZMod N) → G) :
    ((Fin 4 → ZMod N) → G) ≃ᵐ ((Fin 4 → ZMod N) → G) where
  toFun g x := g x * γ₀ x
  invFun g x := g x * (γ₀ x)⁻¹
  left_inv g := by
    funext x
    dsimp only
    group
  right_inv g := by
    funext x
    dsimp only
    group
  measurable_toFun := by
    refine measurable_pi_iff.mpr fun x => ?_
    exact (measurable_pi_apply x).mul measurable_const
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun x => ?_
    exact (measurable_pi_apply x).mul measurable_const

omit [MeasurableInv G] [μG.IsMulLeftInvariant]
  [μG.IsInvInvariant] in
/-- Right multiplication of gauge functions preserves the
product Haar measure. -/
theorem measurePreserving_gaugeMulEquiv
    (γ₀ : (Fin 4 → ZMod N) → G) :
    MeasurePreserving (fun g x => g x * γ₀ x)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
  refine measurePreserving_pi
    (f := fun x v => v * γ₀ x)
    (fun _ : (Fin 4 → ZMod N) => μG)
    (fun _ : (Fin 4 → ZMod N) => μG) fun x => ?_
  exact measurePreserving_mul_right μG (γ₀ x)

/-- **The strictification of PB-3**: the gauge average of a
layer observable over the gauge group (product Haar
probability). Defined for every `F`; its invariance is
exact and pointwise, by Haar substitution in the defining
integral — no exceptional set is involved. -/
noncomputable def gaugeAvg (F : (LayerLink N → G) → ℂ) :
    (LayerLink N → G) → ℂ :=
  fun u => ∫ g : (Fin 4 → ZMod N) → G,
    F (layerGaugeAction g u)
    ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)

omit [MeasurableInv G] [μG.IsMulLeftInvariant]
  [μG.IsInvInvariant] in
/-- The gauge average is exactly gauge-invariant, for every
`F` whatsoever. -/
theorem gaugeAvg_gauge_invariant (F : (LayerLink N → G) → ℂ) :
    GaugeInvariantLayerObs (gaugeAvg μG F) := by
  intro γ₀ u
  have hmp : MeasurePreserving (⇑(gaugeMulEquiv γ₀))
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
    measurePreserving_gaugeMulEquiv μG γ₀
  have h1 : (∫ g : (Fin 4 → ZMod N) → G,
        F (layerGaugeAction g (layerGaugeAction γ₀ u))
        ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
      = ∫ g : (Fin 4 → ZMod N) → G,
        F (layerGaugeAction (⇑(gaugeMulEquiv γ₀) g) u)
        ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    show F (layerGaugeAction g (layerGaugeAction γ₀ u))
      = F (layerGaugeAction (fun x => g x * γ₀ x) u)
    rw [layerGaugeAction_comp]
  show (∫ g : (Fin 4 → ZMod N) → G,
      F (layerGaugeAction g (layerGaugeAction γ₀ u))
      ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
    = ∫ g : (Fin 4 → ZMod N) → G, F (layerGaugeAction g u)
      ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
  rw [h1]
  exact hmp.integral_comp (gaugeMulEquiv γ₀).measurableEmbedding
    (fun h => F (layerGaugeAction h u))

omit [NeZero N] in
/-- The joint gauge action `(g, u) ↦ γ_g u` is measurable. -/
theorem measurable_gaugeAction_prod :
    Measurable (fun p : ((Fin 4 → ZMod N) → G)
        × (LayerLink N → G) => layerGaugeAction p.1 p.2) := by
  refine measurable_pi_iff.mpr fun ℓ => ?_
  show Measurable (fun p : ((Fin 4 → ZMod N) → G)
      × (LayerLink N → G) =>
    p.1 ℓ.1.1 * p.2 ℓ * (p.1 (torusShift N ℓ.1.2 ℓ.1.1))⁻¹)
  exact ((measurable_pi_apply ℓ.1.1).comp measurable_fst |>.mul
    ((measurable_pi_apply ℓ).comp measurable_snd)).mul
    (((measurable_pi_apply (torusShift N ℓ.1.2 ℓ.1.1)).comp
      measurable_fst).inv)

/-- The joint gauge action preserves the product measure:
for each fixed gauge function the action on configurations
is measure-preserving (`gaugeStratumEquiv`), and Tonelli
over the gauge group gives the joint statement. -/
theorem measurePreserving_gaugeAction_prod :
    MeasurePreserving
      (fun p : ((Fin 4 → ZMod N) → G) × (LayerLink N → G) =>
        layerGaugeAction p.1 p.2)
      ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : LayerLink N => μG))
      (Measure.pi fun _ : LayerLink N => μG) := by
  refine ⟨measurable_gaugeAction_prod, ?_⟩
  ext t ht
  rw [Measure.map_apply measurable_gaugeAction_prod ht,
    Measure.prod_apply (measurable_gaugeAction_prod ht)]
  have hset : ∀ g : (Fin 4 → ZMod N) → G,
      (Measure.pi fun _ : LayerLink N => μG)
          (Prod.mk g ⁻¹'
            ((fun p : ((Fin 4 → ZMod N) → G)
              × (LayerLink N → G) =>
              layerGaugeAction p.1 p.2) ⁻¹' t))
        = (Measure.pi fun _ : LayerLink N => μG) t := by
    intro g
    have h1 : (Prod.mk g ⁻¹'
          ((fun p : ((Fin 4 → ZMod N) → G)
            × (LayerLink N → G) =>
            layerGaugeAction p.1 p.2) ⁻¹' t))
        = ⇑(gaugeStratumEquiv
            (fun ℓ : LayerLink N => ℓ.1) g) ⁻¹' t :=
      rfl
    rw [h1, ← Measure.map_apply
      (gaugeStratumEquiv (fun ℓ : LayerLink N => ℓ.1)
        g).measurable ht,
      (measurePreserving_gaugeStratumEquiv μG
        (fun ℓ : LayerLink N => ℓ.1) g).map_eq]
  rw [lintegral_congr_ae (ae_of_all _ hset), lintegral_const,
    measure_univ, mul_one]

/-- The joint evaluation `F (γ_g u)` of an `L²` observable
along the joint gauge action is `L²` on the product space,
with the same `eLpNorm` (the action is measure-preserving
and the integrand is a composition). -/
theorem memLp_gaugeAction_prod {F : (LayerLink N → G) → ℂ}
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    MemLp (fun p : ((Fin 4 → ZMod N) → G)
        × (LayerLink N → G) => F (layerGaugeAction p.1 p.2))
      2 ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) :=
  hF.comp_measurePreserving
    (measurePreserving_gaugeAction_prod μG)

/-- The function-level layer pairing of an observable `F`
against the layer kernel: the integrand of
`LayerKernelPos`, as a product integral. -/
noncomputable def layerPairingProd (β : ℝ)
    (F : (LayerLink N → G) → ℂ) : ℂ :=
  ∫ p, star (F p.1)
      * (layerKernelFun μG ρ β p * F p.2)
    ∂((Measure.pi fun _ : LayerLink N => μG).prod
      (Measure.pi fun _ : LayerLink N => μG))

/-- Square-monotonicity in `ℝ≥0∞`, via `rpow`. -/
theorem ennreal_sq_mono {a b : ℝ≥0∞} (h : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- **The gauge average of a measurable `L²` observable is
`L²`** (with no larger `eLpNorm`): Jensen for the orbit
average, via the corpus's `ℝ≥0∞` Cauchy–Schwarz and the
measure-preservation of the joint action (Tonelli). -/
theorem gaugeAvg_memLp {F : (LayerLink N → G) → ℂ}
    (hFmeas : Measurable F)
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    MemLp (gaugeAvg μG F) 2
      (Measure.pi fun _ : LayerLink N => μG) := by
  have hΦmeas : Measurable
      (fun p : (LayerLink N → G)
        × ((Fin 4 → ZMod N) → G) =>
        F (layerGaugeAction p.2 p.1)) := by
    have h1 : Measurable
        (fun p : (LayerLink N → G)
          × ((Fin 4 → ZMod N) → G) => (p.2, p.1)) :=
      measurable_snd.prodMk measurable_fst
    exact (hFmeas.comp measurable_gaugeAction_prod).comp h1
  have hAESM : AEStronglyMeasurable (gaugeAvg μG F)
      (Measure.pi fun _ : LayerLink N => μG) :=
    hΦmeas.aestronglyMeasurable.integral_prod_right'
  have hΨ₂ : Measurable
      (fun w : ((Fin 4 → ZMod N) → G) × (LayerLink N → G) =>
        ‖F (layerGaugeAction w.1 w.2)‖ₑ ^ 2) :=
    (hFmeas.comp measurable_gaugeAction_prod).enorm.pow_const 2
  have hsec : ∀ u : LayerLink N → G, Measurable
      (fun g : (Fin 4 → ZMod N) → G =>
        ‖F (layerGaugeAction g u)‖ₑ) :=
    fun u => (hFmeas.comp (measurable_gaugeAction_prod.comp
      (measurable_id.prodMk measurable_const))).enorm
  have hA₂ : ∀ u : LayerLink N → G,
      ‖gaugeAvg μG F u‖ₑ ^ 2
        ≤ ∫⁻ g, ‖F (layerGaugeAction g u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) := by
    intro u
    have h1 : ‖gaugeAvg μG F u‖ₑ
        ≤ ∫⁻ g, ‖F (layerGaugeAction g u)‖ₑ
          ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
      enorm_integral_le_lintegral_enorm
        (fun g => F (layerGaugeAction g u))
    have hCS : (∫⁻ g, ‖F (layerGaugeAction g u)‖ₑ * 1
          ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
        ≤ (∫⁻ g, ‖F (layerGaugeAction g u)‖ₑ ^ 2
            ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
            ^ (1 / 2 : ℝ)
          * (∫⁻ _, (1 : ℝ≥0∞) ^ 2
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
            ^ (1 / 2 : ℝ) :=
      lintegral_mul_le_sqrt_mul_sqrt _ _
        (hsec u).aemeasurable measurable_const.aemeasurable
    simp only [mul_one, one_pow, lintegral_const,
      measure_univ, ENNReal.one_rpow, mul_one] at hCS
    have h2 := ennreal_sq_mono hCS
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_two,
      rpow_half_sq, ENNReal.rpow_two] at h2
    exact le_trans (ennreal_sq_mono h1) h2
  have hmap : (∫⁻ p : (LayerLink N → G)
        × ((Fin 4 → ZMod N) → G),
        ‖F (layerGaugeAction p.2 p.1)‖ₑ ^ 2
        ∂((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)))
      = ∫⁻ v, ‖F v‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    have hMP : MeasurePreserving
        (fun p : (LayerLink N → G)
          × ((Fin 4 → ZMod N) → G) =>
          layerGaugeAction p.2 p.1)
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
        (Measure.pi fun _ : LayerLink N => μG) :=
      (measurePreserving_gaugeAction_prod μG).comp
        MeasureTheory.Measure.measurePreserving_swap
    have h2 := MeasureTheory.lintegral_map
      (μ := (Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
      (f := fun v => ‖F v‖ₑ ^ 2)
      (hFmeas.enorm.pow_const 2) hMP.measurable
    rw [hMP.map_eq] at h2
    exact h2.symm
  have hIntB : (∫⁻ u, ‖gaugeAvg μG F u‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG))
      ≤ ∫⁻ v, ‖F v‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    refine le_trans (lintegral_mono fun u => hA₂ u) ?_
    rw [← hmap]
    exact (MeasureTheory.lintegral_prod _
      (hΨ₂.comp measurable_swap).aemeasurable).symm.le
  show eLpNorm _ 2 _ < ∞
  have hsq : (eLpNorm (gaugeAvg μG F) 2
      (Measure.pi fun _ : LayerLink N => μG)) ^ 2
      = ∫⁻ u, ‖gaugeAvg μG F u‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG) :=
    eLpNorm_two_sq _ hAESM
  have hsqF : (eLpNorm F 2
      (Measure.pi fun _ : LayerLink N => μG)) ^ 2
      = ∫⁻ v, ‖F v‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG) :=
    eLpNorm_two_sq _ hF.aestronglyMeasurable
  have hlt : (∫⁻ v, ‖F v‖ₑ ^ 2
      ∂(Measure.pi fun _ : LayerLink N => μG)) < ∞ := by
    rw [← hsqF]
    exact ENNReal.pow_lt_top hF.eLpNorm_lt_top
  have hne : eLpNorm (gaugeAvg μG F) 2
      (Measure.pi fun _ : LayerLink N => μG) ≠ ∞ := by
    intro htop
    have htop2 : (∫⁻ u, ‖gaugeAvg μG F u‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG)) = ∞ := by
      rw [← hsq, htop]
      exact ENNReal.top_pow (by norm_num)
    have hFeq : (∫⁻ v, ‖F v‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG)) = ∞ :=
      le_antisymm le_top (htop2 ▸ hIntB)
    exact hlt.ne hFeq
  exact lt_top_iff_ne_top.mpr hne

/-- **The pairing is gauge-invariant at the function
level**: substituting independent gauge actions in the two
slots does not change the pairing integral — the
substitution is measure-preserving on the product and the
kernel is separately invariant (BRIDGE-SEP). -/
theorem pairing_gauge_integral (hN : Even N) (β : ℝ)
    (F : (LayerLink N → G) → ℂ)
    (g g' : (Fin 4 → ZMod N) → G) :
    (∫ p, star (F (layerGaugeAction g p.1))
        * (layerKernelFun μG ρ β p
          * F (layerGaugeAction g' p.2))
      ∂((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)))
      = ∫ p, star (F p.1)
        * (layerKernelFun μG ρ β p * F p.2)
        ∂((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)) := by
  have h := ((measurePreserving_gaugeStratumEquiv μG
      (fun ℓ : LayerLink N => ℓ.1) g).prod
    (measurePreserving_gaugeStratumEquiv μG
      (fun ℓ : LayerLink N => ℓ.1) g')).integral_comp
    ((gaugeStratumEquiv (fun ℓ : LayerLink N => ℓ.1)
      g).prodCongr
      (gaugeStratumEquiv (fun ℓ : LayerLink N => ℓ.1)
        g')).measurableEmbedding
    (fun p => star (F p.1)
      * (layerKernelFun μG ρ β p * F p.2))
  refine (integral_congr_ae (Filter.Eventually.of_forall
    fun p => ?_)).trans h
  show star (F (layerGaugeAction g p.1))
      * (layerKernelFun μG ρ β p
        * F (layerGaugeAction g' p.2))
    = star (F (layerGaugeAction g p.1))
      * (layerKernelFun μG ρ β
          (layerGaugeAction g p.1, layerGaugeAction g' p.2)
        * F (layerGaugeAction g' p.2))
  congr 2
  exact (layerKernel_gauge_invariant μG ρ hN β g g'
    p.1 p.2).symm

set_option maxHeartbeats 800000 in
/-- **The two-slot gauge-orbit tensor factor is `L²` on
the four-fold product**: its squared `eLpNorm` is the
fourth power of `‖F‖₂` — Tonelli twice, the separated
products split, and the joint action is
measure-preserving. This is the four-fold analogue of the
corpus's tensor estimate, with the gauge action in place
of the bare slot projections. -/
theorem memLp_gaugeTensor {F : (LayerLink N → G) → ℂ}
    (hFmeas : Measurable F)
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    MemLp (fun z : (((Fin 4 → ZMod N) → G)
          × ((Fin 4 → ZMod N) → G))
        × ((LayerLink N → G) × (LayerLink N → G)) =>
      star (F (layerGaugeAction z.1.1 z.2.1))
        * F (layerGaugeAction z.1.2 z.2.2))
      2 (((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG))) := by
  have hΨ₂ : Measurable
      (fun w : ((Fin 4 → ZMod N) → G) × (LayerLink N → G) =>
        ‖F (layerGaugeAction w.1 w.2)‖ₑ ^ 2) :=
    (hFmeas.comp measurable_gaugeAction_prod).enorm.pow_const 2
  have hAesm : AEStronglyMeasurable
      (fun z : (((Fin 4 → ZMod N) → G)
          × ((Fin 4 → ZMod N) → G))
        × ((LayerLink N → G) × (LayerLink N → G)) =>
      star (F (layerGaugeAction z.1.1 z.2.1))
        * F (layerGaugeAction z.1.2 z.2.2))
      (((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG))) := by
    have hf1 : Measurable
        (fun z : (((Fin 4 → ZMod N) → G)
            × ((Fin 4 → ZMod N) → G))
          × ((LayerLink N → G) × (LayerLink N → G)) =>
          F (layerGaugeAction z.1.1 z.2.1)) :=
      hFmeas.comp (measurable_gaugeAction_prod.comp
        ((measurable_fst.fst).prodMk (measurable_snd.fst)))
    have hf2 : Measurable
        (fun z : (((Fin 4 → ZMod N) → G)
            × ((Fin 4 → ZMod N) → G))
          × ((LayerLink N → G) × (LayerLink N → G)) =>
          F (layerGaugeAction z.1.2 z.2.2)) :=
      hFmeas.comp (measurable_gaugeAction_prod.comp
        ((measurable_fst.snd).prodMk (measurable_snd.snd)))
    exact ((continuous_star.measurable.comp hf1).mul hf2).aestronglyMeasurable
  have hB₂ : AEMeasurable
      (fun g : (Fin 4 → ZMod N) → G =>
        ∫⁻ u, ‖F (layerGaugeAction g u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG))
      (Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
    hΨ₂.aemeasurable.lintegral_prod_right'
  have hBval : (∫⁻ g, ∫⁻ u,
        ‖F (layerGaugeAction g u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
      = ∫⁻ v, ‖F v‖ₑ ^ 2
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    rw [← MeasureTheory.lintegral_prod _
      hΨ₂.aemeasurable]
    have h1 := MeasureTheory.lintegral_map
      (μ := (Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : LayerLink N => μG))
      (f := fun v => ‖F v‖ₑ ^ 2)
      (hFmeas.enorm.pow_const 2) measurable_gaugeAction_prod
    rw [(measurePreserving_gaugeAction_prod μG).map_eq]
      at h1
    exact h1.symm
  have hsepL : ∀ q : ((Fin 4 → ZMod N) → G)
      × ((Fin 4 → ZMod N) → G),
      (∫⁻ p, ‖F (layerGaugeAction q.1 p.1)‖ₑ ^ 2
          * ‖F (layerGaugeAction q.2 p.2)‖ₑ ^ 2
        ∂((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)))
      = (∫⁻ u, ‖F (layerGaugeAction q.1 u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG))
        * (∫⁻ u, ‖F (layerGaugeAction q.2 u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG)) := by
    intro q
    have ha : Measurable (fun u : LayerLink N → G =>
        ‖F (layerGaugeAction q.1 u)‖ₑ ^ 2) :=
      (hFmeas.enorm.pow_const 2).comp
        (gaugeStratumEquiv (fun ℓ : LayerLink N => ℓ.1)
          q.1).measurable
    have hb : Measurable (fun u : LayerLink N → G =>
        ‖F (layerGaugeAction q.2 u)‖ₑ ^ 2) :=
      (hFmeas.enorm.pow_const 2).comp
        (gaugeStratumEquiv (fun ℓ : LayerLink N => ℓ.1)
          q.2).measurable
    have hprod : AEMeasurable
        (fun p : (LayerLink N → G) × (LayerLink N → G) =>
          ‖F (layerGaugeAction q.1 p.1)‖ₑ ^ 2
            * ‖F (layerGaugeAction q.2 p.2)‖ₑ ^ 2)
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)) :=
      ((ha.comp measurable_fst).mul
        (hb.comp measurable_snd)).aemeasurable
    rw [MeasureTheory.lintegral_prod _ hprod]
    dsimp only
    rw [lintegral_congr (fun u => lintegral_const_mul'' _
      hb.aemeasurable)]
    rw [lintegral_congr (fun u => mul_comm _ _),
      lintegral_const_mul'' _ ha.aemeasurable, mul_comm]
  have houter : (∫⁻ q, (∫⁻ u,
        ‖F (layerGaugeAction q.1 u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG))
        * (∫⁻ u, ‖F (layerGaugeAction q.2 u)‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG))
      ∂((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)))
      = (∫⁻ v, ‖F v‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG)) ^ 2 := by
    have step : (∫⁻ q, (∫⁻ u,
          ‖F (layerGaugeAction q.1 u)‖ₑ ^ 2
            ∂(Measure.pi fun _ : LayerLink N => μG))
          * (∫⁻ u, ‖F (layerGaugeAction q.2 u)‖ₑ ^ 2
            ∂(Measure.pi fun _ : LayerLink N => μG))
        ∂((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)))
        = ∫⁻ g, ∫⁻ g', (∫⁻ u,
            ‖F (layerGaugeAction g u)‖ₑ ^ 2
              ∂(Measure.pi fun _ : LayerLink N => μG))
          * (∫⁻ u, ‖F (layerGaugeAction g' u)‖ₑ ^ 2
              ∂(Measure.pi fun _ : LayerLink N => μG))
          ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG)
          ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
      MeasureTheory.lintegral_prod _
        ((hB₂.comp_fst).mul (hB₂.comp_snd))
    rw [step, lintegral_congr (fun g =>
      lintegral_const_mul'' _ hB₂),
      lintegral_congr (fun g => mul_comm _ _),
      lintegral_const_mul'' _ hB₂, ← hBval, pow_two]
  have hnorm : (∫⁻ z, ‖star (F (layerGaugeAction z.1.1 z.2.1))
          * F (layerGaugeAction z.1.2 z.2.2)‖ₑ ^ 2
        ∂(((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
          ((Measure.pi fun _ : LayerLink N => μG).prod
            (Measure.pi fun _ : LayerLink N => μG))))
      = (∫⁻ v, ‖F v‖ₑ ^ 2
          ∂(Measure.pi fun _ : LayerLink N => μG)) ^ 2 := by
    rw [lintegral_congr (fun z => by
      have hstar : ‖star (F (layerGaugeAction z.1.1 z.2.1))‖ₑ
          = ‖F (layerGaugeAction z.1.1 z.2.1)‖ₑ := by
        simp [enorm]
      rw [enorm_mul, hstar, mul_pow])]
    have hprodA : AEMeasurable
        (fun z : (((Fin 4 → ZMod N) → G)
            × ((Fin 4 → ZMod N) → G))
          × ((LayerLink N → G) × (LayerLink N → G)) =>
          ‖F (layerGaugeAction z.1.1 z.2.1)‖ₑ ^ 2
            * ‖F (layerGaugeAction z.1.2 z.2.2)‖ₑ ^ 2)
        (((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
          ((Measure.pi fun _ : LayerLink N => μG).prod
            (Measure.pi fun _ : LayerLink N => μG))) :=
      ((hΨ₂.comp ((measurable_fst.fst).prodMk
          (measurable_snd.fst))).mul
        (hΨ₂.comp ((measurable_fst.snd).prodMk
          (measurable_snd.snd)))).aemeasurable
    rw [MeasureTheory.lintegral_prod _ hprodA]
    rw [lintegral_congr hsepL]
    exact houter
  show eLpNorm _ 2 _ < ∞
  by_contra htop
  push Not at htop
  have hEq : eLpNorm _ 2 _ = ∞ := le_antisymm le_top htop
  have hInf : (∫⁻ z, ‖star (F (layerGaugeAction z.1.1 z.2.1))
        * F (layerGaugeAction z.1.2 z.2.2)‖ₑ ^ 2
      ∂(((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)))) = ∞ := by
    rw [← eLpNorm_two_sq _ hAesm, hEq]
    exact ENNReal.top_pow (by norm_num)
  rw [hInf] at hnorm
  have hfin : (∫⁻ v, ‖F v‖ₑ ^ 2
      ∂(Measure.pi fun _ : LayerLink N => μG)) ≠ ∞ := by
    rw [← eLpNorm_two_sq _ hF.aestronglyMeasurable]
    exact ENNReal.pow_ne_top hF.eLpNorm_lt_top.ne
  exact ENNReal.pow_ne_top hfin hnorm.symm

set_option maxHeartbeats 800000 in
/-- **MASTER IDENTITY (PB-3 core)**: the layer pairing of
`F` equals the layer pairing of its gauge average —
average the (constant) pairing over the gauge group,
substitute (BRIDGE-SEP), swap (Fubini), and separate the
double average into the two gauge averages. -/
theorem layerPairingProd_gaugeAvg (hN : Even N) (β : ℝ)
    (hK : MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)))
    {F : (LayerLink N → G) → ℂ} (hFmeas : Measurable F)
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    layerPairingProd μG ρ β F
      = layerPairingProd μG ρ β (gaugeAvg μG F) := by
  have hB : MemLp (fun z : (((Fin 4 → ZMod N) → G)
        × ((Fin 4 → ZMod N) → G))
      × ((LayerLink N → G) × (LayerLink N → G)) =>
    layerKernelFun μG ρ β z.2)
    2 (((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG))) :=
    hK.comp_measurePreserving MeasureTheory.measurePreserving_snd
  have hIntΘ : Integrable
      (fun z : (((Fin 4 → ZMod N) → G)
          × ((Fin 4 → ZMod N) → G))
        × ((LayerLink N → G) × (LayerLink N → G)) =>
      star (F (layerGaugeAction z.1.1 z.2.1))
        * (layerKernelFun μG ρ β z.2
          * F (layerGaugeAction z.1.2 z.2.2)))
      (((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG))) := by
    have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
      ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
    have h1 : Integrable
        (fun z : (((Fin 4 → ZMod N) → G)
            × ((Fin 4 → ZMod N) → G))
          × ((LayerLink N → G) × (LayerLink N → G)) =>
        layerKernelFun μG ρ β z.2
          * (star (F (layerGaugeAction z.1.1 z.2.1))
            * F (layerGaugeAction z.1.2 z.2.2)))
        (((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
          ((Measure.pi fun _ : LayerLink N => μG).prod
            (Measure.pi fun _ : LayerLink N => μG))) :=
      memLp_one_iff_integrable.mp
        (hB.mul (memLp_gaugeTensor μG hFmeas hF))
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hIntΘ' : Integrable
      (Function.uncurry
        fun (p : (LayerLink N → G) × (LayerLink N → G))
          (q : ((Fin 4 → ZMod N) → G)
            × ((Fin 4 → ZMod N) → G)) =>
        star (F (layerGaugeAction q.1 p.1))
          * (layerKernelFun μG ρ β p
            * F (layerGaugeAction q.2 p.2)))
      (((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)).prod
        ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG))) :=
    hIntΘ.swap
  have hprob : (∫ _ : ((Fin 4 → ZMod N) → G)
        × ((Fin 4 → ZMod N) → G), layerPairingProd μG ρ β F
      ∂((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
        (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)))
      = layerPairingProd μG ρ β F := by
    simp [integral_const]
  calc layerPairingProd μG ρ β F
      = ∫ q, layerPairingProd μG ρ β F
        ∂((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
        hprob.symm
    _ = ∫ q, ∫ p, star (F (layerGaugeAction q.1 p.1))
          * (layerKernelFun μG ρ β p
            * F (layerGaugeAction q.2 p.2))
          ∂((Measure.pi fun _ : LayerLink N => μG).prod
            (Measure.pi fun _ : LayerLink N => μG))
        ∂((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
          (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) :=
        integral_congr_ae (Filter.Eventually.of_forall
          fun q => (pairing_gauge_integral μG ρ hN β F
            q.1 q.2).symm)
    _ = ∫ z, star (F (layerGaugeAction z.1.1 z.2.1))
          * (layerKernelFun μG ρ β z.2
            * F (layerGaugeAction z.1.2 z.2.2))
          ∂(((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
              (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)).prod
            ((Measure.pi fun _ : LayerLink N => μG).prod
              (Measure.pi fun _ : LayerLink N => μG))) :=
        MeasureTheory.integral_integral hIntΘ
    _ = ∫ z, star (F (layerGaugeAction z.2.1 z.1.1))
          * (layerKernelFun μG ρ β z.1
            * F (layerGaugeAction z.2.2 z.1.2))
          ∂(((Measure.pi fun _ : LayerLink N => μG).prod
              (Measure.pi fun _ : LayerLink N => μG)).prod
            ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
              (Measure.pi fun _ : (Fin 4 → ZMod N) => μG))) :=
        (MeasureTheory.Measure.measurePreserving_swap.integral_comp
          MeasurableEquiv.prodComm.measurableEmbedding
          (fun z : (((Fin 4 → ZMod N) → G)
              × ((Fin 4 → ZMod N) → G))
            × ((LayerLink N → G) × (LayerLink N → G)) =>
            star (F (layerGaugeAction z.1.1 z.2.1))
            * (layerKernelFun μG ρ β z.2
              * F (layerGaugeAction z.1.2 z.2.2)))).symm
    _ = ∫ p, ∫ q, star (F (layerGaugeAction q.1 p.1))
          * (layerKernelFun μG ρ β p
            * F (layerGaugeAction q.2 p.2))
          ∂((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
            (Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
        ∂((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)) :=
        (MeasureTheory.integral_integral hIntΘ').symm
    _ = ∫ p, star (gaugeAvg μG F p.1)
          * (layerKernelFun μG ρ β p * gaugeAvg μG F p.2)
          ∂((Measure.pi fun _ : LayerLink N => μG).prod
            (Measure.pi fun _ : LayerLink N => μG)) := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.Integrable.prod_right_ae
          hIntΘ'] with p hp
        have hp' : Integrable
            (fun q => star (F (layerGaugeAction q.1 p.1))
              * (layerKernelFun μG ρ β p
                * F (layerGaugeAction q.2 p.2)))
            ((Measure.pi fun _ : (Fin 4 → ZMod N) => μG).prod
              (Measure.pi fun _ : (Fin 4 → ZMod N) => μG)) := hp
        rw [MeasureTheory.integral_prod _ hp']
        have step1 : ∀ g : (Fin 4 → ZMod N) → G,
            (∫ g', star (F (layerGaugeAction g p.1))
                * (layerKernelFun μG ρ β p
                  * F (layerGaugeAction g' p.2))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
            = star (F (layerGaugeAction g p.1))
              * (layerKernelFun μG ρ β p
                * gaugeAvg μG F p.2) := by
          intro g
          have hcong : (∫ g', star (F (layerGaugeAction g p.1))
                * (layerKernelFun μG ρ β p
                  * F (layerGaugeAction g' p.2))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
              = ∫ g', (star (F (layerGaugeAction g p.1))
                  * layerKernelFun μG ρ β p)
                * F (layerGaugeAction g' p.2)
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG) :=
            integral_congr_ae (Filter.Eventually.of_forall
              fun g' => by ring)
          rw [hcong, integral_const_mul]
          show (star (F (layerGaugeAction g p.1))
              * layerKernelFun μG ρ β p) * gaugeAvg μG F p.2
            = star (F (layerGaugeAction g p.1))
              * (layerKernelFun μG ρ β p
                * gaugeAvg μG F p.2)
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall
          step1), integral_mul_const]
        have hstar_int : (∫ g, star (F (layerGaugeAction g p.1))
              ∂(Measure.pi fun _ : (Fin 4 → ZMod N) => μG))
            = star (gaugeAvg μG F p.1) :=
          integral_conj
        rw [hstar_int]
    _ = layerPairingProd μG ρ β (gaugeAvg μG F) := rfl

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **The pairing depends only on the `L²` class**: a.e.-equal
observables have the same layer pairing. The a.e. equality
transports to the product through the two coordinate
projections, which are measure-preserving. -/
theorem layerPairingProd_congr_ae (β : ℝ)
    {F F' : (LayerLink N → G) → ℂ}
    (hae : F =ᵐ[Measure.pi fun _ : LayerLink N => μG] F') :
    layerPairingProd μG ρ β F
      = layerPairingProd μG ρ β F' := by
  have hae1 : (fun p : (LayerLink N → G) × (LayerLink N → G)
        => F p.1)
      =ᵐ[(Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)]
        (fun p => F' p.1) :=
    MeasureTheory.measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually
      hae
  have hae2 : (fun p : (LayerLink N → G) × (LayerLink N → G)
        => F p.2)
      =ᵐ[(Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)]
        (fun p => F' p.2) :=
    MeasureTheory.measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually
      hae
  unfold layerPairingProd
  apply integral_congr_ae
  filter_upwards [hae1, hae2] with p hp1 hp2
  rw [hp1, hp2]

omit [Group G] [MeasurableInv G] [IsTopologicalGroup G]
  [BorelSpace G] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- **Tensor factors are `L²` on the product space** (the
plain-function form of the corpus's `memLp_tensor_gen`,
obtained from it through the class transport above). -/
theorem memLp_tensorFun {F : (LayerLink N → G) → ℂ}
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    MemLp (fun p : (LayerLink N → G) × (LayerLink N → G) =>
        star (F p.1) * F p.2) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
  have hT := memLp_tensor_gen (hF.toLp F) (hF.toLp F)
  have hae := MemLp.coeFn_toLp hF
  have hae1 : (fun p : (LayerLink N → G) × (LayerLink N → G)
        => (⇑(hF.toLp F)) p.1)
      =ᵐ[(Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)]
        (fun p => F p.1) :=
    MeasureTheory.measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually
      hae
  have hae2 : (fun p : (LayerLink N → G) × (LayerLink N → G)
        => (⇑(hF.toLp F)) p.2)
      =ᵐ[(Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)]
        (fun p => F p.2) :=
    MeasureTheory.measurePreserving_snd.quasiMeasurePreserving.tendsto_ae.eventually
      hae
  have haeT : (fun p : (LayerLink N → G) × (LayerLink N → G) =>
        star (⇑(hF.toLp F) p.1) * ⇑(hF.toLp F) p.2)
      =ᵐ[(Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)]
        (fun p => star (F p.1) * F p.2) := by
    filter_upwards [hae1, hae2] with p hp1 hp2
    rw [hp1, hp2]
  show eLpNorm (fun p : (LayerLink N → G) × (LayerLink N → G) =>
      star (F p.1) * F p.2) 2
    ((Measure.pi fun _ : LayerLink N => μG).prod
      (Measure.pi fun _ : LayerLink N => μG)) < ∞
  rw [← eLpNorm_congr_ae haeT]
  exact hT

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- **The product pairing is the iterated pairing**: the
function-level layer pairing (product form) equals the
corpus's `layerPairing` (the iterated form registered by
`LayerKernelPos`), by Fubini (`integral_prod`) and the
Hölder integrability of the pairing integrand. -/
theorem layerPairingProd_eq_layerPairing
    (hK : MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)))
    {F : (LayerLink N → G) → ℂ}
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    layerPairingProd μG ρ β F = layerPairing μG ρ β F := by
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hInt : Integrable
      (fun p : (LayerLink N → G) × (LayerLink N → G) =>
        star (F p.1) * (layerKernelFun μG ρ β p * F p.2))
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
    have h1 : Integrable
        ((layerKernelFun μG ρ β)
          * (fun p : (LayerLink N → G) × (LayerLink N → G) =>
            star (F p.1) * F p.2))
        ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)) :=
      memLp_one_iff_integrable.mp
        (hK.mul (memLp_tensorFun μG hF))
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  unfold layerPairingProd layerPairing
  rw [MeasureTheory.integral_prod _ hInt]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun u => ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun u' => ?_
  show star (F u) * (layerKernel μG ρ β u u' * F u')
    = (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
  rw [starRingEnd_apply]
  ring

/-- **PB-2, the form identity**: the layer operator's
quadratic form at an observable equals its quadratic form
at the observable's gauge average — the pairing of `F`
equals the pairing of `gaugeAvg F` (master identity),
transported to the operator through
`integralKernelOp_inner` and the class transport. -/
theorem layerKernelOp_inner_gaugeAvg
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) {F : (LayerLink N → G) → ℂ}
    (hFmeas : Measurable F)
    (hF : MemLp F 2 (Measure.pi fun _ : LayerLink N => μG)) :
    ⟪hF.toLp F, integralKernelOp
        (layerKernelFun_memLp μG ρ hρcont β) (hF.toLp F)⟫
      = ⟪(gaugeAvg_memLp μG hFmeas hF).toLp (gaugeAvg μG F),
          integralKernelOp
            (layerKernelFun_memLp μG ρ hρcont β)
            ((gaugeAvg_memLp μG hFmeas hF).toLp
              (gaugeAvg μG F))⟫ := by
  have hK : MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) :=
    layerKernelFun_memLp μG ρ hρcont β
  have hlhs : ⟪hF.toLp F, integralKernelOp
        (layerKernelFun_memLp μG ρ hρcont β) (hF.toLp F)⟫
      = layerPairingProd μG ρ β (gaugeAvg μG F) :=
    (integralKernelOp_inner hK (hF.toLp F) (hF.toLp F)).trans
      ((layerPairingProd_congr_ae μG ρ β
        (MemLp.coeFn_toLp hF)).trans
        (layerPairingProd_gaugeAvg μG ρ hN β hK hFmeas hF))
  have hrhs : ⟪(gaugeAvg_memLp μG hFmeas hF).toLp
        (gaugeAvg μG F),
        integralKernelOp
          (layerKernelFun_memLp μG ρ hρcont β)
          ((gaugeAvg_memLp μG hFmeas hF).toLp
            (gaugeAvg μG F))⟫
      = layerPairingProd μG ρ β (gaugeAvg μG F) :=
    (integralKernelOp_inner hK _ _).trans
      (layerPairingProd_congr_ae μG ρ β
        (MemLp.coeFn_toLp (gaugeAvg_memLp μG hFmeas hF)))
  rw [hlhs, hrhs]

/-- **BRIDGE-MAIN (PB-1 + PB-2 + PB-3)**: positivity of the
layer pairing on gauge-invariant observables implies
positivity of the layer-kernel operator on ALL of
`L²(layer)` — `LayerKernelPos` (under `hρcont`) implies
`LayerKernelPosAll`. The bridge is this implication only:
`LayerKernelPos` itself stays open. Route: the operator
pairing of `f` is the function-level pairing of any
measurable representative; the master identity replaces it
by its gauge average; the gauge average is exactly
gauge-invariant, so `LayerKernelPos` applies. -/
theorem layerKernelPosAll_of_layerKernelPos
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hPos : LayerKernelPos (N := N) μG ρ β) :
    LayerKernelPosAll (N := N) μG ρ hρcont β := by
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
    layerKernelFun_memLp μG ρ hρcont β
  have e1 : ⟪f, integralKernelOp
        (layerKernelFun_memLp μG ρ hρcont β) f⟫
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

/-- **BRIDGE-COR**: item 5's conditional headline fires at
the frozen generality — `SeatFactorApproxExpansion` under
`LayerKernelPos` + `hρcont` alone (the bridge discharges
the `LayerKernelPosAll` hypothesis of
`seatFactorApproxExpansion_of_layerKernelPosAll`). -/
theorem seatFactorApproxExpansion_of_layerKernelPos
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) {β : ℝ}
    (hPos : LayerKernelPos (N := N) μG ρ β) :
    SeatFactorApproxExpansion μG ρ hN β :=
  seatFactorApproxExpansion_of_layerKernelPosAll μG ρ hρcont
    hN (layerKernelPosAll_of_layerKernelPos μG ρ hρcont hN β
      hPos)

/-- **BRIDGE-COR, frozen form**: the frozen GATE-0 item-5
headline `pullBotKernel_seatFactorApproxExpansion` holds
under `hρcont` — at every `Even N` and every `β ≥ 0`,
`LayerKernelPos` implies the approximating expansion. -/
theorem pullBotKernel_seatFactorApproxExpansion_of_cont
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    pullBotKernel_seatFactorApproxExpansion (N := N) μG ρ :=
  fun hN _β _hβ hPos =>
    seatFactorApproxExpansion_of_layerKernelPos μG ρ hρcont
      hN hPos

end PosBridge

end ThetLogos
