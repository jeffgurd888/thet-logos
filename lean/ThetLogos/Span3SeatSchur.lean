/-
# F2-W2: the F2 weld line's SEAT SCHUR (working label)

Brick F2-W2 of the F2 weld line, per the governing scoping
memo `routeb-general-scratch/scoping-f2-weld-2026-10-31.md`
(read in full; esp. section 1 inventory, section 4 the seat
Schur and the engine, section 5 W2 spec and kills, section 6
retirements) and pack
`routeb-general-scratch/pack-f2-w2.md`.

**Target.** The landed pin's `SeatSchurTarget`
(`ThetLogos.Span3A0AssemblyPost`, at HEAD), in its exact
registered form. This module discharges it only through the
stages below; it never restates the target into a different
statement.

**NO CLAIM** - parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. The weld ASSUMES
`LayerKernelPos`; it does not prove it. No Gram
factorization of the layer kernel itself appears anywhere
in this module: every use of `LayerKernelPos` below is a
use of the hypothesis, never a re-derivation.

## Stages (memo section 4)

1. The `layerKernel` uniform bound (this stage): the layer
   kernel is an average over a probability measure of the
   exponential of a finite sum of uniformly bounded
   plaquette terms, hence is uniformly bounded by
   `Real.exp (|beta| * C (N))` for an explicit finite
   constant `C (N)` (the layer plaquette count, with the
   crude per-site factor `8 = 4 * 2`: four directions, each
   density bounded by `2` in absolute value).
2. The pullback-pairing reduction: the crossing marginal
   is the pointwise product of the two pullbacks of the
   layer kernel (beta-1, landed); each pullback pairing,
   in iterated-integral form, is exactly a layer-kernel
   pairing of a gauge-invariant layer observable, hence is
   nonnegative under the assumed `LayerKernelPos`; and the
   averaged-kernel pairing folds its two positive
   half-action weights into the observables, reducing it
   to the marginal pairing of the folded observables.
3. The product step: the pointwise product of the two
   pullback pairings is concluded from the factor
   pairings. The finite-rank algebraic core of this step
   is landed below as a conditional lemma: IF the second
   pullback kernel admits a finite expansion into
   separated factors with nonnegative real coefficients
   whose induced factor pairings are nonnegative, THEN
   the product pairing is nonnegative. Producing such an
   expansion (spectral or positivity-preserving
   finite-rank approximation of the second pullback, with
   the limit passage controlled by the stage-1 bound) is
   the pre-named OPEN remainder of this brick, named on
   the face here and in `seatSchurProductStepOpen` below:
   this module lands PARTIAL at the product step, and
   F2-W3 does not fire on it.

Armed kills, kept on the face: K-F2-2 (invariance
confinement) does NOT fire in the stages landed here: the
pullback reductions of stage 2 consume `LayerKernelPos`
only on gauge-invariant layer observables, exactly as
registered. K-F2-3: no finite-seat retreat and no abstract
positive-kernel restatement appears here; the seat
hypotheses stay on the face of every statement.

This module is NOT in the root import list of the library;
it is verified by a targeted build.
-/

import ThetLogos.Span3A0AssemblyPost

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchur

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## Stage 1: the `layerKernel` uniform bound -/

/-- **Stage 1, density bound.** Every plaquette density is
bounded by `2` in absolute value, at every `d` (for
`0 < d` this is the landed `plaquetteDensity_mem_Icc`;
for `d = 0` the density is definitionally `1`). -/
theorem abs_plaquetteDensity_le_two (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    |plaquetteDensity (torusShift N) ρ U x μ ν| ≤ 2 := by
  by_cases hd : d = 0
  · subst hd
    simp [plaquetteDensity]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have h := Set.mem_Icc.mp
      (plaquetteDensity_mem_Icc (torusShift N) ρ hdpos U x μ ν)
    rw [abs_le]
    constructor <;> linarith

/-- **Stage 1, the bound constant.** The explicit finite
constant of the layer-kernel bound: `8` per layer site
(four directions times the density bound `2`), times the
number of layer sites. This is the memo's `C (N, d)`
slot; the bound proved below is in fact independent of
`d`. -/
def layerBoundConst (N : ℕ) [NeZero N] : ℝ :=
  8 * (Fintype.card (LayerSite N) : ℝ)

theorem layerBoundConst_nonneg : 0 ≤ layerBoundConst N := by
  unfold layerBoundConst
  exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- **Stage 1, action bound.** The one-layer action is
bounded by `|beta|` times the bound constant: it is
`beta` times a finite sum (over layer sites and the
three spatial directions above `0`, crudely enlarged to
all four directions) of plaquette densities each bounded
by `2` in absolute value. -/
theorem layerAction_abs_le (β : ℝ) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    |layerAction ρ β α u u'| ≤ |β| * layerBoundConst N := by
  unfold layerAction layerBoundConst
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  calc |∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
          plaquetteDensity (torusShift N) ρ (layerConfig α u u')
            c.1 0 ν|
      ≤ ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
          |plaquetteDensity (torusShift N) ρ (layerConfig α u u')
            c.1 0 ν| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun c _ =>
            Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4), (2 : ℝ) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum
          fun ν _ => abs_plaquetteDensity_le_two ρ _ _ _ _
    _ ≤ ∑ c : LayerSite N, ∑ _ν : Fin 4, (2 : ℝ) :=
        Finset.sum_le_sum fun c _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by norm_num)
    _ = 8 * (Fintype.card (LayerSite N) : ℝ) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_fin,
          nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
        ring

/-- **Stage 1, the `layerKernel` uniform bound (headline
of this stage).** The layer kernel is uniformly pointwise
bounded by `Real.exp (|beta| * C (N))`: it is the average
over the stratum probability measure of the exponential
of the one-layer action, whose absolute value is at most
`|beta| * C (N)` by `layerAction_abs_le`. No bound of
this form was landed before this brick. -/
theorem layerKernel_norm_le (β : ℝ) (u u' : LayerLink N → G) :
    ‖layerKernel μG ρ β u u'‖
      ≤ Real.exp (|β| * layerBoundConst N) := by
  unfold layerKernel
  refine (norm_integral_le_of_norm_le_const
    (C := Real.exp (|β| * layerBoundConst N))
    (ae_of_all _ fun α => ?_)).trans (by simp)
  have h1 : ‖(Real.exp (-(layerAction ρ β α u u')) : ℂ)‖
      = Real.exp (-(layerAction ρ β α u u')) :=
    (RCLike.norm_ofReal _).trans (Real.abs_exp _)
  rw [h1]
  exact Real.exp_le_exp.mpr
    ((neg_le_abs _).trans (layerAction_abs_le ρ β α u u'))

/-- **Stage 1, real form.** The layer kernel is the cast
of a real integral (the average of a real Boltzmann
factor); in particular its real part is that integral and
its imaginary part is `0`. -/
theorem layerKernel_eq_ofReal (β : ℝ) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((∫ α : LayerSite N → G,
          Real.exp (-(layerAction ρ β α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
  unfold layerKernel
  exact integral_ofReal

/-! ## Stage 2: the pullback-pairing reduction -/

/-- **Stage 2, the top extraction as a link map.** The top
extraction `tauTop` is composition with this injective map
of layer links into strict-half links. -/
def embLayerTop (hN : Even N) (ℓ : LayerLink N) :
    ↥(posLinks (N := N)) :=
  ⟨(topSite ⟨ℓ.1.1, ℓ.2.1⟩, ℓ.1.2),
    mem_posLinks_top hN (topSite_val _) ℓ.2.2⟩

/-- **Stage 2, the bottom extraction as a link map.** The
bottom extraction `tauBot` is composition with this
injective map of layer links into strict-half links. -/
def embLayerBot (hN : Even N) (ℓ : LayerLink N) :
    ↥(posLinks (N := N)) :=
  ⟨ℓ.1, layerLink_mem_posLinks hN ℓ⟩

theorem tauTop_eq_comp (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) :
    tauTop hN z = z ∘ embLayerTop hN := rfl

theorem tauBot_eq_comp (hN : Even N)
    (z : ↥(posLinks (N := N)) → G) :
    tauBot hN z = z ∘ embLayerBot hN := rfl

theorem embLayerBot_injective (hN : Even N) :
    Function.Injective (embLayerBot hN) := by
  intro ℓ ℓ' h
  apply Subtype.ext
  exact congrArg (fun m : ↥(posLinks (N := N)) => m.1) h

theorem embLayerTop_injective (hN : Even N) :
    Function.Injective (embLayerTop hN) := by
  intro ℓ ℓ' h
  have hv := congrArg (fun m : ↥(posLinks (N := N)) => m.1) h
  have hv2 : (topSite (⟨ℓ.1.1, ℓ.2.1⟩ : LayerSite N), ℓ.1.2)
      = (topSite (⟨ℓ'.1.1, ℓ'.2.1⟩ : LayerSite N), ℓ'.1.2) := hv
  have h1 : topSite (⟨ℓ.1.1, ℓ.2.1⟩ : LayerSite N)
      = topSite (⟨ℓ'.1.1, ℓ'.2.1⟩ : LayerSite N) :=
    (Prod.ext_iff.mp hv2).1
  have hsite : (⟨ℓ.1.1, ℓ.2.1⟩ : LayerSite N)
      = ⟨ℓ'.1.1, ℓ'.2.1⟩ := by
    have e1 := topPreimage_topSite (⟨ℓ.1.1, ℓ.2.1⟩ : LayerSite N)
    have e2 := topPreimage_topSite (⟨ℓ'.1.1, ℓ'.2.1⟩ : LayerSite N)
    rw [← e1, ← e2, h1]
  have hdir : ℓ.1.2 = ℓ'.1.2 := (Prod.ext_iff.mp hv2).2
  apply Subtype.ext
  exact Prod.ext (congrArg (fun c : LayerSite N => c.1) hsite) hdir

/-- **Stage 2, the top pullback kernel** on strict-half
configurations: the layer kernel pulled back along the
top extraction in both slots. -/
noncomputable def pullTopKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  layerKernel μG ρ β (tauTop hN z) (tauTop hN z')

/-- **Stage 2, the bottom pullback kernel** on strict-half
configurations: the layer kernel pulled back along the
bottom extraction, with the slots swapped (beta-1's
bottom word). -/
noncomputable def pullBotKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  layerKernel μG ρ β (tauBot hN z') (tauBot hN z)

/-- **Stage 2, beta-1 in pullback form.** The crossing
marginal is the pointwise product of the two pullback
kernels. This is the landed
`planeCrossingMarginal_layerKernel`, read through the
pullback definitions. -/
theorem planeCrossingMarginal_eq_pull_mul (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeCrossingMarginal μG ρ hN β z z'
      = pullTopKernel μG ρ hN β z z' * pullBotKernel μG ρ hN β z z' :=
  planeCrossingMarginal_layerKernel μG ρ hN β z z'

/-- **Stage 2, the seat pairing** of two strict-half
observables against a kernel on strict-half
configurations: the integral shape of both conjuncts of
the pin's `SeatSchurTarget`. -/
noncomputable def seatPairing (K : (↥(posLinks (N := N)) → G) →
      (↥(posLinks (N := N)) → G) → ℂ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) : ℂ :=
  ∫ r : (↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G),
      k₁ r.1 * (K r.1 r.2 * (starRingEnd ℂ) (k₂ r.2))
    ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))

/-- The seat pairing against the averaged kernel is the
landed `planeAvgPairing`, by definition. -/
theorem seatPairing_planeAvgKernel (hN : Even N) (β : ℝ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) :
    seatPairing μG (planeAvgKernel μG ρ hN β) k₁ k₂
      = planeAvgPairing μG ρ hN β k₁ k₂ := rfl

/-- The seat pairing depends only on the pointwise values
of its kernel. -/
theorem seatPairing_congr_kernel
    {K₁ K₂ : (↥(posLinks (N := N)) → G) →
      (↥(posLinks (N := N)) → G) → ℂ}
    (hK : ∀ z z', K₁ z z' = K₂ z z')
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) :
    seatPairing μG K₁ k₁ k₂ = seatPairing μG K₂ k₁ k₂ := by
  unfold seatPairing
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  show k₁ r.1 * (K₁ r.1 r.2 * (starRingEnd ℂ) (k₂ r.2))
    = k₁ r.1 * (K₂ r.1 r.2 * (starRingEnd ℂ) (k₂ r.2))
  rw [hK r.1 r.2]

/-- **Stage 2, the twirl reduction (landed form).** Under
the landed side conditions (`hρcont`, `0 < d`), the
averaged-kernel pairing of the twirled representatives
equals the pairing of the observables themselves: the
pairing factors through the two gauge averages. This is
`planeAvgPairing_averages`, applied on the diagonal. -/
theorem planeAvgPairing_twirled_eq (hρcont :
      Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfbdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    planeAvgPairing μG ρ hN β (posGaugeAvg μG f)
        (mirrorGaugeAvg μG f)
      = planeAvgPairing μG ρ hN β f f :=
  planeAvgPairing_averages μG ρ hρcont hN hd β f f hf hfbdd hf hfbdd

/-- **Stage 2, folding the averaged kernel.** The
averaged-kernel pairing is the marginal pairing of the
observables folded by the two positive half-action
weights (one per slot): the landed
`planeAvgKernel_factor` separates the averaged kernel
into the two real exponential weights times the crossing
marginal, and the weights fold into the two observables.
No positivity is used here; this is an identity of
integrals. -/
theorem planeAvgPairing_eq_seatPairing_marginal_fold
    (hN : Even N) (β : ℝ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) :
    planeAvgPairing μG ρ hN β k₁ k₂
      = seatPairing μG (planeCrossingMarginal μG ρ hN β)
          (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ) * k₁ z)
          (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ) * k₂ z) := by
  unfold seatPairing planeAvgPairing
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  show k₁ r.1 * (planeAvgKernel μG ρ hN β r.1 r.2
        * (starRingEnd ℂ) (k₂ r.2))
      = (Real.exp (-(halfActionP ρ β r.1)) : ℂ) * k₁ r.1
        * (planeCrossingMarginal μG ρ hN β r.1 r.2
          * (starRingEnd ℂ) ((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
            * k₂ r.2))
  have hstar : (starRingEnd ℂ)
        ((Real.exp (-(halfActionP ρ β r.2)) : ℂ))
      = (Real.exp (-(halfActionP ρ β r.2)) : ℂ) :=
    Complex.conj_ofReal _
  rw [planeAvgKernel_factor μG ρ hN β r.1 r.2, map_mul, hstar]
  ring

/-- **Stage 2, the layer pairing.** The pairing of a
layer observable against the layer kernel, in the exact
shape registered by `LayerKernelPos`. -/
noncomputable def layerPairing (β : ℝ)
    (F : (LayerLink N → G) → ℂ) : ℂ :=
  ∫ u : LayerLink N → G, ∫ u' : LayerLink N → G,
      (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
    ∂(Measure.pi fun _ : LayerLink N => μG)
    ∂(Measure.pi fun _ : LayerLink N => μG)

/-- **Stage 2, the layer pairing under the hypothesis.**
Assuming `LayerKernelPos`, the layer pairing of every
gauge-invariant layer observable is nonnegative in its
real part. This is a USE of the hypothesis, exactly as
registered; nothing about the layer kernel is factorized
or re-derived. -/
theorem layerPairing_nonneg_of_layerKernelPos (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (F : (LayerLink N → G) → ℂ)
    (hF : GaugeInvariantLayerObs (N := N) F) :
    0 ≤ (layerPairing μG ρ β F).re :=
  hLKP F hF

/-- **Stage 2, the top pullback pairing (iterated form).**
The pairing of a layer observable pulled back along the
top extraction, against the top pullback kernel, written
as an iterated integral over strict-half configurations. -/
noncomputable def pullTopPairingIter (hN : Even N) (β : ℝ)
    (F : (LayerLink N → G) → ℂ) : ℂ :=
  ∫ z : ↥(posLinks (N := N)) → G, ∫ z' : ↥(posLinks (N := N)) → G,
      (starRingEnd ℂ) (F (tauTop hN z))
        * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
        * F (tauTop hN z')
    ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
    ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)

/-- **Stage 2, top transport.** The top pullback pairing
(iterated form) of any layer observable is exactly its
layer pairing: the two extractions are measure-preserving
restrictions (`integral_comp_emb`, landed in the beta-1
cube), applied once per slot. No measurability or
boundedness side condition is needed for this identity of
iterated integrals. -/
theorem pullTopPairingIter_eq_layerPairing (hN : Even N) (β : ℝ)
    (F : (LayerLink N → G) → ℂ) :
    pullTopPairingIter μG ρ hN β F = layerPairing μG ρ β F := by
  have step : ∀ z : ↥(posLinks (N := N)) → G,
      (∫ z' : ↥(posLinks (N := N)) → G,
          (starRingEnd ℂ) (F (tauTop hN z))
            * layerKernel μG ρ β (tauTop hN z) (tauTop hN z')
            * F (tauTop hN z')
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u' : LayerLink N → G,
          (starRingEnd ℂ) (F (tauTop hN z))
            * layerKernel μG ρ β (tauTop hN z) u' * F u'
        ∂(Measure.pi fun _ : LayerLink N => μG) :=
    fun z => integral_comp_emb μG (embLayerTop hN)
      (embLayerTop_injective hN)
      (fun u' => (starRingEnd ℂ) (F (tauTop hN z))
        * layerKernel μG ρ β (tauTop hN z) u' * F u')
  unfold pullTopPairingIter layerPairing
  rw [integral_congr_ae (ae_of_all _ step)]
  exact integral_comp_emb μG (embLayerTop hN)
    (embLayerTop_injective hN)
    (fun u => ∫ u' : LayerLink N → G,
      (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
      ∂(Measure.pi fun _ : LayerLink N => μG))

/-- **Stage 2, bottom pullback pairing (iterated form).**
The pairing of a layer observable pulled back along the
bottom extraction, against the bottom pullback kernel
(slots swapped, as in beta-1's bottom word), written as
an iterated integral over strict-half configurations
with the primed variable outermost, so that the bottom
swap is absorbed by the iteration order. -/
noncomputable def pullBotPairingIter (hN : Even N) (β : ℝ)
    (F : (LayerLink N → G) → ℂ) : ℂ :=
  ∫ z' : ↥(posLinks (N := N)) → G, ∫ z : ↥(posLinks (N := N)) → G,
      F (tauBot hN z)
        * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
        * (starRingEnd ℂ) (F (tauBot hN z'))
    ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
    ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG)

/-- **Stage 2, bottom transport.** The bottom pullback
pairing (iterated form) of any layer observable is
exactly its layer pairing: the pointwise integrand is
the layer pairing's integrand with its factors commuted,
and the two extractions are measure-preserving
restrictions applied once per slot. -/
theorem pullBotPairingIter_eq_layerPairing (hN : Even N) (β : ℝ)
    (F : (LayerLink N → G) → ℂ) :
    pullBotPairingIter μG ρ hN β F = layerPairing μG ρ β F := by
  have step : ∀ z' : ↥(posLinks (N := N)) → G,
      (∫ z : ↥(posLinks (N := N)) → G,
          F (tauBot hN z)
            * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
            * (starRingEnd ℂ) (F (tauBot hN z'))
        ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      = ∫ u : LayerLink N → G,
          (starRingEnd ℂ) (F (tauBot hN z'))
            * layerKernel μG ρ β (tauBot hN z') u * F u
        ∂(Measure.pi fun _ : LayerLink N => μG) := by
    intro z'
    have hring : ∀ z : ↥(posLinks (N := N)) → G,
        F (tauBot hN z)
            * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
            * (starRingEnd ℂ) (F (tauBot hN z'))
          = (starRingEnd ℂ) (F (tauBot hN z'))
            * layerKernel μG ρ β (tauBot hN z') (tauBot hN z)
            * F (tauBot hN z) :=
      fun z => by ring
    rw [integral_congr_ae (ae_of_all _ hring)]
    exact integral_comp_emb μG (embLayerBot hN)
      (embLayerBot_injective hN)
      (fun u => (starRingEnd ℂ) (F (tauBot hN z'))
        * layerKernel μG ρ β (tauBot hN z') u * F u)
  unfold pullBotPairingIter layerPairing
  rw [integral_congr_ae (ae_of_all _ step)]
  exact integral_comp_emb μG (embLayerBot hN)
    (embLayerBot_injective hN)
    (fun u' => ∫ u : LayerLink N → G,
      (starRingEnd ℂ) (F u') * layerKernel μG ρ β u' u * F u
      ∂(Measure.pi fun _ : LayerLink N => μG))

/-- **Stage 2, top pullback pairing nonnegative.** Under
the assumed `LayerKernelPos`, the top pullback pairing
(iterated form) of every gauge-invariant layer observable
is nonnegative in its real part. -/
theorem pullTopPairingIter_nonneg (hN : Even N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (F : (LayerLink N → G) → ℂ)
    (hF : GaugeInvariantLayerObs (N := N) F) :
    0 ≤ (pullTopPairingIter μG ρ hN β F).re := by
  rw [pullTopPairingIter_eq_layerPairing μG ρ hN β F]
  exact layerPairing_nonneg_of_layerKernelPos μG ρ β hLKP F hF

/-- **Stage 2, bottom pullback pairing nonnegative.**
Under the assumed `LayerKernelPos`, the bottom pullback
pairing (iterated form) of every gauge-invariant layer
observable is nonnegative in its real part. -/
theorem pullBotPairingIter_nonneg (hN : Even N) (β : ℝ)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (F : (LayerLink N → G) → ℂ)
    (hF : GaugeInvariantLayerObs (N := N) F) :
    0 ≤ (pullBotPairingIter μG ρ hN β F).re := by
  rw [pullBotPairingIter_eq_layerPairing μG ρ hN β F]
  exact layerPairing_nonneg_of_layerKernelPos μG ρ β hLKP F hF

/-! ## Stage 3: the product step - finite-rank core, conditional
discharge, and the named open remainder -/

/-- **Stage 3, the finite-rank Schur core at the seat.**
Let the second kernel admit a finite expansion into
separated factors with nonnegative real coefficients.
If every induced factor pairing (the first kernel paired
against the two observables dressed by the expansion's
factors) is nonnegative in its real part, and every factor
integrand is integrable at the seat, then the pairing of
the pointwise product kernel is nonnegative in its real
part. This is the algebraic core of the memo's
finite-rank engine; producing the expansion for the
concrete second pullback is the open remainder below.
No kernel is factorized here: the expansion is a
hypothesis, and the first kernel enters only through its
pairings. -/
theorem seatPairing_mul_nonneg_of_finiteRank
    {ι : Type*} [Fintype ι]
    (K₁ K₂ : (↥(posLinks (N := N)) → G) →
      (↥(posLinks (N := N)) → G) → ℂ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (a b : ι → (↥(posLinks (N := N)) → G) → ℂ)
    (hExp : ∀ z z', K₂ z z'
      = ∑ i, (c i : ℂ) * (a i z * (starRingEnd ℂ) (b i z')))
    (hInt : ∀ i, Integrable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (k₁ r.1 * a i r.1)
          * (K₁ r.1 r.2 * (starRingEnd ℂ) (k₂ r.2 * b i r.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hTerm : ∀ i, 0 ≤ (seatPairing μG K₁
      (fun z => k₁ z * a i z) (fun z => k₂ z * b i z)).re) :
    0 ≤ (seatPairing μG (fun z z' => K₁ z z' * K₂ z z')
      k₁ k₂).re := by
  have hpt : ∀ r : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G),
      k₁ r.1 * ((fun z z' => K₁ z z' * K₂ z z') r.1 r.2
          * (starRingEnd ℂ) (k₂ r.2))
        = ∑ i, (c i : ℂ) * ((k₁ r.1 * a i r.1)
            * (K₁ r.1 r.2 * (starRingEnd ℂ) (k₂ r.2 * b i r.2))) := by
    intro r
    show k₁ r.1 * (K₁ r.1 r.2 * K₂ r.1 r.2
          * (starRingEnd ℂ) (k₂ r.2)) = _
    rw [hExp r.1 r.2]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    ring
  have hInt' : ∀ i, Integrable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (c i : ℂ) * ((k₁ r.1 * a i r.1)
          * (K₁ r.1 r.2 * (starRingEnd ℂ) (k₂ r.2 * b i r.2))))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    fun i => (hInt i).const_mul _
  unfold seatPairing
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_finset_sum _ (fun i _ => hInt' i)]
  simp only [integral_const_mul]
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg (hc i) (hTerm i)

/-- **Stage 3, conditional discharge of the pin.** IF the
bottom pullback kernel admits a finite expansion as in
`seatPairing_mul_nonneg_of_finiteRank`, and IF the induced
factor pairings are nonnegative and the factor integrands
integrable, both for the twirled pair and for its
half-action-folded form, THEN the pin's `SeatSchurTarget`
holds, in its exact registered form (cited from the pin,
not restated). The hypotheses of this theorem are exactly
the product step: the expansion, its factor pairings, and
its integrability. They are NOT discharged in this
module; see `seatSchurProductStepOpen` below. -/
theorem seatSchurTarget_of_finiteRankProductStep
    (hN : Even N) (β : ℝ)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (a b : ι → (↥(posLinks (N := N)) → G) → ℂ)
    (hExp : ∀ z z', pullBotKernel μG ρ hN β z z'
      = ∑ i, (c i : ℂ) * (a i z * (starRingEnd ℂ) (b i z')))
    (hIntMarg : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ) (i : ι),
      Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          ((posGaugeAvg μG f) r.1 * a i r.1)
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2
                * b i r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hTermMarg : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ) (i : ι),
      0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => (posGaugeAvg μG f) z * a i z)
        (fun z => (mirrorGaugeAvg μG f) z * b i z)).re)
    (hIntFold : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ) (i : ι),
      Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (((Real.exp (-(halfActionP ρ β r.1)) : ℂ)
              * (posGaugeAvg μG f) r.1) * a i r.1)
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ)
                (((Real.exp (-(halfActionP ρ β r.2)) : ℂ)
                    * (mirrorGaugeAvg μG f) r.2) * b i r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hTermFold : ∀ (f : (↥(posLinks (N := N)) → G) → ℂ) (i : ι),
      0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => ((Real.exp (-(halfActionP ρ β z)) : ℂ)
            * (posGaugeAvg μG f) z) * a i z)
        (fun z => ((Real.exp (-(halfActionP ρ β z)) : ℂ)
            * (mirrorGaugeAvg μG f) z) * b i z)).re) :
    SeatSchurTarget μG ρ hN β := by
  intro _hβ _hLKP f hf hfbdd
  have hprod : ∀ (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ),
      (∀ i, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (k₁ r.1 * a i r.1)
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) (k₂ r.2 * b i r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) →
      (∀ i, 0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
        (fun z => k₁ z * a i z) (fun z => k₂ z * b i z)).re) →
      0 ≤ (seatPairing μG (planeCrossingMarginal μG ρ hN β)
        k₁ k₂).re := by
    intro k₁ k₂ hI hT
    have h1 := seatPairing_mul_nonneg_of_finiteRank μG
      (pullTopKernel μG ρ hN β) (pullBotKernel μG ρ hN β)
      k₁ k₂ c hc a b hExp hI hT
    rwa [seatPairing_congr_kernel μG
      (fun z z' => (planeCrossingMarginal_eq_pull_mul μG ρ hN β
        z z').symm) k₁ k₂] at h1
  constructor
  · rw [planeAvgPairing_eq_seatPairing_marginal_fold μG ρ hN β
      (posGaugeAvg μG f) (mirrorGaugeAvg μG f)]
    exact hprod _ _ (hIntFold f) (hTermFold f)
  · exact hprod _ _ (hIntMarg f) (hTermMarg f)

/-- **Stage 3, the open remainder, registered.** The pin's
seat Schur itself, CITED from the pin
(`SeatSchurTarget`, `ThetLogos.Span3A0AssemblyPost`) - not
restated, and asserted nowhere in this module. This is
exactly what remains open at the product step after
stages 1-2 and the finite-rank core above: a
positivity-preserving expansion (spectral or finite-rank)
of the bottom pullback kernel at general `(G, rho)`,
whose induced factor pairings are nonnegative on the
twirled class - via the stage-2 transport, those pairings
are layer-kernel pairings - with the limit passage
controlled by the stage-1 bound
(`layerKernel_norm_le`), together with the identification
of the product-integral pairings of the pin with the
iterated-integral pairings of stage 2 at the bounded,
measurable seat. F2-W3 does not fire on this partial. -/
def seatSchurProductStepOpen (hN : Even N) (β : ℝ) : Prop :=
  SeatSchurTarget μG ρ hN β

end Span3SeatSchur

end ThetLogos
