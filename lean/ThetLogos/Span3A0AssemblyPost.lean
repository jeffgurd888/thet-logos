/-
# F2-W0: the F2 weld line's registration pin

Brick F2-W0 of the F2 weld line, per the governing scoping
memo `routeb-general-scratch/scoping-f2-weld-2026-10-31.md`
(read in full; esp. section 1 pin inventory, section 2 the
weld exactly, section 4 the seat Schur statement, section 5
the split and kills, section 6 what retires) and pack
`routeb-general-scratch/pack-f2-w0.md`.

**REGISTRATION ONLY.** This module freezes the weld's target
statements. It proves NOTHING beyond pin-grade identities
(definition read-backs). No target below is asserted to
hold, and no proof of any target is attempted here.

**NO CLAIM** - parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. Proof-grade distance
toward the continuum: ZERO, before and after this pin.

## The headline target, cited - not restated

The weld's headline is `A0AssemblyTarget`, as registered in
`ThetLogos.Span3FactLayerKernelPos` (closing section): at
`Even N`, `LayerKernelPos` at every `beta >= 0` implies
clause (a) of `TransferFormPos` at every `beta >= 0`. It is
cited here as this line's headline (see
`F2WeldHeadlineTarget` below, an exact citation alias) and
is NOT restated into any new claim.

## Target (1): the weld implication, parameterized pin form

The weld's mathematical content (memo section 2) is exactly
the intermediate implication, at general `(G, rho)`, `muG`
Haar probability, `Even N`, `hN2 : 2 <= N`, `h-rho-cont`,
and each `beta >= 0`:

  `LayerKernelPos muG rho beta`
    -> `SliceHPosOne muG rho hN2 h-rho-cont beta`

citing the landed ends exactly: `LayerKernelPos` in
`ThetLogos.LayerKernelPos`, and `SliceHPosOne` with its
landed transport
`inner_transferOp_self_re_nonneg_of_sliceHPosOne` in
`ThetLogos.LatticeSliceDescent`.

**Import reality - on the face.** Those two chains sit on
opposite sides of the `reflSite_eq_torusShift_zero`
duplicate seam (memo section 3): the `LayerKernelPos` chain
sits on the `PlaneCrossingFactor` side; the
`LatticeSliceDescent` chain (via `LatticeReconZero`) pulls
`LatticeGramSeries`, the other side. The two declarations
of that name are two DIFFERENT statements (memo section 3),
and no single Lean environment can import both chains
today. This module therefore does NOT import
`LatticeSliceDescent`, edits NOTHING outside itself, and
registers target (1) in the house parameterized pin style:
the slice endpoint is carried as an explicit parameter
`SlicePos`, a predicate over `(hN2, h-rho-cont, beta)` at
the fixed `(muG, rho, N)` of the section, exactly as
`ThetLogos.Span3ScalingLimit` registered
`ScalingLimitOfLattice` over owned objects with its opaque
hypothesis fields labeled. The intended instantiation -
named here, not imported - is

  `SlicePos hN2 h-rho-cont beta`
    `= SliceHPosOne muG rho hN2 h-rho-cont beta`.

**The direct statement of target (1), with `SliceHPosOne`
named in the code itself, becomes formable only after
F2-W1** (the duplicate rename, memo section 3 / section 5:
three edit sites in `PlaneCrossingFactor.lean` only). That
rename is NOT done by this module.

## Target (2): the seat Schur, stated exactly

The seat Schur (memo section 4 headline, verbatim-grade)
IS stated directly below (`SeatSchurTarget`), because its
vocabulary - `planeAvgPairing`, `posGaugeAvg`,
`mirrorGaugeAvg`, `planeCrossingMarginal`,
`planeAvgKernel_factor`, and `LayerKernelPos` - is
co-importable on the `PlaneCrossingFactor` side today.

Statement: at general `(G, rho)`, `muG` Haar probability,
`Even N`, `h-rho-cont`, `beta >= 0`, ASSUMING
`LayerKernelPos muG rho beta`: for every bounded
a.e.-strongly-measurable strict-half observable `f`, the
diagonal pairing of its twirled representatives is
nonnegative:

  `0 <= (planeAvgPairing muG rho hN beta f-hat-1 f-hat-2).re`

where `f-hat-1 = posGaugeAvg muG f` and
`f-hat-2 = mirrorGaugeAvg muG f` are the two gauge averages
(the twirled class of `planeAvgPairing_averages`,
`ThetLogos.PlaneCrossingSeparate`) - equivalently, the
pointwise product kernel
`A1 * A2 = planeCrossingMarginal` (beta-1 factorization
`planeCrossingMarginal_layerKernel`,
`ThetLogos.PlaneCrossingCube`: the two pullbacks of the one
kernel along the top and bottom extractions, the bottom
with arguments swapped) is pairing-positive on that class,
and hence so is the averaged kernel via
`planeAvgKernel_factor` (`ThetLogos.PlaneAvgKernel`: the
two half-action factors are positive reals, one per slot).

**Seat hypotheses - ON THE FACE (K-F2-3 fence).**
- Probability measures: `muG` is a Haar probability
  measure (`IsProbabilityMeasure muG` in the section
  context), and every configuration measure in the pairing
  is a product of copies of `muG`, hence a probability
  measure. No general measure space appears.
- Bounded kernels: the seat's kernels are uniformly
  pointwise bounded at this seat - for the averaged kernel
  this is landed (`planeAvgKernel_norm_le`); the
  corresponding bound for the layer kernel itself is
  F2-W2's first step (memo section 4, item 2). Bounded
  kernels on finite measure spaces are `MemLp p` for every
  `p`, and their pointwise products are bounded, hence
  `MemLp 2`: the L2 typecheck obstruction of the abstract
  form (below) is absent at this seat.
- Twirled class: positivity is demanded ONLY for the
  twirled representatives (`posGaugeAvg` / `mirrorGaugeAvg`)
  of bounded a.e.-strongly-measurable strict-half
  observables - the class on which the pullback pairings
  are pairings of gauge-invariant layer observables, i.e.
  exactly the class `LayerKernelPos` controls. The
  observable side conditions (a.e. strong measurability
  w.r.t. the product Haar probability measure, and a
  pointwise norm bound) are hypothesis fields of
  `SeatSchurTarget` itself, not hidden.
A statement of this Schur without those seat hypotheses
is K-F2-3 void (see kills below).

**The general-API Schur is NOT this line's statement.**
The abstract product statement for arbitrary L2 kernels on
general measure spaces (SHELF-3b item 3, named open in
`ThetLogos.IntegralKernelSchur`) is ill-posed as stated at
L2 generality and is NOT restated, consumed, or claimed
here. This line eats the seat-shaped Schur only.

## The fence (memo section 2, verbatim-grade)

Completing the weld proves the implication ONLY. It does
NOT prove FACT (`StratumColumnFactorization` stays an
unproved pin). It does NOT prove `LayerKernelPos` - the
weld ASSUMES it; positivity of the layer kernel at general
`(G, rho)` remains the open core. It does NOT prove clause
(a) - only the implication into it. Not
`UniformMarginFactorization`, not any uniformity arrow,
not the gap package's compactness hypothesis. Continuum
distance: still zero.

**FORBIDDEN move - on the face.** No Gram factorization of
the layer kernel itself inside this line. A Gram
factorization of that kernel with `MemLp` factors would
prove `LayerKernelPos` outright; that is the positivity
core itself, NOT a weld. The weld assumes the core's
target as a hypothesis and builds nothing on the core's
own lanes (the core chain stays single-lane, outside this
line's queue). Any draft of this line that factorizes the
layer kernel itself is void on sight.

## Armed kills (memo section 5) - on the face

- **K-F2-1 (fix scope).** If the F2-W1 rename forces any
  edit outside `PlaneCrossingFactor.lean`'s three sites,
  W1 stops and re-prices at full rank.
- **K-F2-2 (invariance confinement).** If composing the
  pullbacks is found to require layer-kernel positivity on
  NON-gauge-invariant observables - i.e. the twirl
  confinement fails at the weld's actual generality - then
  `LayerKernelPos` as registered does not suffice for the
  assembly, and the weld route dies at full rank. Silently
  strengthening this pin's targets is void. Companion: any
  draft factorizing the layer kernel itself (fence above)
  is void on sight.
- **K-F2-3 (generality creep / vacuity).** Any seat Schur
  stated for abstract positive kernels at L2 generality
  re-enters SHELF-3b's ill-posed statement and is void on
  sight; any landing restricted to finite seats under the
  weld headline is the vacuity failure. The section 4
  statement carries its seat hypotheses on its face or it
  does not land.
- **K-F2-4 (buy inflation).** Any dossier sentence
  describing the weld's landing as progress on FACT, on
  the layer kernel's positivity, on clause (a) itself, or
  on uniformity is void on sight. The buy is a machine
  link between open statements.

This module is NOT in the root import list of the library
(the corpus pattern for recent pins); it is verified by a
targeted build.
-/

import ThetLogos.Span3FactLayerKernelPos
import ThetLogos.PlaneCrossingSeparate

namespace ThetLogos

open MeasureTheory

section Span3A0AssemblyPost

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## Target (1): the weld implication (parameterized pin) -/

/-- **The weld implication - TARGET PIN (F2-W0, stated, not
proved).** Parameterized form (module header): `SlicePos`
is the slice endpoint carried as an explicit parameter, a
predicate over `(hN2, h-rho-cont, beta)` at this section's
fixed `(muG, rho, N)`; its intended instantiation, named
on the face and formable in code only after F2-W1, is
`SliceHPosOne muG rho hN2 h-rho-cont beta`
(`ThetLogos.LatticeSliceDescent`). At that instantiation
this is exactly the memo section 2 implication: at
`Even N`, `hN2 : 2 <= N`, continuity of the representation,
and each `beta >= 0`, `LayerKernelPos muG rho beta`
(the hypothesis end, `ThetLogos.LayerKernelPos`) implies
the one-step slice diagonal positivity end, whose landed
transport `inner_transferOp_self_re_nonneg_of_sliceHPosOne`
then gives clause (a) on all of the OS space. No instance
of this pin is asserted to hold. -/
def layerKernelPos_implies_sliceHPosOne
    (SlicePos : (2 ≤ N) →
      (Continuous fun g : G => repMatrix ρ g) → ℝ → Prop) :
    Prop :=
  ∀ (hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ), 0 ≤ β →
    LayerKernelPos (N := N) μG ρ β → SlicePos hN2 hρcont β

/-- **Pin read-back for target (1).** The parameterized
weld pin, read back: at any slice-endpoint predicate, the
pin is exactly the per-`beta` implication above. Pin-grade
identity only - the definition unfolded, no content
added, no instance discharged. -/
theorem layerKernelPos_implies_sliceHPosOne_apply
    (SlicePos : (2 ≤ N) →
      (Continuous fun g : G => repMatrix ρ g) → ℝ → Prop)
    (h : layerKernelPos_implies_sliceHPosOne μG ρ SlicePos)
    (hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (hβ : 0 ≤ β)
    (hLKP : LayerKernelPos (N := N) μG ρ β) :
    SlicePos hN2 hρcont β :=
  h hN hN2 hρcont β hβ hLKP

/-! ## Target (2): the seat Schur (stated directly, exactly) -/

/-- **The seat Schur - TARGET PIN (F2-W0, stated, not
proved).** At `Even N` (`hN`), `beta >= 0`, assuming
`LayerKernelPos muG rho beta`: for every strict-half
observable `f` that is a.e. strongly measurable w.r.t. the
product Haar probability measure on strict-half
configurations and pointwise bounded (the seat hypotheses,
on the face - module header), the diagonal pairing of its
twirled representatives is nonnegative in BOTH of its
registered forms:

- the averaged-kernel form: `0 <= (planeAvgPairing muG rho
  hN beta (posGaugeAvg muG f) (mirrorGaugeAvg muG f)).re`;
- the pointwise-product form: the same integral shape with
  `planeCrossingMarginal muG rho hN beta` in the kernel
  slot - the product kernel of the beta-1 factorization
  `planeCrossingMarginal_layerKernel`, pairing-positive on
  the twirled class.

The two forms are tied by `planeAvgKernel_factor` (the
half-action factors are positive reals, one per slot).
Positivity is demanded ONLY on this twirled class, ONLY at
this probability-measure, bounded-kernel seat (K-F2-3).
No instance of this pin is asserted to hold; the
layer-kernel norm bound this target's proof route consumes
is F2-W2's first step, not a statement of this pin. -/
def SeatSchurTarget (hN : Even N) (β : ℝ) : Prop :=
  0 ≤ β → LayerKernelPos (N := N) μG ρ β →
  ∀ f : (↥(posLinks (N := N)) → G) → ℂ,
    AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
    (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
    0 ≤ (planeAvgPairing μG ρ hN β (posGaugeAvg μG f)
        (mirrorGaugeAvg μG f)).re ∧
    0 ≤ (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        (posGaugeAvg μG f) r.1
          * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).re

/-- **Pin read-back for target (2), averaged-kernel form.**
Under the seat Schur pin, the twirled diagonal
`planeAvgPairing` is nonnegative for every bounded
a.e.-strongly-measurable strict-half observable.
Pin-grade projection only. -/
theorem seatSchurTarget_planeAvgPairing_nonneg (hN : Even N)
    (β : ℝ) (h : SeatSchurTarget μG ρ hN β) (hβ : 0 ≤ β)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfbdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    0 ≤ (planeAvgPairing μG ρ hN β (posGaugeAvg μG f)
        (mirrorGaugeAvg μG f)).re :=
  (h hβ hLKP f hf hfbdd).1

/-- **Pin read-back for target (2), product-kernel form.**
Under the seat Schur pin, the pointwise product kernel
`planeCrossingMarginal` is pairing-positive on the twirled
class. Pin-grade projection only. -/
theorem seatSchurTarget_marginalPairing_nonneg (hN : Even N)
    (β : ℝ) (h : SeatSchurTarget μG ρ hN β) (hβ : 0 ≤ β)
    (hLKP : LayerKernelPos (N := N) μG ρ β)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hf : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfbdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    0 ≤ (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        (posGaugeAvg μG f) r.1
          * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).re :=
  (h hβ hLKP f hf hfbdd).2

/-! ## The headline target, cited -/

/-- **The headline target, CITED - not restated.** This is
exactly `A0AssemblyTarget` as registered in
`ThetLogos.Span3FactLayerKernelPos`: at `Even N`,
`LayerKernelPos` at every `beta >= 0` implies clause (a)
of `TransferFormPos` at every `beta >= 0`. The definition
here is a citation alias only, so this line's headline has
a local name to register against; it introduces no new
statement and no new claim, and it is not proved here. -/
def F2WeldHeadlineTarget (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    Prop :=
  A0AssemblyTarget (N := N) μG ρ hN2 hρcont hd

/-- **Citation check for the headline.** The cited headline
is the registered `A0AssemblyTarget` itself, read in both
directions. Pin-grade identity only. -/
theorem f2WeldHeadlineTarget_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    F2WeldHeadlineTarget (N := N) μG ρ hN2 hρcont hd ↔
      A0AssemblyTarget (N := N) μG ρ hN2 hρcont hd :=
  Iff.rfl

/-- **Headline read-back.** The cited headline, applied:
under it, `LayerKernelPos` at every `beta >= 0` (at
`Even N`) yields clause (a) of `TransferFormPos` at every
`beta >= 0`. This is the registered `A0AssemblyTarget`
read back through its citation alias - pin-grade identity
only; the headline itself remains stated, not proved. -/
theorem f2WeldHeadlineTarget_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (h : F2WeldHeadlineTarget (N := N) μG ρ hN2 hρcont hd)
    (hN : Even N)
    (hLKP : ∀ β : ℝ, 0 ≤ β → LayerKernelPos (N := N) μG ρ β) :
    ∀ β : ℝ, 0 ≤ β →
      TransferFormClauseA (N := N) μG ρ β hN2 hρcont :=
  h hN hLKP

end Span3A0AssemblyPost

end ThetLogos
