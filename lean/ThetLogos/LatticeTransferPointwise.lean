import ThetLogos.LatticeTransfer
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# LatticeTransferPointwise — pointwise positivity of `T_β f`

**NO CLAIM.** Parts of the official Clay Yang–Mills statement
closed by this module: 0.

Stage 1b-D's dossier (`whitepaper/pitch-4-stage-1b-d-2026-10-17.md`)
fenced one small hole in its own text: "**Pointwise positivity
of `T_β f`** (positive functions to positive functions) is not
stated; it follows from the form positivity by the standard
indicator argument (priced S, not formalized here)." This
module formalizes exactly that argument (gap-theorem queue,
2026-10-24, item Q2).

For a slice observable `f` that is pointwise real and
nonnegative, the vector `T_β (sliceState f)` has an a.e.
representative that is pointwise real and nonnegative:
a.e. `z`, `0 ≤ (T_β f z).re` and `(T_β f z).im = 0`.
The argument is the dossier's: apply the landed form
positivity `transferOp_form_nonneg` to the pair (indicator
of a measurable set `S`, `f`); the form value is the set
integral of `T_β f` over `S`; the real part of that integral
is nonnegative and the imaginary part vanishes, for every
`S`; Mathlib's a.e.-from-set-integrals lemmas then give the
pointwise-a.e. conclusion. No Gram clause, no OS-form input —
the Gibbs measure's positivity alone, as with the form
positivity itself.

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  The indicator step `setIntegral_transferOp_sliceState` and
  the headline `transferOp_pointwise_nonneg` are
  machine-checked (parent-verified rebuild, 3,562 jobs;
  axioms standard, no `sorryAx`). Dossier:
  `whitepaper/gap-queue-q2-pointwise-positivity-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Set

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The indicator step of the argument: for every measurable
set `S` of slice configurations, the set integral of the
transferred observable over `S` has nonnegative real part and
vanishing imaginary part. -/
theorem setIntegral_transferOp_sliceState (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (f : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β))
    (hfpos : ∀ z, 0 ≤ (f z).re ∧ (f z).im = 0)
    (S : Set (↥(sliceLinks (N := N)) → G)) (hS : MeasurableSet S) :
    0 ≤ (∫ z in S,
        ((transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf)) z).re
        ∂(sliceMeasure (N := N) μG ρ β))
    ∧ (∫ z in S,
        ((transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf)) z).im
        ∂(sliceMeasure (N := N) μG ρ β)) = 0 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  -- The indicator observable of `S`.
  set gS : (↥(sliceLinks (N := N)) → G) → ℂ :=
    S.indicator (fun _ => (1 : ℂ)) with hgS
  have hgSm : AEStronglyMeasurable gS (sliceMeasure (N := N) μG ρ β) :=
    aestronglyMeasurable_const.indicator hS
  have hgB : ∀ z, ‖gS z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ S <;> simp [hgS, Set.indicator, hz]
  have hg : MemLp gS 2 (sliceMeasure (N := N) μG ρ β) :=
    memLp_of_bounded μG ρ hρcont hd β gS hgSm 1 hgB
  have hgpos : ∀ z, 0 ≤ (gS z).re ∧ (gS z).im = 0 := by
    intro z
    by_cases hz : z ∈ S <;> simp [hgS, Set.indicator, hz]
  have hform := transferOp_form_nonneg μG ρ hN2 hρcont hd β f gS hf hg
    hfpos hgpos
  have hInt : Integrable
      ⇑(transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf))
      (sliceMeasure (N := N) μG ρ β) :=
    (Lp.memLp (transferOp μG ρ hN2 hρcont β
      (sliceState μG ρ β f hf))).integrable (by norm_num)
  -- The form value is the set integral of the transferred observable.
  have hinner : (inner ℂ (sliceState μG ρ β gS hg)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf)))
      = ∫ z in S, (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β f hf)) z
        ∂(sliceMeasure (N := N) μG ρ β) := by
    rw [MeasureTheory.L2.inner_def, ← integral_indicator hS]
    apply integral_congr_ae
    have hcoe : ⇑(sliceState μG ρ β gS hg)
        =ᵐ[sliceMeasure (N := N) μG ρ β] gS := hg.coeFn_toLp
    filter_upwards [hcoe] with z hz
    rw [hz]
    by_cases hzS : z ∈ S
    · rw [hgS, Set.indicator_of_mem hzS, Set.indicator_of_mem hzS]
      simp [RCLike.inner_apply]
    · rw [hgS, Set.indicator_of_notMem hzS, Set.indicator_of_notMem hzS]
      simp [RCLike.inner_apply]
  rw [hinner] at hform
  constructor
  · have hre : (∫ z in S, (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β f hf)) z
        ∂(sliceMeasure (N := N) μG ρ β)).re
      = ∫ z in S, ((transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β f hf)) z).re
        ∂(sliceMeasure (N := N) μG ρ β) :=
      (integral_re (hInt.integrableOn (s := S))).symm
    rw [hre] at hform
    exact hform.1
  · have him : (∫ z in S, (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β f hf)) z
        ∂(sliceMeasure (N := N) μG ρ β)).im
      = ∫ z in S, ((transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β f hf)) z).im
        ∂(sliceMeasure (N := N) μG ρ β) :=
      (integral_im (hInt.integrableOn (s := S))).symm
    rw [him] at hform
    exact hform.2

/-- **Pointwise positivity of `T_β f`** (gap-theorem queue
Q2; the Stage 1b-D dossier's named hole): a pointwise real
nonnegative slice observable is transferred to a vector whose
representative is a.e. pointwise real and nonnegative. At
every real `β`; no Gram clause spent. -/
theorem transferOp_pointwise_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (f : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hf : MemLp f 2 (sliceMeasure (N := N) μG ρ β))
    (hfpos : ∀ z, 0 ≤ (f z).re ∧ (f z).im = 0) :
    ∀ᵐ z ∂(sliceMeasure (N := N) μG ρ β),
      0 ≤ ((transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf)) z).re
      ∧ ((transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf)) z).im
        = 0 := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont hd β
  have hInt : Integrable
      ⇑(transferOp μG ρ hN2 hρcont β (sliceState μG ρ β f hf))
      (sliceMeasure (N := N) μG ρ β) :=
    (Lp.memLp (transferOp μG ρ hN2 hρcont β
      (sliceState μG ρ β f hf))).integrable (by norm_num)
  have hre : 0 ≤ᵐ[sliceMeasure (N := N) μG ρ β]
      (fun z => ((transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β f hf)) z).re) :=
    MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg hInt.re
      (fun S hS _ => (setIntegral_transferOp_sliceState μG ρ hN2
        hρcont hd β f hf hfpos S hS).1)
  have him : (fun z => ((transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β f hf)) z).im)
      =ᵐ[sliceMeasure (N := N) μG ρ β] 0 :=
    MeasureTheory.Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero
      hInt.im
      (fun S hS _ => (setIntegral_transferOp_sliceState μG ρ hN2
        hρcont hd β f hf hfpos S hS).2)
  filter_upwards [hre, him] with z hzre hzim
  exact ⟨hzre, hzim⟩

end ThetLogos
