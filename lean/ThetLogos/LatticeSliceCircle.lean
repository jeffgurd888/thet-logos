/-
# S2-3: the (R-C2)ʳ discharge at the U(1) seat

Stage 2 ladder, brick S2-3 (priced M), under the revised S2-2
gate (`whitepaper/stage2-s22-gate-revision-2026-10-24.md`, §2
row 18, §3.2, §5 note). The gate's S2-2c engine
(`LatticeSliceEngine.lean`) is assembled under one named
hypothesis, `SliceHPosOne` (H-pos(1)ʳ): positivity of the
one-step pairing `Π₁` on slice observables. This brick
discharges that hypothesis at the U(1) seat by the re-aimed
Route C clause (R-C2)ʳ and instantiates the engine
hypothesis-free there.

**Fences — read first.** This discharge is at the U(1) seat
ONLY. It is NOT a general `(G, ρ)` 1b-B result, and it is
not an input to Stage 1b-B: no `osForm` positivity at any
general `(G, ρ)` is asserted anywhere in this module, and
the general-case label is untouched (Stage 1b-B positivity
at general `(G, ρ)` remains OPEN). What is discharged is
the slice engine's named hypothesis at one seat, by that
seat's own landed positivity theorem (Route C). **NO
CLAIM** — parts of any Clay statement closed by this
module: 0.

## The route

* Route C (`LatticeGramSeries.lean`): `osForm_circle_nonneg`
  — OS positivity of the U(1) Wilson theory at every
  `β ≥ 0`, on observables factoring through the strict
  positive half with a continuous bounded representative.
* The K-S2-3 class-coverage exhibition: slice observables
  are `posLinks` observables — `sliceLinks ⊆ posLinks` at
  even `N` (landed, `LatticeOSSpace`), with representative
  `φ ∘ posToSlice` (`sliceFactor`, `continuous_posToSlice`).
  So a **continuous** slice observable lies in Route C's
  class verbatim, and S2-2a's identity
  `slicePairOne_self_eq_osForm` turns its `Π₁` diagonal
  into Route C's `osForm` diagonal.
* The regularity closure: `SliceHPosOne` quantifies over
  all `MemLp` slice observables, not only continuous ones.
  The gap is closed by density, not by strengthening: the
  diagonal `x ↦ (⟪x, transferOp x⟫).re` is a continuous
  function of the `L²` slice state (`transferOp` is a
  continuous linear map), the good set is therefore
  closed, and continuous functions are dense in
  `L²` of the slice measure — a probability measure on the
  compact slice-configuration space
  (`ContinuousMap.toLp_denseRange`). Nonnegativity on the
  dense continuous subclass passes to every `L²` class.

## The Π₂-level clause (gate (R-C2)ʳ, item (c))

The gate's second hypothesis H-pos(2)ʳ is not outstanding
at this seat or any other: in the factored form in which
the gate states it, it is S2-2b's theorem
`sliceHPosTwo_proved` at every real `β` (the `Π₂` diagonal
is a norm square). It is restated at the seat below
(`sliceHPosTwo_circle`) for the record, and it already
sits inside the engine package as its clause 8. No
further Π₂-level clause is named by (R-C2)ʳ beyond the
package.

Seat data, fixed throughout: `G = Circle`,
`μG = haarProb Circle`, `ρ = circleRep` (so `d = 1`),
even `N`, `β ≥ 0`.

Status: brick S2-3 — verdict STANDS IN FULL ((R-C2) r
discharged at the U(1) seat; the class-coverage gap
closed by an L2-density argument, by proof);
parent-verified 2026-10-24 (targeted build exit 0,
strict recount, axiom check). Dossier:
`whitepaper/stage2-s23-circle-discharge-2026-10-24.md`.
-/

import ThetLogos.LatticeSliceEngine
import ThetLogos.LatticeGramSeries
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace ThetLogos

open MeasureTheory

variable {N : ℕ} [NeZero N]

/-- A continuous complex function on the (compact) slice
configuration space is bounded. -/
theorem exists_forall_norm_le_of_continuous
    {φ : (↥(sliceLinks (N := N)) → Circle) → ℂ}
    (hφ : Continuous φ) :
    ∃ C : ℝ, ∀ z, ‖φ z‖ ≤ C := by
  obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn
    Set.univ_nonempty (continuous_norm.comp hφ).continuousOn
  exact ⟨‖φ z₀‖, fun z => hz₀ (Set.mem_univ z)⟩

/-- **(R-C2)ʳ, continuous subclass.** For a continuous slice
observable at the U(1) seat, `β ≥ 0`, the one-step diagonal
is nonnegative: by S2-2a it is the `osForm` diagonal of the
slice observable, which factors through the strict positive
half (landed `sliceFactor`), and Route C's
`osForm_circle_nonneg` applies verbatim. -/
theorem slicePairOne_circle_nonneg_of_continuous
    (hN2 : 2 ≤ N) (hN : Even N) (β : ℝ) (hβ : 0 ≤ β)
    (φ : (↥(sliceLinks (N := N)) → Circle) → ℂ)
    (hφc : Continuous φ)
    (hφ : MemLp φ 2
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)) :
    0 ≤ (slicePairOne (haarProb Circle) circleRep hN2
      circleRep_continuous β φ hφ φ hφ).re := by
  rw [slicePairOne_self_eq_osForm (haarProb Circle) circleRep
    hN2 circleRep_continuous hN (by norm_num) β φ hφ]
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_continuous hφc
  have hF : ∀ U : Config (Fin 4 → ZMod N) Circle,
      sliceObs φ U = (φ ∘ posToSlice hN)
        (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1) :=
    fun U => sliceFactor hN φ U
  exact (osForm_circle_nonneg hN β hβ (sliceObs φ)
    (φ ∘ posToSlice hN) hF
    (hφc.comp (continuous_posToSlice hN)) C
    (fun z => hC _)).1

/-- **(R-C2)ʳ DISCHARGED — `SliceHPosOne` at the U(1) seat.**
For every even `N` and every `β ≥ 0`, H-pos(1)ʳ holds at
`(haarProb Circle, circleRep)` with **no positivity
hypothesis**: the one-step diagonal is nonnegative on
*every* `L²` slice observable. The continuous subclass is
Route C verbatim (`slicePairOne_circle_nonneg_of_continuous`);
the extension to all `MemLp` observables is `L²`-density —
the diagonal is a continuous function of the slice state,
the good set is closed, and continuous functions are dense
in `L²` of the slice measure
(`ContinuousMap.toLp_denseRange`; the slice measure is a
probability measure on the compact metrizable
slice-configuration space, hence weakly regular). -/
theorem sliceHPosOne_circle (hN2 : 2 ≤ N) (hN : Even N)
    (β : ℝ) (hβ : 0 ≤ β) :
    SliceHPosOne (haarProb Circle) circleRep hN2
      circleRep_continuous β := by
  haveI : IsProbabilityMeasure
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    isProbabilityMeasure_sliceMeasure (haarProb Circle)
      circleRep circleRep_continuous (by norm_num) β
  intro φ hφ
  have hQcont : Continuous
      fun x : osSpace (N := N) (haarProb Circle) circleRep β =>
        (inner ℂ x (transferOp (haarProb Circle) circleRep hN2
          circleRep_continuous β x)).re :=
    Complex.continuous_re.comp
      (continuous_inner.comp
        (continuous_id.prodMk
          (transferOp (haarProb Circle) circleRep hN2
            circleRep_continuous β).continuous))
  set S : Set (osSpace (N := N) (haarProb Circle) circleRep β) :=
    (fun x => (inner ℂ x (transferOp (haarProb Circle) circleRep
      hN2 circleRep_continuous β x)).re) ⁻¹' Set.Ici 0 with hS
  have hSclosed : IsClosed S :=
    isClosed_Ici.preimage hQcont
  have hgood : ∀ ψ : C((↥(sliceLinks (N := N)) → Circle), ℂ),
      ContinuousMap.toLp 2
          (sliceMeasure (N := N) (haarProb Circle) circleRep β)
          ℂ ψ ∈ S := by
    intro ψ
    obtain ⟨C, hC⟩ :=
      exists_forall_norm_le_of_continuous ψ.continuous
    have hψLp : MemLp
        (ψ : (↥(sliceLinks (N := N)) → Circle) → ℂ) 2
        (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
      memLp_of_bounded (haarProb Circle) circleRep
        circleRep_continuous (by norm_num) β ψ
        ψ.continuous.stronglyMeasurable.aestronglyMeasurable C hC
    have hbridge : ContinuousMap.toLp 2
          (sliceMeasure (N := N) (haarProb Circle) circleRep β)
          ℂ ψ
        = sliceState (haarProb Circle) circleRep β ψ hψLp := by
      rw [Lp.ext_iff]
      exact (ContinuousMap.coeFn_toLp (p := 2)
        (μ := sliceMeasure (N := N) (haarProb Circle)
          circleRep β) (𝕜 := ℂ) ψ).trans
        (MemLp.coeFn_toLp hψLp).symm
    rw [hbridge]
    exact slicePairOne_circle_nonneg_of_continuous hN2 hN β hβ
      ψ ψ.continuous hψLp
  have hdense : DenseRange (ContinuousMap.toLp 2
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ)
      (μ := sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (𝕜 := ℂ) (p := 2) (by norm_num)
  have hsub : closure (Set.range (ContinuousMap.toLp 2
        (sliceMeasure (N := N) (haarProb Circle) circleRep β)
        ℂ)) ⊆ S :=
    closure_minimal (Set.range_subset_iff.mpr hgood) hSclosed
  have hx : sliceState (haarProb Circle) circleRep β φ hφ
      ∈ closure (Set.range (ContinuousMap.toLp 2
        (sliceMeasure (N := N) (haarProb Circle) circleRep β)
        ℂ)) := by
    rw [hdense.closure_range]
    exact Set.mem_univ _
  exact hsub hx

/-- **The Π₂-level clause at the seat (gate item (c)).**
H-pos(2)ʳ in factored form, at the U(1) seat — in fact at
general `(G, ρ)` and every real `β`, by S2-2b's theorem:
the `Π₂` diagonal is the norm square
`‖transferOp (sliceState φ)‖²`. Restated here so the
seat's record carries it; no discharge was outstanding. -/
theorem sliceHPosTwo_circle (hN2 : 2 ≤ N) (hN : Even N)
    (β : ℝ) :
    SliceHPosTwo (haarProb Circle) circleRep hN2
      circleRep_continuous β :=
  sliceHPosTwo_proved (haarProb Circle) circleRep hN2
    circleRep_continuous hN β

/-- **The U(1) engine, hypothesis-free (S2-3 headline).**
S2-2c's `sliceEngine_package` instantiated at the U(1)
seat for every `β ≥ 0`, its single hypothesis
`SliceHPosOne` supplied by `sliceHPosOne_circle`. The
13 clauses are the package's own, verbatim: the
`Π₁`-quotient is a pre-Hilbert space (inner product on
classes, positivity, definiteness, null = radical); the
descended `T̂` is characterized by `Π₂`, unique,
self-adjoint, positive in factored form (clause 8 — 2b's
norm-square content, NOT an `osForm` discharge), a
contraction with a continuous-linear realization; the
vacuum `Ω` is a unit vector fixed by `T̂`; and `Ω` is
cyclic by construction. At this seat only — see the
module header's fence. -/
theorem sliceEngine_circle_package (hN2 : 2 ≤ N) (hN : Even N)
    (β : ℝ) (hβ : 0 ≤ β) :
    (∀ a b : ↥(sliceObsSubmodule (N := N) (haarProb Circle)
        circleRep β),
      inner ℂ (sliceMk (haarProb Circle) circleRep hN2
            circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ) a)
          (sliceMk (haarProb Circle) circleRep hN2
            circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ) b)
        = slicePairOneObs (haarProb Circle) circleRep hN2
            circleRep_continuous β a b)
    ∧ (∀ x : sliceQuotient (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ),
        0 ≤ (inner ℂ x x).re)
    ∧ (∀ x : sliceQuotient (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ),
        inner ℂ x x = 0 → x = 0)
    ∧ (∀ a : ↥(sliceObsSubmodule (N := N) (haarProb Circle)
          circleRep β),
        (a ∈ sliceNullSubmodule (haarProb Circle) circleRep
            hN2 circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ))
          ↔ ∀ b : ↥(sliceObsSubmodule (N := N)
                (haarProb Circle) circleRep β),
              slicePairOneObs (haarProb Circle) circleRep hN2
                circleRep_continuous β a b = 0)
    ∧ (∀ a b : ↥(sliceObsSubmodule (N := N) (haarProb Circle)
          circleRep β),
        inner ℂ (sliceMk (haarProb Circle) circleRep hN2
              circleRep_continuous hN β
              (sliceHPosOne_circle hN2 hN β hβ) b)
            (sliceHat (haarProb Circle) circleRep hN2
              circleRep_continuous hN β
              (sliceHPosOne_circle hN2 hN β hβ)
              (sliceMk (haarProb Circle) circleRep hN2
                circleRep_continuous hN β
                (sliceHPosOne_circle hN2 hN β hβ) a))
          = slicePairTwoObs (haarProb Circle) circleRep hN2
              circleRep_continuous β b a)
    ∧ (∀ S : sliceQuotient (haarProb Circle) circleRep hN2
            circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ) →ₗ[ℂ]
          sliceQuotient (haarProb Circle) circleRep hN2
            circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ),
        (∀ a b : ↥(sliceObsSubmodule (N := N)
              (haarProb Circle) circleRep β),
          inner ℂ (sliceMk (haarProb Circle) circleRep hN2
                circleRep_continuous hN β
                (sliceHPosOne_circle hN2 hN β hβ) b)
              (S (sliceMk (haarProb Circle) circleRep hN2
                circleRep_continuous hN β
                (sliceHPosOne_circle hN2 hN β hβ) a))
            = slicePairTwoObs (haarProb Circle) circleRep hN2
                circleRep_continuous β b a)
          → S = sliceHat (haarProb Circle) circleRep hN2
              circleRep_continuous hN β
              (sliceHPosOne_circle hN2 hN β hβ))
    ∧ LinearMap.IsSymmetric
        (sliceHat (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ))
    ∧ (∀ x : sliceQuotient (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ),
        0 ≤ (inner ℂ x
          (sliceHat (haarProb Circle) circleRep hN2
            circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ) x)).re)
    ∧ (∀ x : sliceQuotient (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ),
        ‖sliceHat (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ) x‖ ≤ ‖x‖)
    ∧ (∀ x : sliceQuotient (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ),
        sliceHatCLM (haarProb Circle) circleRep hN2
            circleRep_continuous hN β
            (sliceHPosOne_circle hN2 hN β hβ) x
          = sliceHat (haarProb Circle) circleRep hN2
              circleRep_continuous hN β
              (sliceHPosOne_circle hN2 hN β hβ) x)
    ∧ ‖sliceOmega (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one‖ = 1
    ∧ sliceHat (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ)
        (sliceOmega (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one)
      = sliceOmega (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one
    ∧ Function.Surjective
        (sliceMk (haarProb Circle) circleRep hN2
          circleRep_continuous hN β
          (sliceHPosOne_circle hN2 hN β hβ)) :=
  sliceEngine_package (haarProb Circle) circleRep hN2
    circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one
