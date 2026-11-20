/-
# StageSliceFoldPin — SLICE Seat 2: the ℤ₃ fold of the Stage-2 slice seat

DRAFT — brick SS2-B1a (configuration-level phase invariance).
Target: lean/ThetLogos/StageSliceFoldPin.lean, branch `stageslice`.

The fold is the ℤ₃-INVARIANT SECTOR of the Stage-2 slice's OS space
`osSpace (haarProb Circle) circleRep β` — NOT a quotient (Seat 1,
OrbifoldGapPin, was the quotient). The ℤ₃ sits inside the circle's
rotation symmetry: multiplication of every link variable by a
constant phase `c` with `c ^ 3 = 1`.

FENCES: NO CLAIM; dials 0/4; a finite sector gap is not a continuum
or Yang–Mills gap; lane grade only.
-/

import ThetLogos.LatticeTransfer
import ThetLogos.LatticeOSMarginal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ThetLogos.SliceTransportA

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section FoldAction

variable {N : ℕ} [NeZero N]
variable (μG : Measure Circle) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : Circle →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The global phase action on configurations: multiply every link
by the constant phase `c`. This is the circle's own rotation
symmetry; the fold subgroup is the case `c ^ 3 = 1`. -/
noncomputable def phaseConfig (c : Circle) (U : Config (Fin 4 → ZMod N) Circle) :
    Config (Fin 4 → ZMod N) Circle :=
  fun ℓ => c * U ℓ

theorem measurable_phaseConfig (c : Circle) :
    Measurable (phaseConfig (N := N) c) := by
  -- `unfold` first (the `measurable_sliceStep` idiom): the bare `of_eval`
  -- goal leaves the pi-family a metavariable and `const_mul`'s constant
  -- unassignable; after unfolding, the expected type pins it.
  unfold phaseConfig
  exact Measurable.of_eval fun ℓ =>
    Measurable.const_mul
      (measurable_pi_apply (X := fun _ : Link (Fin 4 → ZMod N) => Circle) ℓ) c

/-- Plaquettes are invariant under the global phase action: the
phased word `c·a · c·b · (c·d)⁻¹ · (c·e)⁻¹` collapses to the
unphased word because `Circle` is commutative (the phases cancel
in pairs). -/
theorem plaquette_phaseConfig (c : Circle)
    (U : Config (Fin 4 → ZMod N) Circle) (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    plaquette (torusShift N) (phaseConfig c U) x μ ν
      = plaquette (torusShift N) U x μ ν := by
  show (c * U (x, μ)) * (c * U (torusShift N μ x, ν))
      * (c * U (torusShift N ν x, μ))⁻¹ * (c * U (x, ν))⁻¹
    = U (x, μ) * U (torusShift N μ x, ν)
      * (U (torusShift N ν x, μ))⁻¹ * (U (x, ν))⁻¹
  -- `abel` does not fire on `Circle` in this pin (abel_nf: no progress,
  -- even on `c * c⁻¹ = 1`); use the explicit-argument cancellation route.
  have hc : c * c * c⁻¹ * c⁻¹ = 1 := by
    rw [mul_assoc c c c⁻¹, mul_inv_cancel, mul_one, mul_inv_cancel]
  calc (c * U (x, μ)) * (c * U (torusShift N μ x, ν))
        * (c * U (torusShift N ν x, μ))⁻¹ * (c * U (x, ν))⁻¹
      = (U (x, μ) * U (torusShift N μ x, ν)
        * (U (torusShift N ν x, μ))⁻¹ * (U (x, ν))⁻¹)
        * (c * c * c⁻¹ * c⁻¹) := by
          rw [mul_inv_rev, mul_inv_rev]
          ac_rfl
    _ = U (x, μ) * U (torusShift N μ x, ν)
        * (U (torusShift N ν x, μ))⁻¹ * (U (x, ν))⁻¹ := by
          rw [hc, mul_one]

/-- The Wilson action is invariant under the global phase action
(every plaquette is). -/
theorem wilsonAction_phaseConfig (c : Circle) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) Circle) :
    wilsonAction (torusShift N) ρ β (phaseConfig c U)
      = wilsonAction (torusShift N) ρ β U := by
  unfold wilsonAction
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold plaquetteDensity
  rw [plaquette_phaseConfig c U x μ ν]

/-- The Gibbs density is invariant under the global phase action,
because the Wilson action is. -/
theorem gibbsDensity_phaseConfig (c : Circle) (β : ℝ)
    (U : Config (Fin 4 → ZMod N) Circle) :
    gibbsDensity (torusShift N) ρ β (phaseConfig c U)
      = gibbsDensity (torusShift N) ρ β U := by
  apply Subtype.ext
  show Real.exp (- wilsonAction (torusShift N) ρ β (phaseConfig c U))
    = Real.exp (- wilsonAction (torusShift N) ρ β U)
  rw [wilsonAction_phaseConfig ρ c β U]

/-- The product (configuration) measure is invariant under the
global phase action: every factor is preserved by left
multiplication (Haar invariance). -/
theorem measurePreserving_phaseConfig (c : Circle) :
    MeasurePreserving (phaseConfig (N := N) c) (configMeasure μG)
      (configMeasure μG) := by
  unfold configMeasure
  exact measurePreserving_pi (fun _ : Link (Fin 4 → ZMod N) => μG)
    (fun _ : Link (Fin 4 → ZMod N) => μG)
    (fun _ => measurePreserving_mul_left μG c)

theorem configMeasure_map_phaseConfig (c : Circle) :
    (configMeasure (Λ := Fin 4 → ZMod N) μG).map (phaseConfig (N := N) c)
      = configMeasure (Λ := Fin 4 → ZMod N) μG :=
  (measurePreserving_phaseConfig (N := N) μG c).map_eq

/-- **The Gibbs measure is invariant under the global phase
action** (strong `Measure.map` form), for every real `β`. Mirror
of `gibbsMeasure_map_shiftConfig`, with phase invariance of the
density in place of shift invariance — the phase action needs no
commutation hypothesis, because it acts on the link values, not
the sites. -/
theorem gibbsMeasure_map_phaseConfig (c : Circle)
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    Measure.map (phaseConfig c) (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β := by
  ext s hs
  rw [Measure.map_apply (measurable_phaseConfig c) hs]
  unfold gibbsMeasure
  rw [Measure.smul_apply, Measure.smul_apply]
  have h1 : ((configMeasure μG :
        Measure (Config (Fin 4 → ZMod N) Circle)).restrict s)
      = Measure.map (phaseConfig c)
          ((configMeasure μG :
            Measure (Config (Fin 4 → ZMod N) Circle)).restrict
            (phaseConfig c ⁻¹' s)) := by
    rw [← Measure.restrict_map (measurable_phaseConfig c) hs,
      configMeasure_map_phaseConfig μG c]
  have key : (∫⁻ U, (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
        ∂((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) Circle)).restrict
          (phaseConfig c ⁻¹' s)))
      = ∫⁻ U, (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)
        ∂((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) Circle)).restrict s) := by
    rw [h1, lintegral_map (measurable_gibbsDensity_coe ρ hρcont β)
      (measurable_phaseConfig c)]
    refine lintegral_congr fun U => ?_
    exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞))
      (gibbsDensity_phaseConfig ρ c β U).symm
  have hwd : ((configMeasure μG :
        Measure (Config (Fin 4 → ZMod N) Circle)).withDensity
        (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞)))
        (phaseConfig c ⁻¹' s)
      = ((configMeasure μG :
          Measure (Config (Fin 4 → ZMod N) Circle)).withDensity
          (fun U => (gibbsDensity (torusShift N) ρ β U : ℝ≥0∞))) s := by
    rw [withDensity_apply _ ((measurable_phaseConfig c) hs),
      withDensity_apply _ hs]
    exact key
  rw [hwd]

end FoldAction

section SlicePhase

variable {N : ℕ} [NeZero N]
variable (μG : Measure Circle) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : Circle →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The phase action on slice configurations: multiply every
slice link by the constant phase `c`. -/
noncomputable def slicePhase (c : Circle) (z : ↥(sliceLinks (N := N)) → Circle) :
    ↥(sliceLinks (N := N)) → Circle :=
  fun ℓ => c * z ℓ

theorem measurable_slicePhase (c : Circle) :
    Measurable (slicePhase (N := N) c) := by
  -- Same repair as `measurable_phaseConfig` (B1a): `unfold` first,
  -- pin the pi-family on `measurable_pi_apply`, or the constant
  -- stays a metavariable.
  unfold slicePhase
  exact Measurable.of_eval fun ℓ =>
    Measurable.const_mul
      (measurable_pi_apply (X := fun _ : ↥(sliceLinks (N := N)) => Circle) ℓ) c

/-- Restriction to the time-`0` slice commutes with the phase
action (both sides read `ℓ ↦ c * U ℓ.1`). -/
theorem restrictConfig_phaseConfig (c : Circle)
    (U : Config (Fin 4 → ZMod N) Circle) :
    restrictConfig sliceLinks (phaseConfig c U)
      = slicePhase c (restrictConfig sliceLinks U) :=
  rfl

/-- The slice (OS) measure is invariant under the slice phase
action: it is the slice marginal of a phase-invariant measure,
and restriction commutes with the action. -/
theorem sliceMeasure_map_slicePhase (c : Circle)
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    Measure.map (slicePhase (N := N) c) (sliceMeasure (N := N) μG ρ β)
      = sliceMeasure (N := N) μG ρ β := by
  unfold sliceMeasure marginalMeasure
  rw [Measure.map_map (measurable_slicePhase c)
        (measurable_restrictConfig sliceLinks)]
  have hcomp : slicePhase (N := N) c ∘ restrictConfig sliceLinks
      = restrictConfig sliceLinks ∘ phaseConfig c := by
    funext U
    exact (restrictConfig_phaseConfig c U).symm
  rw [hcomp, ← Measure.map_map (measurable_restrictConfig sliceLinks)
        (measurable_phaseConfig c),
    gibbsMeasure_map_phaseConfig μG ρ c hρcont β]

/-- The slice phase action as a measure-preserving map of the
slice measure (packaged form, for the `Lp` pullback). -/
theorem measurePreserving_slicePhase (c : Circle)
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    MeasurePreserving (slicePhase (N := N) c) (sliceMeasure μG ρ β)
      (sliceMeasure μG ρ β) :=
  ⟨measurable_slicePhase c, sliceMeasure_map_slicePhase μG ρ c hρcont β⟩

/-- Slice phases compose by multiplying the phases (pointwise
associativity). -/
theorem slicePhase_mul (c c' : Circle)
    (z : ↥(sliceLinks (N := N)) → Circle) :
    slicePhase c (slicePhase c' z) = slicePhase (c * c') z := by
  funext ℓ
  show c * (c' * z ℓ) = (c * c') * z ℓ
  rw [mul_assoc]

end SlicePhase

section FoldUnitary

variable {N : ℕ} [NeZero N]

/-- The fold isometry: precomposition with the slice phase rotation,
as a linear isometry of the OS space. -/
noncomputable def foldIsometry (β : ℝ) (c : Circle) :
    osSpace (N := N) (haarProb Circle) circleRep β →ₗᵢ[ℂ]
      osSpace (N := N) (haarProb Circle) circleRep β :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (slicePhase c)
    (measurePreserving_slicePhase (haarProb Circle) circleRep c
      circleRep_continuous β)

/-- The inverse rotation undoes the fold isometry. Proved by `Lp.ext`
plus an `EventuallyEq` chain (the dependent-rewrite trap is avoided:
the rearrangement is a plain function equality). -/
theorem foldIsometry_inv_apply (β : ℝ) (c : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    foldIsometry β c (foldIsometry β c⁻¹ f) = f := by
  have hcomp : slicePhase c⁻¹ ∘ slicePhase c
      = (id : (↥(sliceLinks (N := N)) → Circle)
        → (↥(sliceLinks (N := N)) → Circle)) := by
    funext z ℓ
    show c⁻¹ * (c * z ℓ) = z ℓ
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hmp : MeasurePreserving (slicePhase (N := N) c)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c
      circleRep_continuous β
  have hmp' : MeasurePreserving (slicePhase (N := N) c⁻¹)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c⁻¹
      circleRep_continuous β
  apply MeasureTheory.Lp.ext
  -- `compMeasurePreservingₗᵢ_apply` is not a generated name in this
  -- pin; restate by defeq (foldIsometry unfolds to the ₗᵢ, whose
  -- FunLike application is the plain `compMeasurePreserving`).
  show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c) hmp
      (MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c⁻¹) hmp' f))
    =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β] ⇑f
  have e_outer : ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c) hmp
        (MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c⁻¹) hmp' f))
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c⁻¹) hmp' f)
          ∘ slicePhase (N := N) c :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp
  have e_inner : ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c⁻¹) hmp' f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) c⁻¹ :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp'
  have e_post : ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c⁻¹) hmp' f)
        ∘ slicePhase (N := N) c
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        (⇑f ∘ slicePhase (N := N) c⁻¹) ∘ slicePhase (N := N) c :=
    hmp.quasiMeasurePreserving.ae_eq_comp e_inner
  have e_rearr : ((⇑f ∘ slicePhase (N := N) c⁻¹) ∘ slicePhase (N := N) c) = ⇑f := by
    rw [Function.comp_assoc, hcomp, Function.comp_id]
  exact e_outer.trans (e_post.trans (Filter.EventuallyEq.of_eq e_rearr))

/-- The fold unitary: the fold isometry promoted to a linear isometry
equivalence, by surjectivity (the inverse rotation is a preimage). -/
noncomputable def foldUnitary (β : ℝ) (c : Circle) :
    osSpace (N := N) (haarProb Circle) circleRep β ≃ₗᵢ[ℂ]
      osSpace (N := N) (haarProb Circle) circleRep β :=
  LinearIsometryEquiv.ofSurjective (foldIsometry β c) (fun f =>
    ⟨foldIsometry β c⁻¹ f, foldIsometry_inv_apply β c f⟩)

theorem foldUnitary_apply (β : ℝ) (c : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    foldUnitary β c f = foldIsometry β c f := rfl

/-- Folding twice composes the rotations (note the order: the inner
fold's rotation lands on the right of the product). -/
theorem foldUnitary_mul (β : ℝ) (c c' : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    foldUnitary β c (foldUnitary β c' f) = foldUnitary β (c' * c) f := by
  have hmp : MeasurePreserving (slicePhase (N := N) c)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c
      circleRep_continuous β
  have hmp' : MeasurePreserving (slicePhase (N := N) c')
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c'
      circleRep_continuous β
  apply MeasureTheory.Lp.ext
  have e_outer : ⇑(foldUnitary β c (foldUnitary β c' f))
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑(foldUnitary β c' f) ∘ slicePhase (N := N) c := by
    show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c) hmp
        (foldUnitary β c' f))
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑(foldUnitary β c' f) ∘ slicePhase (N := N) c
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp
  have e_inner : ⇑(foldUnitary β c' f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) c' := by
    show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c') hmp' f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) c'
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp'
  have e_post : ⇑(foldUnitary β c' f) ∘ slicePhase (N := N) c
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        (⇑f ∘ slicePhase (N := N) c') ∘ slicePhase (N := N) c :=
    hmp.quasiMeasurePreserving.ae_eq_comp e_inner
  have e_rearr : (⇑f ∘ slicePhase (N := N) c') ∘ slicePhase (N := N) c
      = ⇑f ∘ slicePhase (N := N) (c' * c) := by
    funext x
    show ⇑f (slicePhase (N := N) c' (slicePhase (N := N) c x))
      = ⇑f (slicePhase (N := N) (c' * c) x)
    congr 1
    exact slicePhase_mul c' c x
  have e_rhs : ⇑(foldUnitary β (c' * c) f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) (c' * c) := by
    have hmp'' : MeasurePreserving (slicePhase (N := N) (c' * c))
        (sliceMeasure (N := N) (haarProb Circle) circleRep β)
        (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
      measurePreserving_slicePhase (haarProb Circle) circleRep (c' * c)
        circleRep_continuous β
    show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) (c' * c)) hmp'' f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) (c' * c)
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp''
  exact (e_outer.trans (e_post.trans (Filter.EventuallyEq.of_eq e_rearr))).trans e_rhs.symm

/-- Folding by `1` does nothing. -/
theorem foldUnitary_one_apply (β : ℝ)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    foldUnitary β 1 f = f := by
  have hmp : MeasurePreserving (slicePhase (N := N) (1 : Circle))
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep 1
      circleRep_continuous β
  have h1 : slicePhase (N := N) (1 : Circle) = id := by
    funext z ℓ
    show (1 : Circle) * z ℓ = z ℓ
    exact one_mul _
  apply MeasureTheory.Lp.ext
  have e1 : ⇑(foldUnitary β 1 f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) 1 := by
    show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) 1) hmp f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑f ∘ slicePhase (N := N) 1
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp
  exact e1.trans (Filter.EventuallyEq.of_eq (by rw [h1, Function.comp_id]))

/-- A cube-root-of-unity fold, applied three times, is the identity. -/
theorem foldUnitary_cube (β : ℝ) (c : Circle) (hc3 : c ^ 3 = 1)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    foldUnitary β c (foldUnitary β c (foldUnitary β c f)) = f := by
  rw [foldUnitary_mul, foldUnitary_mul, ← pow_three, hc3]
  exact foldUnitary_one_apply β f

/-- The fold unitary fixes the vacuum (the constant function `1`). -/
theorem foldUnitary_vacuum (β : ℝ) (c : Circle) :
    foldUnitary β c (osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
        circleRep_continuous Nat.zero_lt_one β)
      = osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
          circleRep_continuous Nat.zero_lt_one β := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) (haarProb Circle) circleRep
    circleRep_continuous Nat.zero_lt_one β
  have hmp : MeasurePreserving (slicePhase (N := N) c)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c
      circleRep_continuous β
  have e_const : (⇑(osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
          circleRep_continuous Nat.zero_lt_one β) :
          (↥(sliceLinks (N := N)) → Circle) → ℂ)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        Function.const _ (1 : ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2
        (sliceMeasure (N := N) (haarProb Circle) circleRep β) (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        Function.const _ (1 : ℂ)
    exact MeasureTheory.Lp.coeFn_const (p := 2)
      (μ := sliceMeasure (N := N) (haarProb Circle) circleRep β) (c := (1 : ℂ))
  apply MeasureTheory.Lp.ext
  have e_outer : ⇑(foldUnitary β c (osVacuum (μG := haarProb Circle) (ρ := circleRep)
          (N := N) circleRep_continuous Nat.zero_lt_one β))
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑(osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
          circleRep_continuous Nat.zero_lt_one β) ∘ slicePhase (N := N) c := by
    show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c) hmp
        (osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
          circleRep_continuous Nat.zero_lt_one β))
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
        ⇑(osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
          circleRep_continuous Nat.zero_lt_one β) ∘ slicePhase (N := N) c
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp
  exact e_outer.trans
    ((hmp.quasiMeasurePreserving.ae_eq_comp e_const).trans
      ((Filter.EventuallyEq.of_eq (rfl : Function.const _ (1 : ℂ) ∘ slicePhase (N := N) c
        = Function.const _ (1 : ℂ))).trans e_const.symm))

/-- There is a primitive cube root of unity in the circle. -/
theorem exists_primitive_cube_root_circle :
    ∃ c : Circle, c ^ 3 = 1 ∧ c ≠ 1 := by
  refine ⟨Circle.exp (2 * Real.pi / 3), ?_, ?_⟩
  · rw [← Circle.exp_natCast_mul]
    have h : ((3 : ℕ) : ℝ) * (2 * Real.pi / 3) = 2 * Real.pi := by
      push_cast
      ring
    rw [h]
    exact Circle.exp_eq_one.mpr ⟨1, by simp⟩
  · intro hcon
    rw [Circle.exp_eq_one] at hcon
    obtain ⟨n, hn⟩ := hcon
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h6 : (2 * Real.pi) * (1 - 3 * (n : ℝ)) = 0 := by linarith [hn]
    rcases mul_eq_zero.mp h6 with h | h
    · exact (by positivity : (2 : ℝ) * Real.pi ≠ 0) h
    · have hcast : ((3 * n : ℤ) : ℝ) = 1 := by push_cast; linarith [h]
      have h7 : 3 * n = 1 := by exact_mod_cast hcast
      omega

end FoldUnitary

section FoldCommute

variable {N : ℕ} [NeZero N]

/-- The phase rotation commutes with the next-slice reading:
rotating the whole configuration rotates the next slice the
same way (both legs are pointwise). -/
theorem phaseConfig_nextConfig (hN2 : 2 ≤ N) (c : Circle)
    (U : Config (Fin 4 → ZMod N) Circle) :
    nextConfig (G := Circle) (N := N) hN2 (phaseConfig c U)
      = slicePhase c (nextConfig (G := Circle) (N := N) hN2 U) := by
  funext ℓ
  rfl

/-- The global phase action as a measurable equivalence of
configuration space (its inverse is the inverse phase). -/
noncomputable def phaseConfigEquiv (c : Circle) :
    Config (Fin 4 → ZMod N) Circle ≃ᵐ Config (Fin 4 → ZMod N) Circle where
  toFun := phaseConfig c
  invFun := phaseConfig c⁻¹
  left_inv U := by
    funext ℓ
    show c⁻¹ * (c * U ℓ) = U ℓ
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  right_inv U := by
    funext ℓ
    show c * (c⁻¹ * U ℓ) = U ℓ
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  measurable_toFun := measurable_phaseConfig c
  measurable_invFun := measurable_phaseConfig c⁻¹

/-- The fold unitary acts as precomposition with the slice phase,
almost everywhere. -/
theorem coeFn_foldUnitary (β : ℝ) (c : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    ⇑(foldUnitary β c f)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
      ⇑f ∘ slicePhase (N := N) c := by
  have hmp : MeasurePreserving (slicePhase (N := N) c)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c
      circleRep_continuous β
  show ⇑(MeasureTheory.Lp.compMeasurePreserving (slicePhase (N := N) c) hmp f)
    =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
      ⇑f ∘ slicePhase (N := N) c
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp

/-- The inverse fold unitary acts as precomposition with the
inverse slice phase, almost everywhere. -/
theorem coeFn_foldUnitary_symm (β : ℝ) (c : Circle)
    (g : osSpace (N := N) (haarProb Circle) circleRep β) :
    ⇑((foldUnitary β c)⁻¹ g)
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
      ⇑g ∘ slicePhase (N := N) c⁻¹ := by
  have hmp : MeasurePreserving (slicePhase (N := N) c)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c
      circleRep_continuous β
  have hmp' : MeasurePreserving (slicePhase (N := N) c⁻¹)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β)
      (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
    measurePreserving_slicePhase (haarProb Circle) circleRep c⁻¹
      circleRep_continuous β
  have hcomp : slicePhase (N := N) c ∘ slicePhase (N := N) c⁻¹ = id := by
    funext z ℓ
    show c * (c⁻¹ * z ℓ) = z ℓ
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have e1 : ⇑g
      =ᵐ[sliceMeasure (N := N) (haarProb Circle) circleRep β]
      ⇑((foldUnitary β c)⁻¹ g) ∘ slicePhase (N := N) c := by
    have hU := coeFn_foldUnitary β c ((foldUnitary β c)⁻¹ g)
    have hU2 : foldUnitary β c ((foldUnitary β c)⁻¹ g) = g :=
      LinearIsometryEquiv.apply_symm_apply _ _
    rw [hU2] at hU
    exact hU
  have e2 := hmp'.quasiMeasurePreserving.ae_eq_comp e1
  have e3 : (⇑((foldUnitary β c)⁻¹ g) ∘ slicePhase (N := N) c)
        ∘ slicePhase (N := N) c⁻¹
      = ⇑((foldUnitary β c)⁻¹ g) := by
    rw [Function.comp_assoc, hcomp, Function.comp_id]
  exact (e2.trans (Filter.EventuallyEq.of_eq e3)).symm

/-- **The fold commutes with the transfer operator** (K-FOLD-COMMUTE
is decided here: it does NOT fire — the commutation holds). Via
the form identity `transferOp_inner` and one Gibbs substitution
`U ↦ phaseConfig c⁻¹ U`, using phase invariance of the Gibbs
measure and `phaseConfig_nextConfig`. -/
theorem foldUnitary_comm_transferOp_apply (hN2 : 2 ≤ N) (β : ℝ) (c : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    transferOp (haarProb Circle) circleRep hN2 circleRep_continuous β
        (foldUnitary β c f)
      = foldUnitary β c
        (transferOp (haarProb Circle) circleRep hN2 circleRep_continuous β f) := by
  apply eq_of_forall_inner_left (haarProb Circle) circleRep β
  intro g
  have eLHS : inner ℂ g (transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β (foldUnitary β c f))
      = ∫ W, (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks
            (phaseConfig c⁻¹ W)))
          * ⇑f (nextConfig (G := Circle) (N := N) hN2 W)
        ∂(gibbsMeasure (torusShift N) (haarProb Circle) circleRep β) := by
    rw [transferOp_inner (haarProb Circle) circleRep hN2 circleRep_continuous β
      g (foldUnitary β c f)]
    have hnext : MeasurePreserving (nextConfig (G := Circle) (N := N) hN2)
        (gibbsMeasure (torusShift N) (haarProb Circle) circleRep β)
        (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
      measurePreserving_nextConfig (haarProb Circle) circleRep hN2
        circleRep_continuous β
    have e1 : (fun W => (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks W))
          * ⇑(foldUnitary β c f) (nextConfig (G := Circle) (N := N) hN2 W))
        =ᵐ[gibbsMeasure (torusShift N) (haarProb Circle) circleRep β]
        (fun W => (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks W))
          * ⇑f (slicePhase (N := N) c (nextConfig (G := Circle) (N := N) hN2 W))) := by
      filter_upwards
        [hnext.quasiMeasurePreserving.ae_eq_comp (coeFn_foldUnitary β c f)] with W hW
      simp only [Function.comp_apply] at hW
      rw [hW]
    rw [integral_congr_ae e1]
    have hpc : ∀ W : Config (Fin 4 → ZMod N) Circle,
        phaseConfig c⁻¹ (phaseConfig c W) = W := by
      intro W
      funext ℓ
      show c⁻¹ * (c * W ℓ) = W ℓ
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    have e2' : (∫ W, (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks W))
          * ⇑f (slicePhase (N := N) c (nextConfig (G := Circle) (N := N) hN2 W))
          ∂(gibbsMeasure (torusShift N) (haarProb Circle) circleRep β))
        = ∫ W, (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks
              (phaseConfig c⁻¹ (phaseConfig c W))))
          * ⇑f (nextConfig (G := Circle) (N := N) hN2 (phaseConfig c W))
          ∂(gibbsMeasure (torusShift N) (haarProb Circle) circleRep β) := by
      apply integral_congr_ae
      filter_upwards with W
      rw [hpc, phaseConfig_nextConfig]
    rw [e2']
    exact MeasurePreserving.integral_comp
      ⟨measurable_phaseConfig c,
        gibbsMeasure_map_phaseConfig (haarProb Circle) circleRep c
          circleRep_continuous β⟩
      (phaseConfigEquiv c).measurableEmbedding
      (fun W => (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks
            (phaseConfig c⁻¹ W)))
        * ⇑f (nextConfig (G := Circle) (N := N) hN2 W))
  have eRHS : inner ℂ g (foldUnitary β c (transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β f))
      = ∫ W, (starRingEnd ℂ) (⇑g (restrictConfig (G := Circle) sliceLinks
            (phaseConfig c⁻¹ W)))
          * ⇑f (nextConfig (G := Circle) (N := N) hN2 W)
        ∂(gibbsMeasure (torusShift N) (haarProb Circle) circleRep β) := by
    have hU : inner ℂ g (foldUnitary β c (transferOp (haarProb Circle) circleRep hN2
          circleRep_continuous β f))
        = inner ℂ ((foldUnitary β c)⁻¹ g)
          (transferOp (haarProb Circle) circleRep hN2 circleRep_continuous β f) := by
      conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply (foldUnitary β c) g]
      exact LinearIsometryEquiv.inner_map_map _ _ _
    rw [hU, transferOp_inner (haarProb Circle) circleRep hN2 circleRep_continuous β
      ((foldUnitary β c)⁻¹ g) f]
    have hrest : MeasurePreserving (restrictConfig (G := Circle) sliceLinks)
        (gibbsMeasure (torusShift N) (haarProb Circle) circleRep β)
        (sliceMeasure (N := N) (haarProb Circle) circleRep β) :=
      measurePreserving_slicePull (haarProb Circle) circleRep β
    apply integral_congr_ae
    filter_upwards
      [hrest.quasiMeasurePreserving.ae_eq_comp (coeFn_foldUnitary_symm β c g)] with W hW
    simp only [Function.comp_apply] at hW
    rw [hW]
    congr 2
  rw [eLHS, eRHS]

/-- **The invariant sector:** the fixed-point subspace of the
fold unitary — the kernel of `U − 1`, where `U` is the fold
unitary. This is the ℤ₃-invariant sector of the slice OS
space (the fold, not a quotient). -/
noncomputable def invariantSector (β : ℝ) (c : Circle) :
    Submodule ℂ (osSpace (N := N) (haarProb Circle) circleRep β) :=
  LinearMap.ker ((foldUnitary β c).toLinearEquiv.toLinearMap - LinearMap.id)

theorem mem_invariantSector (β : ℝ) (c : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β) :
    f ∈ invariantSector β c ↔ foldUnitary β c f = f := by
  rw [invariantSector, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  exact sub_eq_zero

/-- The invariant sector is closed (it is the fixed-point set
of the continuous fold unitary). -/
theorem invariantSector_isClosed (β : ℝ) (c : Circle) :
    IsClosed (invariantSector (N := N) β c :
      Set (osSpace (N := N) (haarProb Circle) circleRep β)) := by
  have hset : (invariantSector (N := N) β c :
      Set (osSpace (N := N) (haarProb Circle) circleRep β))
      = {f | foldUnitary β c f = f} := by
    ext f
    simp only [SetLike.mem_coe, mem_invariantSector, Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_eq (foldUnitary β c).continuous continuous_id

/-- The transfer operator preserves the invariant sector
(the fold commutes with it). -/
theorem transferOp_mem_invariantSector (hN2 : 2 ≤ N) (β : ℝ) (c : Circle)
    (f : osSpace (N := N) (haarProb Circle) circleRep β)
    (hf : f ∈ invariantSector β c) :
    transferOp (haarProb Circle) circleRep hN2 circleRep_continuous β f
      ∈ invariantSector β c := by
  rw [mem_invariantSector] at hf ⊢
  rw [← foldUnitary_comm_transferOp_apply hN2 β c f, hf]

/-- The transfer operator also preserves the orthogonal
complement of the invariant sector (it is self-adjoint at
even `N`, and it commutes with the fold). -/
theorem transferOp_mem_invariantSector_orth (hN2 : 2 ≤ N) (hN : Even N)
    (β : ℝ) (c : Circle)
    (x : osSpace (N := N) (haarProb Circle) circleRep β)
    (hx : x ∈ (invariantSector β c)ᗮ) :
    transferOp (haarProb Circle) circleRep hN2 circleRep_continuous β x
      ∈ (invariantSector β c)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  rw [← ContinuousLinearMap.adjoint_inner_left,
    transferOp_adjoint (haarProb Circle) circleRep hN2 circleRep_continuous hN β]
  exact hx _ (transferOp_mem_invariantSector hN2 β c u hu)

/-- The vacuum lies in the invariant sector (the fold fixes
it). -/
theorem osVacuum_mem_invariantSector (β : ℝ) (c : Circle) :
    osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
        circleRep_continuous Nat.zero_lt_one β ∈ invariantSector β c := by
  rw [mem_invariantSector]
  exact foldUnitary_vacuum β c

end FoldCommute

section FoldGap

variable {N : ℕ} [NeZero N]

/-- The folded transfer operator: the transfer operator
restricted to the invariant sector (it preserves the sector
by B2). -/
noncomputable def foldTransferOp (hN2 : 2 ≤ N) (β : ℝ) (c : Circle) :
    (invariantSector (N := N) β c) →L[ℂ] (invariantSector (N := N) β c) :=
  (transferOp (N := N) (haarProb Circle) circleRep hN2 circleRep_continuous β).restrict
    (fun x hx => transferOp_mem_invariantSector hN2 β c x hx)

theorem foldTransferOp_apply (hN2 : 2 ≤ N) (β : ℝ) (c : Circle)
    (x : invariantSector (N := N) β c) :
    ((foldTransferOp hN2 β c x : osSpace (N := N) (haarProb Circle) circleRep β))
      = transferOp (N := N) (haarProb Circle) circleRep hN2 circleRep_continuous β x.1 :=
  rfl

/-- The folded form-gap: on the invariant sector, the SAME δ
as the ambient form-gap. The sector's vectors are a subset
of the vectors the landed form-gap quantifies over, so the
bound inherits with nothing changed — no new bound is
claimed. -/
theorem folded_form_gap_circle (hN2 : 2 ≤ N) (hN : Even N)
    (hβ : 0 < β) (δ : ℝ) (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N) (haarProb Circle) circleRep β))
    (c : Circle)
    (x : invariantSector (N := N) β c)
    (hx : inner ℂ x (⟨osVacuum (μG := haarProb Circle) (ρ := circleRep) (N := N)
        circleRep_continuous Nat.zero_lt_one β,
        osVacuum_mem_invariantSector β c⟩ : invariantSector β c) = 0) :
    (inner ℂ x (foldTransferOp hN2 β c x)).re
      ≤ (1 - δ) * ‖x‖ ^ 2 := by
  have hx' : inner ℂ x.1 (osVacuum (haarProb Circle) circleRep
      circleRep_continuous zero_lt_one β) = 0 := by
    have h := hx
    rw [Submodule.coe_inner] at h
    exact h
  have hfg := transferOp_form_gap_circle hN2 β hN hβ δ hgap b x.1 hx'
  rw [Submodule.coe_inner, foldTransferOp_apply, ← Submodule.norm_coe]
  exact hfg

/-- The folded spectral correspondence: the landed
correspondence, restricted to the invariant sector. A domain
vector whose underlying slice vector lies in the sector
satisfies the same two-sided bound — the discharged
correspondence already quantifies over all domain vectors,
so the sector's vectors inherit it directly. The sector
hypothesis is carried to state the restriction; it is not
needed in the proof, and that is the inheritance. -/
theorem folded_sliceSpectralCorrespondence (hN2 : 2 ≤ N) (hN : Even N)
    (hpos : SliceHPosOne (haarProb Circle) circleRep hN2 circleRep_continuous β)
    (hβ : 0 < β) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N) (haarProb Circle) circleRep β))
    (c : Circle)
    (x : ↥(sliceHamOperatorDomain (haarProb Circle) circleRep hN2
      circleRep_continuous hN β hpos))
    (_hxsec : sliceWeldCompleted hN2 hN β hpos (x.1).1 ∈ invariantSector (N := N) β c)
    (hx : ‖x.1‖ = 1)
    (horth : inner ℂ x.1 (sliceBatteryVacuum (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos zero_lt_one) = 0) :
    Real.exp (- sliceBatteryEnergy (haarProb Circle) circleRep hN2
        circleRep_continuous hN β hpos x)
      ≤ (inner ℂ (x.1).1 (sliceTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos (x.1).1)).re
    ∧ (inner ℂ (x.1).1 (sliceTc (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos (x.1).1)).re
      ≤ 1 - δ :=
  sliceSpectralCorrespondence_of_transport hN2 hN β hpos hβ δ hδ0 hδ1 hgap b x hx horth

end FoldGap

end ThetLogos
