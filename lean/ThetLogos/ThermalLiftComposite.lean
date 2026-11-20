import Mathlib.Tactic
import ThetLogos.ThermalLiftPin

/-!
# ThetLogos.ThermalLiftComposite — THERMAL LIFT, brick LIFT-1

**The potential of a gradient.** The profiled composite,
frozen by `ThermalLiftPin` (LIFT-0a) and proved here: the
profiled thermal potential solves the projected Poisson
problem for the profiled source; its field and flow factor
through the contrast; and at a constant profile the whole
composite *is* the landed `ThermalSourceComposite`
composite, on the nose.

Every proof routes through the landed channel's own
theorems (`PoissonTotalMassBlindness`) and the landed
constant-profile hinge (`gibbsProb_eq_profWeight_const`) —
no constant-profile identity is re-proved, and nothing is
weakened to the constant case (K-LIFT-PROFILE does not
fire: the channel's theorems are stated for an arbitrary
source `g`, so the generalization is by application, not
by new machinery).

**Kills, on the face.** K-LIFT-BLIND is this brick's
positive content: the field and flow see the contrast
alone (`profContrastForm_holds`), and the source's total
never enters. K-LIFT-EQUIL stands as cited in the pin:
at a constant *source* the field is zero — here, at a
constant profile the composite reduces to the landed one,
whose ceiling theorems say exactly that. K-LIFT-COSTUME
does not fire: source and potential remain independently
defined; the only bridge used is the Poisson inversion
theorem `laplacianOp_poissonPotential`.

**Fences.** Statics only; no response, no test body, no
universality, no attraction sign is stated. Dial-ineligible
by SR-5 inheritance: **Dial 2 = 0 under every outcome.
NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **The constant-profile hinge.** The profiled source
at a constant profile is the landed thermal source:
T1's two Gibbs dialects agree on the nose
(`gibbsProb_eq_profWeight_const`), so the profiled
construction contains the landed one as its
constant-profile face. -/
theorem profThermalSource_const (β : ℝ) (E : V → ℝ) :
    profThermalSource (fun _ => β) E = thermalSource E β := by
  funext i
  show profWeight (fun _ => β) E i * E i = thermalSource E β i
  rw [thermalSource_apply, gibbsProb_eq_profWeight_const]

/-- **LIFT-1, the Poisson form (frozen target, proved).**
The profiled composite potential solves the projected
problem for the profiled source. The bare form
`L φ = profThermalSource β E` is not asserted — it is
false whenever the source's total is nonzero; the
channel sees the contrast (K-LIFT-BLIND). -/
theorem profPoissonForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) :
    ProfPoissonForm w hw hw0 hpos β E :=
  laplacianOp_poissonPotential w hw hw0 hpos
    (profThermalSource β E)

/-- **LIFT-1, the contrast form (frozen target, proved).**
Two profiled sources with the same mean-subtraction have
the same field and the same flow: the outputs factor
through the contrast alone. -/
theorem profContrastForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β β' : V → ℝ)
    (E E' : V → ℝ) :
    ProfContrastForm w hw hw0 hpos β β' E E' := by
  intro h
  exact ⟨poissonField_eq_of_meanSub_eq w hw hw0 hpos _ _ h,
    poissonFlow_eq_of_meanSub_eq w hw hw0 hpos _ _ h⟩

/-- **Reduction, potential.** At a constant profile the
profiled potential is the landed composite potential. -/
theorem profThermalPotential_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : ℝ) (E : V → ℝ) :
    profThermalPotential w hw hw0 hpos (fun _ => β) E
      = thermalPotential w hw hw0 hpos E β :=
  congrArg (poissonPotential w hw hw0 hpos)
    (profThermalSource_const β E)

/-- **Reduction, field.** At a constant profile the
profiled field is the landed composite field. -/
theorem profThermalField_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : ℝ) (E : V → ℝ) :
    profThermalField w hw hw0 hpos (fun _ => β) E
      = thermalField w hw hw0 hpos E β :=
  congrArg (poissonField w hw hw0 hpos)
    (profThermalSource_const β E)

/-- **Reduction, flow.** At a constant profile the
profiled flow is the landed composite flow. -/
theorem profThermalFlow_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : ℝ) (E : V → ℝ) :
    profThermalFlow w hw hw0 hpos (fun _ => β) E
      = thermalFlow w hw hw0 hpos E β :=
  congrArg (poissonFlow w hw hw0 hpos)
    (profThermalSource_const β E)

/-- **LIFT-1, the reduction form (frozen target,
proved).** Potential, field and flow at a constant
profile are the landed composite's, on the nose. -/
theorem profReductionForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : ℝ) (E : V → ℝ) :
    ProfReductionForm w hw hw0 hpos β E :=
  ⟨profThermalPotential_const w hw hw0 hpos β E,
    profThermalField_const w hw hw0 hpos β E,
    profThermalFlow_const w hw hw0 hpos β E⟩

end ThetLogos
