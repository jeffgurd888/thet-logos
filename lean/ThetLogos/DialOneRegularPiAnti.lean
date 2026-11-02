import Mathlib.Tactic
import ThetLogos.DialOneRegularPin
import ThetLogos.DialOneAntiparticleBase

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneExtraction
open ThetLogos.DialOneRegularPin
open ThetLogos.DialOneAntiparticleChapter
open ThetLogos.DialOneAntiparticleBase

namespace ThetLogos.DialOneRegularPiAnti

/-!
# ThetLogos.DialOneRegularPiAnti — `piAnti` is regular; W′ answered YES

Governing texts: the registration pin
(`DialOneRegularPin`, freezing `DialOneRegular`,
`WeightRealizable'`, `WeightQuestionW'` with the
correction, the fired K-CLS-1a, and the registered kill
K-W′-REG on its face), CLS-1 (`DialOneExtraction`), and
CLS-3c-A (`DialOneAntiparticleBase`).

## Verdict (T1 here)

**`WeightQuestionW'` is answered YES by `piAnti`.**
The one conjunct CLS-3c-A did not settle —
`ExtractionLemma piAnti` — is proved here at the joint
`(3, 1)`, transported from `extractionLemma_pi1` at the
joint `(3, -1)`: `piAnti (u1ParamGen 3 1 t) =
pi1 (u1ParamGen 3 (-1) t)` as matrices, by
`piAnti_eq_pi1_colourTwist` and the landed β-flip
`colourTwist_u1ParamGen`, and every clause of the
extraction lemma — determinant, diagonality of the
lifted product, differentiability at `0` of its
diagonal entries — is that matrix equality read through
the landed π₁ facts. Hence `DialOneRegular piAnti`
(base landed in CLS-3c-A), and W′ assembles from the
landed strengthened family, `piAnti_ne_pi1`, and the
landed common weights.

**K-W′-REG does not fire**: its trigger was a proof of
`¬ ExtractionLemma piAnti`; the opposite is proved
here, so the `piAnti` route to W′ stands, and W′ with
it. **K-CLS-1 remains armed against the ORIGINAL
pose**, untouched by anything here.

**NO CLAIM; Dial 1 = 0; all dials 0/4. Classification
data only: parts of any official statement closed by
this module: 0.**
-/

/-- **The transport matrix equality**: along the
flipped joint, `piAnti`'s family value IS π₁'s — by
`piAnti_eq_pi1_colourTwist` (CLS-3c-A: `piAnti =
pi1 ∘ colourTwist`) and the landed β-flip
`colourTwist_u1ParamGen` (`colourTwist` flips only β
in `u1ParamGen`). -/
theorem piAnti_family_eq_pi1 (t : ℝ) :
    piAnti (u1ParamGen 3 1 t) = pi1 (u1ParamGen 3 (-1) t) := by
  rw [piAnti_eq_pi1_colourTwist, colourTwist_u1ParamGen]

/-- **The lifted products agree** along the two joints:
`liftedProd` is a def — `π`'s matrix times `piOp` of it
— so the matrix equality of
`piAnti_family_eq_pi1` transports by congruence. -/
theorem liftedProd_piAnti_eq_pi1 (t : ℝ) :
    liftedProd piAnti 3 1 t = liftedProd pi1 3 (-1) t := by
  unfold liftedProd
  rw [piAnti_family_eq_pi1 t]

/-- **HEADLINE 1 — `ExtractionLemma piAnti`**, at the
joint `(3, 1)`, transported from `extractionLemma_pi1`
at `(3, -1)` (CLS-1, §7): the determinant clause by the
transport equality and the landed `pi1_det_gen`
(`-4 * 3 + -12 * -1 = 0`); the diagonality clause by
the lifted-product equality and the landed
`pi1_liftedProd_diag`; the differentiability clause by
the lifted-product equality, the landed
`pi1_liftedProd_entry` (each diagonal entry is a pure
character), and the landed `differentiableAt_exp_lin`. -/
theorem extractionLemma_piAnti : ExtractionLemma piAnti := by
  refine ⟨3, 1, by decide, ?_, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
    rw [piAnti_family_eq_pi1 t, pi1_det_gen, h0]
    simp
  · intro t s s' h
    rw [liftedProd_piAnti_eq_pi1 t]
    exact pi1_liftedProd_diag t s s' h
  · intro s
    have hfun : (fun t => liftedProd piAnti 3 1 t s s)
        = (fun t : ℝ => Complex.exp
            ((((pi1AVal s.val * 3 + pi1BVal s.val * (-1))
                + (pi1AVal (partner s).val * 3
                  + pi1BVal (partner s).val * (-1)) : ℤ) : ℂ)
              * ((t : ℂ) * Complex.I))) := by
      funext t
      rw [liftedProd_piAnti_eq_pi1 t]
      exact pi1_liftedProd_entry t s
    rw [hfun]
    exact differentiableAt_exp_lin _

/-- **HEADLINE 2 — `DialOneRegular piAnti`**: the
landed base (`dialOneBase_piAnti`, CLS-3c-A) ∧
Headline 1. This is the conjunct CLS-3c-A left
unsettled, now discharged. -/
theorem dialOneRegular_piAnti : DialOneRegular piAnti :=
  ⟨dialOneBase_piAnti, extractionLemma_piAnti⟩

/-- **HEADLINE 3 — `WeightQuestionW'`, answered YES**:
assembled per the pin's exact def form from the landed
strengthened family (`strengthenedFam_piAnti`,
CLS-3c-A), Headline 2, the landed `piAnti_ne_pi1`
(CLS-3c), and the landed common weights
(`weightAt_piAnti_common`, CLS-3c-A). -/
theorem weightQuestionW'_piAnti : WeightQuestionW' :=
  ⟨piAnti, strengthenedFam_piAnti, dialOneRegular_piAnti,
   ThetLogos.DialOneAntiparticleChapter.piAnti_ne_pi1,
   weightAt_piAnti_common⟩

end ThetLogos.DialOneRegularPiAnti
