import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjPin
import ThetLogos.DialOnePiUFamily

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneConjugationCounterexample

namespace ThetLogos.DialOneGradeRConjReadback

/-!
# ThetLogos.DialOneGradeRConjReadback — GRADE R: preservation at `pi1`, read back

The pin `ThetLogos.DialOneGradeRConjPin` posed
`PreservationAtPi1ConjU` — the statement
`DialOneStrengthenedFam (conjRep conjU pi1)` — as a
named Prop and deliberately did NOT assert it: its T1
form waited on the corrected D1-PIU-STR brick, whose
headline is `DialOneStrengthenedFam piU`. That brick
has now landed in the tree
(`ThetLogos.DialOnePiUFamily.strengthened_piU`,
K-CLS-1a-STR fired by it), so the sequenced step the
pin marked closes here, by the pin's own read-back
`piU_eq_conjRep` (`piU = conjRep conjU pi1`, an `rfl`
read-back), with no further content: one rewrite.

This is preservation's first T1 instance — at the one
exhibited pair (`conjU`, `pi1`). The class-level
`PreservationQ` remains OPEN: no class-wide proof is
claimed here, and no counterexample to preservation
itself is exhibited or claimed anywhere in the run.
The two located gaps stand as the content module
`ThetLogos.DialOneGradeRConj` priced them — (α)
reality, since closed negatively by
`ThetLogos.DialOneGradeRReality.reality_does_not_follow`
(the class does not force `IsRealMat`; the hypothesis
in `dialOneBase_preserved` is essential), and (β) the
pulled projection clauses, an arithmetic fact per
exhibited pair. `PiAntiOrbitQ` is stated in the pin
and was not attempted in this run. The quotient
classification stays L+ / FRONTIER.

## Fences

NO CLAIM. Dial 1 = 0: a classification grade derives
no measured number. No `axiom` declarations and no
sorrys in this module.
-/

/-- **Preservation at `pi1` under `conjU` — the pin's
sequenced corollary, CLOSED.** The pin's
`PreservationAtPi1ConjU`, proved by rewriting along the
pin's `piU_eq_conjRep` read-back to the landed
`ThetLogos.DialOnePiUFamily.strengthened_piU`. -/
theorem preservationAtPi1ConjU :
    ThetLogos.DialOneGradeRConjPin.PreservationAtPi1ConjU := by
  unfold ThetLogos.DialOneGradeRConjPin.PreservationAtPi1ConjU
  rw [← ThetLogos.DialOneGradeRConjPin.piU_eq_conjRep]
  exact ThetLogos.DialOnePiUFamily.strengthened_piU

/-- **The full preservation instance at the exhibited
pair (`conjU`, `pi1`)**: the conjugating matrix is in
the class (the pin's `conjU_centralizing`), the point
is in the strengthened family (the landed
`ThetLogos.DialOneGammaFamilyChecks.strengthened_pi1`),
and its conjugate is in the strengthened family
(`preservationAtPi1ConjU` above). The three components
of the `PreservationQ` instance at this pair, bundled
at full rank. -/
theorem preservation_instance_pi1_conjU :
    ThetLogos.DialOneGradeRConjPin.CentralizingClass
        ThetLogos.DialOneConjugationCounterexample.conjU
      ∧ DialOneStrengthenedFam pi1
      ∧ ThetLogos.DialOneGradeRConjPin.PreservationAtPi1ConjU :=
  ⟨ThetLogos.DialOneGradeRConjPin.conjU_centralizing,
   ThetLogos.DialOneGammaFamilyChecks.strengthened_pi1,
   preservationAtPi1ConjU⟩

end ThetLogos.DialOneGradeRConjReadback

#print axioms ThetLogos.DialOneGradeRConjReadback.preservationAtPi1ConjU
#print axioms ThetLogos.DialOneGradeRConjReadback.preservation_instance_pi1_conjU
