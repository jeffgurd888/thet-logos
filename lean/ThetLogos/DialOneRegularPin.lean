import Mathlib.Tactic
import ThetLogos.DialOneExtraction

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

namespace ThetLogos.DialOneRegularPin

/-!
# ThetLogos.DialOneRegularPin — the regular-class re-pose of Grade W, REGISTERED

Governing text: the W′ scoping memo
(`routeb-general-scratch/scoping-cls1ab-2026-11-02.md`
§2.3/§3), over the CLS-0 pin
(`DialOneClassificationPin`), CLS-1
(`DialOneExtraction`), CLS-3c-A
(`DialOneAntiparticleBase`), and the fired K-CLS-1a
(`DialOneConjugationCounterexample`). This brick is the
STATEMENT PIN only: it freezes `DialOneRegular`,
`WeightRealizable'`, and `WeightQuestionW'` exactly as
scoped, plus the one read-back
`regular_has_weights`. **NO CLAIM; Dial 1 = 0; all
dials 0/4. A pin is not a derivation: parts of any
official statement closed by this module: 0.**

## (a) THE CORRECTION to the memo — the memo's status sentence is SUPERSEDED

The memo's §3 status sentence ("`WeightQuestionW`
remains open") is **SUPERSEDED**. CLS-3c-A answered the
original `WeightQuestionW` **YES**: `piAnti` lies in
`DialOneStrengthenedFam`, is not `pi1`, and carries the
common weights (`weightQuestionW_piAnti` in
`DialOneAntiparticleBase.lean`). W′ is therefore the
**regular-class refinement of an ANSWERED question**,
not the working pose of an open one. What W′ still asks
that CLS-3c-A did not settle: whether a non-π₁
strengthened point carrying the common weights is
REGULAR (`DialOneRegular`) — `piAnti` is the standing
candidate, and its `ExtractionLemma` is the unsettled
conjunct.

## (b) K-CLS-1a has FIRED since the memo

K-CLS-1a has **FIRED** since the memo
(`DialOneConjugationCounterexample.lean`): `DialOneBase`
does **NOT** imply `DiagLift` — `DiagLift` is NOT a base
consequence. `DialOneRegular`'s `ExtractionLemma`
conjunct is therefore known-genuine extra input, not
decoration. Cross-sign diagonality is T1
(`DialOneCrossSign.lean`), so the diagonality content
of `ExtractionLemma` is **within-sign only**.

## (c) Kills and status, registered at full rank

**K-CLS-1 remains armed against the ORIGINAL pose**;
extraction over the regular class is **FULL** (CLS-1:
`extraction_of_extractionLemma` — every `π` with
`DialOneRegular π` admits a weight vector, recorded
below as `regular_has_weights`).

**K-W′-REG (kill registered for W′).** If
`¬ ExtractionLemma piAnti` is ever proved, the `piAnti`
route to W′ dies at full rank — W′ itself reopens on
other witnesses; it is **not** killed.

**NO CLAIM; Dial 1 = 0; dials 0/4.**
-/

/-- **The regular class** (the memo's §2.3 re-pose,
frozen): base ∧ the joint extraction lemma — one joint
primitive determinant-one direction carrying
diagonality and differentiability at `0` together
(`ExtractionLemma`, CLS-1). By (b) on the face, the
second conjunct is genuine extra input: K-CLS-1a fired,
so it does not follow from the first. -/
def DialOneRegular (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    Prop :=
  DialOneBase π ∧ ExtractionLemma π

/-- **Grade W′, weight realizability over the regular
class, as a statement**: the integer vector `w` is
realized at Grade W′ iff some representation in the
landed strengthened set (`DialOneStrengthenedFam`) that
is also regular (`DialOneRegular`) carries it, in the
sense of `weightAt`. This names the image of the weight
relation over the strengthened regular class; it asserts
that no particular `w` is or is not realized. -/
def WeightRealizable' (w : Fin 32 → ℤ) : Prop :=
  ∃ π, DialOneStrengthenedFam π ∧ DialOneRegular π
    ∧ weightAt π w

/-- **The Grade-W′ question, as a statement**: whether
ANY regular representation in the strengthened set
other than π₁ carries the common matrix's weights, i.e.
`∃ π, DialOneStrengthenedFam π ∧ DialOneRegular π ∧
π ≠ pi1 ∧ weightAt π commonWeightVector`. Per (a) on
the face, this is the regular-class refinement of the
original `WeightQuestionW`, which CLS-3c-A already
answered YES by `piAnti`; the open content here is
exactly the regularity of such a point, with `piAnti`
the standing candidate. This pin states the question
and asserts neither it nor its negation. -/
def WeightQuestionW' : Prop :=
  ∃ π, DialOneStrengthenedFam π ∧ DialOneRegular π
    ∧ π ≠ pi1 ∧ weightAt π commonWeightVector

/-- **Read-back — extraction over the regular class is
FULL (CLS-1)**: every regular `π` admits a weight
vector. Immediate from the landed
`extraction_of_extractionLemma`: a `DialOneRegular π`
is exactly the pair of hypotheses that headline
consumes. -/
theorem regular_has_weights :
    ∀ π, DialOneRegular π → ∃ v, weightAt π v :=
  fun π h => extraction_of_extractionLemma π h.1 h.2

end ThetLogos.DialOneRegularPin
