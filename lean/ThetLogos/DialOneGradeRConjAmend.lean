import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjPin
import ThetLogos.DialOneGradeRConj
import ThetLogos.DialOneGradeRReality

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin

namespace ThetLogos.DialOneGradeRConjAmend

/-!
# ThetLogos.DialOneGradeRConjAmend — GRADE R: the class, AMENDED (Jeff's decision)

Jeff's decision, 2026-11-07 20:45 EST, in his words:
**"Amend the class: add the reality condition."**

## Form of the amendment: an adoption, not a rewrite

The pin's `CentralizingClass` — transpose-unitarity
plus conditions (a)/(b)/(c), exactly as the Q1 paper's
Part C picked it — stands UNTOUCHED, and so does the
(α) verdict against it: `DialOneGradeRReality`'s
`reality_does_not_follow` (reality does not follow
from (a)/(b)/(c); the witness `U0` is a non-real class
member, proved entrywise). That verdict is the
historical record, and the amendment's exclusion of
`U0` is meaningful only against the original class.

What this module does is adopt the OPERATIVE gauge
class going forward: `RealCentralizingClass`, the
original class with the reality condition
(`IsRealMat U`, i.e. `Uᴴ = Uᵀ`) adjoined as a fourth
condition — a NEW definition, definitionally the
conjunction `CentralizingClass U ∧ IsRealMat U`.

## What the amendment discharges, and what it does not

* It discharges gap (α) BY ADOPTION: on the amended
  class, the content module's capstone upgrades to
  `strengthened_preserved_of_real_pulled` — preservation
  reduces to the pulled clauses (gap (β)) ALONE, the
  reality hypothesis being read off the amended
  membership definitionally. This is the theorem that
  would not assemble on the old class.
* It leaves gap (β) exactly where it stood: the pulled
  clauses are an arithmetic fact per (U, π) pair, not
  a consequence of the class conditions, amended or
  not. `PreservationQReal` below is therefore still
  OPEN, and is asserted nowhere in this module.
* The orbit question likewise carries over open:
  `PiAntiOrbitQReal` is stated, not asserted.
* `U0`'s preservation question loses its road
  meaning: `U0` sits OUTSIDE the operative class now
  (`U0_not_realCentralizing` below), so whether it
  preserves the strengthened set no longer bears on
  the R-CONJ road as amended.

## The two membership facts

`conjU` — the class's exhibited member — is real
(landed, entrywise: `conjU_conjTranspose`), so it
survives the amendment: `conjU_realCentralizing`.
`U0` — the (α) witness — does not:
`U0_not_realCentralizing`. The amendment excludes
exactly the freedom the (α) lane exhibited, and
nothing landed is lost by it.

## Fences

NO CLAIM. Dial 1 = 0: a classification grade derives
no measured number. The quotient classification
itself remains L+ / FRONTIER and is not stated,
priced, or attempted here. No `axiom` declarations;
no sorrys.
-/

/-- **The amended (operative) centralizing class**:
the pin's `CentralizingClass` (transpose-unitarity +
(a)/(b)/(c)) with the reality condition adjoined, per
Jeff's 2026-11-07 decision. Definitionally the
conjunction — the original predicate is a component,
not edited. -/
def RealCentralizingClass (U : Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  CentralizingClass U ∧ IsRealMat U

/-- **`conjU` belongs to the amended class** — the
pin's `conjU_centralizing` plus `conjU`'s landed
reality (`conjU_conjTranspose`, entrywise, in
`DialOneConjugationCounterexample`). The amendment
keeps the class's exhibited member. -/
theorem conjU_realCentralizing :
    RealCentralizingClass
      ThetLogos.DialOneConjugationCounterexample.conjU :=
  ⟨ThetLogos.DialOneGradeRConjPin.conjU_centralizing,
   ThetLogos.DialOneConjugationCounterexample.conjU_conjTranspose⟩

/-- **`U0` does NOT belong to the amended class** —
the (α) witness is in the original class
(`U0_centralizing`) but is not real (`U0_not_real`),
so the amendment excludes exactly it. -/
theorem U0_not_realCentralizing :
    ¬ RealCentralizingClass ThetLogos.DialOneGradeRReality.U0 :=
  fun h => ThetLogos.DialOneGradeRReality.U0_not_real h.2

/-- **THE CAPSTONE UPGRADE — preservation on the
amended class, modulo gap (β) alone.** The content
module's capstone
(`DialOneGradeRConj.strengthened_preserved_of_reality_pulled`)
with its two hypotheses `CentralizingClass U` and
`IsRealMat U` replaced by the single amended
membership `RealCentralizingClass U`; the three
pulled-clause hypotheses are carried EXACTLY as the
capstone carries them. The reality hypothesis is
discharged definitionally from the amended
membership. This is the form that would not assemble
on the old class, where the reality hypothesis was
essential and underivable (gap (α), closed negatively
in `DialOneGradeRReality`). -/
theorem strengthened_preserved_of_real_pulled
    {U : Matrix (Fin 32) (Fin 32) ℂ}
    (hU : RealCentralizingClass U)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneStrengthenedFam π)
    (hlep : ∀ α β : ℤ,
      Matrix.trace (gammaF * (Uᵀ * lepProj * U) * π (u1Gen α β)) = 0)
    (hcol : ∀ (c : Fin 3) (α β : ℤ),
      Matrix.trace (gammaF * (Uᵀ * colProj c * U) * π (u1Gen α β)) = 0)
    (heR : ∀ α β : ℤ,
      Matrix.trace (gammaF * (Uᵀ * eRProj * U) * π (u1Gen α β)) = 0) :
    DialOneStrengthenedFam (conjRep U π) :=
  ThetLogos.DialOneGradeRConj.strengthened_preserved_of_reality_pulled
    hU.1 hU.2 π h hlep hcol heR

/-- **The amended R-CONJ gauge relation**: `π ~ σ`
iff `σ` is the sandwich conjugate of `π` by some
member of the AMENDED class (`RealCentralizingClass`).
The restriction of the pin's `GaugeConj` to real class
members. (Posed as a relation only, as in the pin.) -/
def GaugeConjReal (π σ : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∃ U, RealCentralizingClass U ∧ σ = conjRep U π

/-- **PRESERVATION on the amended class — the road's
first question, restated. NOT asserted.** Is the
strengthened set closed under conjugation by every
member of the amended class? The amendment removed
gap (α) from its obstruction; gap (β) — the pulled
clauses, per (U, π) arithmetic — remains, so this is
still OPEN. If a counterexample is ever exhibited
against the amended class, the road's kill condition
fires as in the pin's header. -/
def PreservationQReal : Prop :=
  ∀ (U : Matrix (Fin 32) (Fin 32) ℂ)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ),
    RealCentralizingClass U → DialOneStrengthenedFam π
      → DialOneStrengthenedFam (conjRep U π)

/-- **The piAnti orbit question on the amended class.
NOT asserted.** Is `piAnti` gauge-conjugate to `pi1`
by a member of the amended (real) class? OPEN, as it
was on the original class: no conjugating unitary is
landed, real or otherwise. -/
def PiAntiOrbitQReal : Prop :=
  ∃ U, RealCentralizingClass U
    ∧ ThetLogos.DialOneAntiparticleChapter.piAnti = conjRep U pi1

end ThetLogos.DialOneGradeRConjAmend
