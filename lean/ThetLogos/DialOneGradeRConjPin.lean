import Mathlib.Tactic
import ThetLogos.DialOneSeatTiePin
import ThetLogos.DialOneGammaTracePin
import ThetLogos.DialOneGammaFamilyPin
import ThetLogos.DialOneConjugationCounterexample
import ThetLogos.DialOneAntiparticleChapter

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin

namespace ThetLogos.DialOneGradeRConjPin

/-!
# ThetLogos.DialOneGradeRConjPin — GRADE R, R-CONJ road: the gauge class, PINNED

Governing texts: the Q1 paper
(`q1-sep-audit-reg-scope-2026-11-06.md`) Part C, as
corrected by its appended CORRECTION RECORD
(2026-11-07 ~19:40 EST), and the re-scope note
`grade-r-conj-rescope-2026-11-07.md`. Jeff fired the
Grade R run 2026-11-07 20:07 EST ("run grade R"); the
bounded reading is the R-CONJ road only. R-EQ and R-W
stand closed at T1 (re-verified this run:
`DialOneAntiparticleBase.strengthenedFam_piAnti` with
`DialOneAntiparticleChapter.piAnti_ne_pi1`;
`DialOneAntiparticleBase.weightQuestionW_piAnti`) and
are NOT re-opened here.

This is the STATEMENT PIN (step S of the paper's
pricing). It gives the R-CONJ road its landed
vocabulary: the centralizing class as a predicate, the
sandwich conjugation, the gauge relation, `conjU`'s
membership in the class (assembled from landed
citations — the one proved theorem of this pin), and
the road's two questions as named Props:
`PreservationQ` and `PiAntiOrbitQ`, plus the sequenced
corollary-in-waiting `PreservationAtPi1ConjU`.

**This pin asserts NONE of its three question-Props.**
They enter as Props only — never as axioms, never as
theorems. There are no `axiom` declarations in this
module and no sorrys.

## The road's kill condition, on the face

If a counterexample is ever exhibited — a class member
`U`, a strengthened-set member `π`, with
`conjRep U π` OUTSIDE the strengthened set — then
`PreservationQ` is FALSE, the R-CONJ quotient on the
strengthened set is not well-defined, and the R-CONJ
classification road dies at the well-definedness gate.
No such counterexample is landed or exhibited here.

## The two located gaps (re-scope §4)

Transport under a general class member is obstructed at
exactly two points, both carried openly by the content
module `DialOneGradeRConj`: **(α)** the base's star
clause transports iff `Uᴴ = Uᵀ` (entrywise reality),
which is not among conditions (a)/(b)/(c) and is not
known to follow from them (`conjU` is real, landed —
`conjU_conjTranspose` — but as a fact about its
entries, not as a class consequence); **(β)** the
projection clauses `C3lep` / `C3col` / `FeR` transport
iff the corresponding PULLED clauses (against
`Uᵀ * P * U`) hold at the original point — an arithmetic
fact per (U, π) pair, not a consequence of (a)/(b)/(c).
`C3` transports in full; the base transports modulo (α).

## Fences

NO CLAIM. Dial 1 = 0: a classification grade derives
no measured number. The quotient classification itself
is L+ / FRONTIER and is not stated, priced, or
attempted here.
-/

/-- **The centralizing class** (Grade R, R-CONJ): the
unitaries of the corpus's landed sandwich form
(transpose-unitarity) satisfying exactly the transport
conditions (a)/(b)/(c) of the Q1 paper's Part C — the
conditions `DialOneConjugationCounterexample` proved
for `conjU`: (a) commutation with `gammaF`,
(b) the `piOp` intertwining in transport form
`piOp U = Uᵀ`, (c) commutation with the Dirac data
`DF_oneGen` at generic (universally quantified real)
Yukawas. -/
def CentralizingClass (U : Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  U * Uᵀ = 1 ∧ Uᵀ * U = 1
    ∧ gammaF * U = U * gammaF
    ∧ piOp U = Uᵀ
    ∧ ∀ Ynu Ye Yu Yd : ℝ,
        DF_oneGen Ynu Ye Yu Yd * U = U * DF_oneGen Ynu Ye Yu Yd

/-- **Sandwich conjugation of a representation** by a
matrix `U`, in the landed form (`piU` is this at
`conjU`, `pi1` — see the read-back below). -/
def conjRep (U : Matrix (Fin 32) (Fin 32) ℂ)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    AF → Matrix (Fin 32) (Fin 32) ℂ :=
  fun a => U * π a * Uᵀ

/-- Read-back: the landed `piU` is visibly the sandwich
conjugate of `pi1` by `conjU`. -/
theorem piU_eq_conjRep :
    ThetLogos.DialOneConjugationCounterexample.piU
      = conjRep ThetLogos.DialOneConjugationCounterexample.conjU pi1 :=
  rfl

/-- **The R-CONJ gauge relation**: `π ~ σ` iff `σ` is
the sandwich conjugate of `π` by some member of the
centralizing class. (Posed as a relation only; that it
is an equivalence on the strengthened set is part of
what the gated quotient road would have to face —
group closure of the class and preservation,
`PreservationQ` below, among them.) -/
def GaugeConj (π σ : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∃ U, CentralizingClass U ∧ σ = conjRep U π

/-- **Entrywise reality** of a matrix, in the form the
base's star clause turns on (gap (α) of the header):
`Uᴴ = Uᵀ`. A named predicate, NOT a class condition —
the class Jeff picked is (a)/(b)/(c) above, and whether
reality follows from them is open. -/
def IsRealMat (U : Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  Uᴴ = Uᵀ

/-- **`conjU` belongs to the centralizing class** — the
positive half, assembled from the landed citations of
`ThetLogos.DialOneConjugationCounterexample`:
unitarity (`conjU_mul_transpose`, `conjU_transpose_mul`),
(a) `conjU_gamma_comm`, (b) `piOp_conjU`,
(c) `conjU_df_comm`. -/
theorem conjU_centralizing :
    CentralizingClass ThetLogos.DialOneConjugationCounterexample.conjU :=
  ⟨ThetLogos.DialOneConjugationCounterexample.conjU_mul_transpose,
   ThetLogos.DialOneConjugationCounterexample.conjU_transpose_mul,
   ThetLogos.DialOneConjugationCounterexample.conjU_gamma_comm,
   ThetLogos.DialOneConjugationCounterexample.piOp_conjU,
   ThetLogos.DialOneConjugationCounterexample.conjU_df_comm⟩

/-- **PRESERVATION — the R-CONJ road's first question,
as a named Prop. NOT asserted.** Is the strengthened
set closed under conjugation by every member of the
centralizing class? The one exhibited pair (`conjU`,
`pi1`) preserves (the Q1 correction record's flip; its
T1 form is the corrected D1-PIU-STR brick, in its own
lane). The class-level statement is OPEN, obstructed at
gaps (α) and (β) of the header. If it is false, the
road's kill condition (header) fires. -/
def PreservationQ : Prop :=
  ∀ (U : Matrix (Fin 32) (Fin 32) ℂ)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ),
    CentralizingClass U → DialOneStrengthenedFam π
      → DialOneStrengthenedFam (conjRep U π)

/-- **The piAnti orbit question (step S–M), as a named
Prop. NOT asserted.** Is `piAnti` gauge-conjugate to
`pi1` under the centralizing class? OPEN (the paper's
C.1: `piAnti` is a toggle-type point; no conjugating
unitary is landed; its Grade T exclusion was by
clauses, not by conjugacy). -/
def PiAntiOrbitQ : Prop :=
  ∃ U, CentralizingClass U
    ∧ ThetLogos.DialOneAntiparticleChapter.piAnti = conjRep U pi1

/-- **The preservation-at-`pi1` corollary-in-waiting,
as a named Prop. NOT asserted in this pin.** By the
`piU_eq_conjRep` read-back this is
`DialOneStrengthenedFam piU`. It is the single
sequenced step that closes after the corrected
D1-PIU-STR brick (headline: `DialOneStrengthenedFam
piU`) is integrated: one rewrite by the read-back, no
further content. Sequenced, marked, and deliberately
left open here — this pin does not import from another
lane's worktree. -/
def PreservationAtPi1ConjU : Prop :=
  DialOneStrengthenedFam
    (conjRep ThetLogos.DialOneConjugationCounterexample.conjU pi1)

end ThetLogos.DialOneGradeRConjPin
