import Mathlib.Tactic
import ThetLogos.DialOneGammaFamilyPin
import ThetLogos.DialOneGammaFamilyChecks

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaFamilyPin

namespace ThetLogos.DialOneClassificationPin

/-!
# ThetLogos.DialOneClassificationPin — CLS-0: the Dial-1 classification, REGISTERED

Governing text: the next-rotation scoping
(`whitepaper/next-rotation-scoping-2026-11-01.md`, Lane 1)
CLS-0 entry, over the LANDED Dial-1 record: base + C3 kills
forcing (D1-C3 checks), base + C3 + clean family excludes
every toggle compensator (`toggle_exclusion`,
`DialOneGammaFamilyChecks`), and the classification of the
strengthened set's representations is the honest open
frontier. This brick is the STATEMENT PIN only: the
definitions and question Props below, the K-CLS-0 costume
fence on the face, and nothing else. **This pin asserts NO
classification result. NO CLAIM; Dial 1 = 0; all dials
0/4. A pin is not a derivation: parts of any official
statement closed by this module: 0.**

## The three grades — never conflated

The classification question is frozen here in three
distinct grades. Any later dossier, brick, or public
sentence that merges them misreads this pin at full rank.

* **Grade W — weight realizability** (formalized below):
  the image of the weight relation over representations
  satisfying the landed strengthened set
  `DialOneStrengthenedFam` (base ∧ C3 ∧ clean family, from
  `DialOneGammaFamilyPin`). The Grade-W target is
  `commonWeightVector`, the table's weight vector. The
  open question is pinned as `WeightQuestionW`: does any
  `π ≠ pi1` in the strengthened set carry the common
  matrix's weights? π₁ itself realizes the target (the
  trivial point of the image); the open content is
  exclusively the non-π₁ realizability. **OPEN.**

* **Grade T — toggle-orbit** (formalized below, in record
  form): whether any toggle of π₁, in the three landed
  toggle families, lies in the strengthened set off π₁
  itself (`ToggleQuestion`). **Grade T is already decided
  negatively at T1 by the landed checks:
  `ThetLogos.DialOneGammaFamilyChecks.toggle_exclusion`
  puts π₁ in `DialOneStrengthenedFam` and
  `ThetLogos.HyperchargeForcing.piFlip`, `piDouble`, and
  every `ThetLogos.DialOneGammaFamilyChecks.piSwap c`
  outside it, so `ToggleQuestion` is FALSE.** That decided
  status is recorded here, on the face, so nobody re-opens
  Grade T as if it were live: this pin states the question
  in record form only and proves nothing about it — the
  decision lives in the checks module, cited, never
  re-derived here. The general toggle notion (an arbitrary
  partner-closed flipped-seat set, a group action on the
  toggles) is CLS-2's to widen; the record form below is
  deliberately exactly the three landed families.

* **Grade R — representations up to equivalence** (PROSE
  ONLY — no formal seat in this module): classify the
  strengthened set's representations themselves up to an
  equivalence. **The equivalence notion is UNCHOSEN and
  the grade is UNPRICED.** The scoping's candidates stand
  unnamed by any definition here: literal equality of
  functions (finest; Grade W is its shadow), conjugation
  by a unitary commuting with γ_F, J/`piOp`, and the Dirac
  data (the physical gauge equivalence — no landed
  vocabulary for the conjugating class as a group action),
  or weight-vector equality (coarsest; collapses to
  Grade W). Until a future scoping chooses and defends
  one, Grade R is not a question that can be stated, and
  this pin's job for Grade R is exactly to make its
  absence explicit and named: **there is deliberately no
  definition, no Prop, and no placeholder for Grade R
  anywhere in this module.** Faking a formal seat for it
  would fail this brick.

## K-CLS-0 — the costume fence, on the face

**K-CLS-0 (costume kill, pre-registered).** If any
"weight" or "classification" notion in this pin required
character-ness, sector-constancy, or diagonality of π as
a HYPOTHESIS (as opposed to a conclusion, or to the
content of an equation being asked), the pin would be a
costume and would die at full rank. The fence is kept by
construction: `weightAt` below is a RELATION, stated for
every representation `π` and every integer vector `v`,
with no hypothesis on `π` at all — not membership in any
condition set, not character-ness, not sector-constancy,
not diagonality. Its defining equation (the landed lifted
eigenvalue `(π (u1ParamGen α β t) * piOp (π (u1ParamGen
α β t))) s s` of the forcing vocabulary equals the pure
character `exp (v s · t · I)`, along an existentially
quantified primitive unimodular direction with the landed
determinant condition) is the CONTENT of the weight
claim, not a hypothesis restricting which `π` may be
asked about. A `π` for which no `v` satisfies the relation
is not excluded from anything by this pin: it simply
contributes no point to the Grade-W image. Whether every
strengthened-set `π` admits some `v` at all is the
extraction gap (CLS-1's prove-or-kill question), **OPEN
and not assumed anywhere in this pin**: baking it in
would be exactly the K-CLS-0 costume. The weight relation
is likewise defined for the toggles — `piFlip`,
`piDouble`, and the `piSwap c` are representations like
any others as far as `weightAt` is concerned — exactly as
the landed lane's lifted-eigenvalue vocabulary was.

## What this pin does not do

It proves no realizability and no non-realizability at
Grade W; it does not re-prove, weaken, or re-read
`toggle_exclusion` at Grade T; it gives Grade R no formal
content whatsoever. It freezes the question. The
B−L realizability question and non-toggle existence in
either direction are, per the governing scoping,
unpriceable today and are not smuggled in here under any
name.
-/

/-! ## Grade W — weight realizability -/

/-- **The weight relation** (Grade W's vocabulary, in the
landed lifted-eigenvalue form): `weightAt π v` holds iff
along some primitive unimodular direction `(α, β)` — the
direction existentially quantified, exactly as in
`DialOneBase`'s primitive-direction clause and
`DialOneForcing`'s quantification, with the landed
determinant condition `det = 1` — the lifted eigenvalue
of `π` at every seat `s` and every `t` is the pure
character with integer exponent `v s`:
`(π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s
= exp (v s · t · I)`. **K-CLS-0 fence**: this is a
relation over ALL `π` and ALL `v`, with no hypothesis on
`π` — no character-ness, no sector-constancy (the vector
is per-seat, `Fin 32 → ℤ`, not per-sector), no
diagonality. A `π` admitting no such `v` is a `π` whose
weights do not exist, not a `π` this pin excludes; that
extraction question is CLS-1, open, unassumed here. -/
def weightAt (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (v : Fin 32 → ℤ) : Prop :=
  ∃ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1
    ∧ (∀ t, (π (u1ParamGen α β t)).det = 1)
    ∧ ∀ (t : ℝ) (s : Fin 32),
      (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s
        = Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I)

/-- **The common weight vector** (the Grade-W target): the
table's seated lifted weights in integer form, built from
the landed vocabulary of STEP 0 of the D1-A′ pin — the
diagonal of the COMMON HYPERCHARGE MATRIX
(`commonHyperchargeMatrix`) before the cast to `ℂ`:
seat `i` carries `W i + W (partner i)`, from the landed
`ThetLogos.Track1RouteB.W` and the landed `partner`
involution. By the landed `commonHyperchargeMatrix_diag`,
its entry at every fermion seat `fermionIndex f c` is, in
`ℂ`, exactly `3 * (hypercharge f : ℂ)` — the
`(3 • hypercharge f)` entries at `fermionIndex f c`, in
the lifted form as landed. No value is re-tabulated here;
this is `commonHyperchargeMatrix`'s own diagonal, read in
`ℤ`. -/
def commonWeightVector : Fin 32 → ℤ :=
  fun i => ThetLogos.Track1RouteB.W i
    + ThetLogos.Track1RouteB.W (partner i)

/-- **Grade W — weight realizability, as a statement**:
the integer vector `w` is realized at Grade W iff some
representation in the LANDED strengthened set
(`DialOneStrengthenedFam`: base ∧ C3 ∧ clean family)
carries it, in the sense of `weightAt`. This names the
image of the weight relation over the strengthened set;
it asserts that no particular `w` is or is not realized. -/
def WeightRealizable (w : Fin 32 → ℤ) : Prop :=
  ∃ π, DialOneStrengthenedFam π ∧ weightAt π w

/-- **The Grade-W question, as a statement — OPEN**:
whether ANY representation in the strengthened set other
than π₁ carries the common matrix's weights, i.e.
`∃ π, DialOneStrengthenedFam π ∧ π ≠ pi1 ∧ weightAt π
commonWeightVector`. π₁ itself realizes
`commonWeightVector` (the trivial point of the image), so
the question is exactly the non-π₁ content of
`WeightRealizable commonWeightVector`. This pin states
the question and asserts neither it nor its negation:
Grade W is the classification's open frontier at weight
level. -/
def WeightQuestionW : Prop :=
  ∃ π, DialOneStrengthenedFam π ∧ π ≠ pi1
    ∧ weightAt π commonWeightVector

/-- Read-back: `weightAt` is visibly the registered
relation — an existentially quantified primitive
unimodular det-1 direction, the landed lifted eigenvalue
equal to the pure character at every seat and every `t`,
no hypothesis on `π`. -/
theorem weightAt_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (v : Fin 32 → ℤ) :
    weightAt π v ↔
      ∃ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1
        ∧ (∀ t, (π (u1ParamGen α β t)).det = 1)
        ∧ ∀ (t : ℝ) (s : Fin 32),
          (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s
            = Complex.exp ((v s : ℂ) * (t : ℂ) * Complex.I) :=
  Iff.rfl

/-- Read-back: `commonWeightVector` is visibly the landed
`W i + W (partner i)` diagonal of the COMMON HYPERCHARGE
MATRIX, in `ℤ`. -/
theorem commonWeightVector_unfold :
    commonWeightVector
      = fun i => ThetLogos.Track1RouteB.W i
          + ThetLogos.Track1RouteB.W (partner i) :=
  rfl

/-- Read-back: `WeightRealizable` is visibly
strengthened-set membership ∧ the weight relation. -/
theorem weightRealizable_unfold (w : Fin 32 → ℤ) :
    WeightRealizable w ↔
      ∃ π, DialOneStrengthenedFam π ∧ weightAt π w :=
  Iff.rfl

/-- Read-back: the Grade-W question is visibly the
registered non-π₁ realizability of `commonWeightVector`
over the strengthened set. -/
theorem weightQuestionW_unfold :
    WeightQuestionW ↔
      ∃ π, DialOneStrengthenedFam π ∧ π ≠ pi1
        ∧ weightAt π commonWeightVector :=
  Iff.rfl

/-! ## Grade T — toggle-orbit, record form

**Decided status, recorded on the face**: Grade T is
already decided NEGATIVELY at T1 by the landed
`ThetLogos.DialOneGammaFamilyChecks.toggle_exclusion` —
π₁ lies in `DialOneStrengthenedFam` while `piFlip`,
`piDouble`, and every `piSwap c` lie outside it — so
`ToggleQuestion` below is FALSE. This pin records that
status and states the question in record form only; it
proves nothing about Grade T and re-opens nothing. The
general toggle notion is CLS-2's to widen. -/

/-- **Toggle-of-π₁, RECORD FORM**: `π` is one of the three
landed toggle families — `piFlip` (the ν_R single flip,
`ThetLogos.HyperchargeForcing.piFlip`), `piDouble` (the
ν_R ↔ e_R double flip), or a per-colour quark swap
`ThetLogos.DialOneGammaFamilyChecks.piSwap c` for some
colour `c`. This is deliberately the record of what has
landed, NOT the general toggle notion (an arbitrary
partner-closed flipped-seat set): widening it is CLS-2's
registered work, and no sentence of this pin may be read
as a statement about toggles beyond these three families. -/
def IsToggleOfPi1 (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  π = ThetLogos.HyperchargeForcing.piFlip ∨ π = piDouble
    ∨ ∃ c, π = ThetLogos.DialOneGammaFamilyChecks.piSwap c

/-- **The Grade-T question, as a statement — ALREADY
DECIDED**: whether any toggle of π₁, in the record form
above, lies in the strengthened set off π₁ itself.
**LANDED ANSWER (T1, in
`DialOneGammaFamilyChecks.toggle_exclusion`): FALSE** —
every named toggle is outside `DialOneStrengthenedFam`.
Stated here so the classification's three grades each
carry their question by name; proved nowhere here, and
not to be re-opened as a live question. -/
def ToggleQuestion : Prop :=
  ∃ π, DialOneStrengthenedFam π ∧ IsToggleOfPi1 π ∧ π ≠ pi1

/-- Read-back: `IsToggleOfPi1` is visibly the registered
record form — `piFlip ∨ piDouble ∨ ∃ c, piSwap c`, the
three landed toggle families and no others. -/
theorem isToggleOfPi1_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    IsToggleOfPi1 π ↔
      π = ThetLogos.HyperchargeForcing.piFlip ∨ π = piDouble
        ∨ ∃ c, π = ThetLogos.DialOneGammaFamilyChecks.piSwap c :=
  Iff.rfl

/-- Read-back: `ToggleQuestion` is visibly the registered
record-form toggle question over the strengthened set. -/
theorem toggleQuestion_unfold :
    ToggleQuestion ↔
      ∃ π, DialOneStrengthenedFam π ∧ IsToggleOfPi1 π ∧ π ≠ pi1 :=
  Iff.rfl

/-! ## Grade R — prose only, by design

There is no section of definitions for Grade R in this
module, and that absence is the pin's content for the
grade: the equivalence notion is UNCHOSEN, the grade is
UNPRICED, and it enters this registration as the prose of
the module header above — named, fenced, and deliberately
given no formal seat — until a future scoping chooses the
equivalence and prices the grade. -/

end ThetLogos.DialOneClassificationPin
