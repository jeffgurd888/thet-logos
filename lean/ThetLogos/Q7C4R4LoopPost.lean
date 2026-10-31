import Mathlib.Tactic
import ThetLogos.Q7C4R4Dynamics
import ThetLogos.FiniteEntropy
import ThetLogos.ThermalZ4ClockDefect
import ThetLogos.ViscousLine

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4LoopPost - registration of thermal loops on the
Q7 x C4 x R4 composite (Q7CR-LOOP-0)

**Status: REGISTRATION ONLY (A0/T0 pattern) - `LoopData` plus three
closure `Prop`s stated as THREE SEPARATE definitions, and
`SelfContainedLoop`. NO theorems are attempted in this module.
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing memo: `scoping-q7cr-missing-pieces-thermal-loops-2026-10-30.md`
section 2 (the definitions, carried here in substance) and the
section 4 LOOP-0 row. Gates LANDED: Q7CR-5
(`ThetLogos.Q7C4R4Dynamics` - the step/state notion below), T-ENT
(`ThetLogos.FiniteEntropy` - `entropyW`, so the factor-entropy-change
terms of `LedgerClosed` are admissible in the form registered here),
Z4-KMS-1 (`ThetLogos.ThermalZ4ClockDefect` - the clock miniature's
defect source, CITED in section 5 below, not re-proved).

## State and step notion (from Q7CR-5, landed)

A state is a weight function on `compIndex` (`compIndex -> R`), the
weight-state form of Q7CR-5; the distinguished thermal family is
Q7CR-5's `dynGibbs beta` (the normalized Gibbs weights of the CHOSEN
generator), with `dynGibbsState` its expectation form. A step is a
stated map on that state space, carried as data (section 1). Nothing
else is admitted as a state or a step in this line.

## The three closure notions - SEPARATE, never conflated

A loop is data (`LoopData`, section 2) plus three separate Props
about it (section 3). They are three different statements, and no
result on this line may pass one off as another:

- `IndexClosed` - the **control/protocol parameters** return
  exactly: the step parameters (times, grades, couplings) at the
  end equal those at the start. A statement about the *protocol*,
  not about any state.
- `StateClosed` - the **state** returns exactly: the composite of
  the loop's steps, applied to the initial state, equals the
  initial state, as an equality in the state space
  (`compIndex -> R`). This Prop is registered so that it CAN FAIL
  for stated step-data (kill K-LOOP-1, below): a step's state map
  is an unconstrained data field, the total step is the literal
  composition of the stated steps, and it is NOT defined as a
  return-map or projection. Step-data whose maps move the initial
  state (for example a single step rescaling one weight) give
  `StateClosed` = a false equality claim about that data.
- `LedgerClosed` - the **accounting** closes internally: the sum
  of the steps' defect terms (trace-defect form, section 1) plus
  the factor entropy changes (T-ENT's `entropyW` form) equals the
  loop's stated total, with **every term carried by a factor of
  the composite**: each step carries a named `defectFactor` and a
  named `entropyFactor` (section 1), the sums range only over the
  loop's own steps, and no term is an unnamed environment, a
  boundary sink, or prose.

## Self-contained

`SelfContainedLoop` (section 4) is, in the memo's words:
`StateClosed AND LedgerClosed AND (external work term = 0)`.
The external work term is an explicit component of `LoopData`
(the field `externalWork`), never silently absent. Three readings
are thereby separated forever: a loop may be `IndexClosed` only
(a relabeling - thermal content zero), `StateClosed` with an
external work term paying for it (a driven cycle - NOT
self-contained), or `SelfContainedLoop` in the sense above.
Every later dossier on this line states which of the three each
result is, in these words.

## Thermal vocabulary fence

The only thermal quantities admitted are the owned ledgers named
in the memo: the trace defect in `ViscousLine.traceDefect` form
(its closed form `traceDefect_eq_sum`:
`sum i, w i * (1 - exp (-2 * t * lam i))`, transported here from
`Fin N` seats to `compIndex` with per-step rate data carried as a
field), and - T-ENT having landed - `entropyW` and its factor
bookkeeping. No beta(x) field, no flow-generated arrow (G2 stands:
the Gibbs state is exactly stationary under its modular flow;
arrows live in steps, never in flows). Jeff's verb for the
compulsion reading appears in this line only in quotation as his;
the strong reading - exact state closure + positive production +
no ledger outlet - is DEAD ON ARRIVAL per the memo's obstruction
O1 (pre-registered kill K-LOOP-2): this brick only registers the
notions; LOOP-1 is the brick that proves the no-go.

## The clock miniature (section 5)

The Z4 clock shift is registered on the face as the
**IndexClosed-only miniature**: `z4ClockLoopData beta` is
`LoopData`-shaped data whose protocol does four clock turns and
returns its control parameters exactly, and whose state step is
the clock pullback along the C4 factor's `Fin 4` coordinate. Its
defect source is CITED from Z4-KMS-1 - `z4_clock_defect_factor`
(per-step factor `exp (-beta / 4)`, `exp (3 * beta / 4)` at the
wrap) and `z4_clock_not_invariant` (for `beta > 0` the shifted
ladder weights are not the ladder weights) - and is NOT re-proved
here. Registered as IndexClosed ONLY: **its thermal content as a
loop is zero** - its Gibbs/ladder state does not return at
`beta > 0` after a step (that non-return is Z4-KMS-1's statement,
and its loop-form corollary seat is LOOP-2's, not this brick's
claim). No `StateClosed`, `LedgerClosed`, or `SelfContainedLoop`
statement is made about the miniature in this module.

## Fences (standing for the whole LOOP line)

- The three closure notions are NEVER conflated: index closure
  passed off as state closure is K-LOOP-armed (K-LOOP-3).
- K-LOOP-1 (closure bought by definition / vacuity): `StateClosed`
  must be able to fail for stated step-data; see above.
- K-LOOP-2 (production without a ledger outlet): not a candidate
  form anywhere on this line.
- K-LOOP-4 (continuum creep): any loop form requiring continuum
  fields or infinite-dimensional flows is FRONTIER, not a brick.
- NO CLAIM; dials 0/4; no measured number is claimed by this line;
  the bounded-commutator vacuity caveat inherited from the
  gauntlet memo applies where the composite's operators are
  mentioned.
-/

/-! ## Section 1. Protocol parameters, factors, and steps -/

/-- **Protocol (control) parameters of one step**: a time, a grade
(the C4 clock grade, `Fin 4`), and a coupling. These are the
parameters `IndexClosed` is about - protocol data, never state
data. -/
structure LoopStepParam where
  /-- Step time (the heat/ternary step's duration parameter). -/
  time : ℝ
  /-- Step grade (the C4 clock grade at this step). -/
  grade : Fin 4
  /-- Step coupling. -/
  coupling : ℝ

/-- **A named factor of the composite** Q7 x C4 x R4. Ledger terms
are carried by one of these three - never by an unnamed
environment or sink. -/
inductive LoopFactor where
  /-- The Q7 factor. -/
  | q7
  /-- The C4 factor. -/
  | c4
  /-- The R4 factor. -/
  | r4
  deriving DecidableEq, Repr

/-- **One step of a loop**, as data: its protocol parameters, its
stated map on the weight-state space (`compIndex -> R`, Q7CR-5's
state form), its per-mode rate data for the trace-defect term,
and the named factors carrying its two ledger terms.

The state map is an unconstrained field on purpose: nothing in
this registration forces it to return any state, so
`StateClosed` (section 3) can fail for stated step-data
(K-LOOP-1). -/
structure LoopStep where
  /-- Protocol parameters of this step. -/
  param : LoopStepParam
  /-- The stated state map of this step, on weight states. -/
  applyState : (compIndex → ℝ) → (compIndex → ℝ)
  /-- Per-mode rates for this step's trace-defect term, in
  `ViscousLine.traceDefect` form. -/
  rate : compIndex → ℝ
  /-- The named factor carrying this step's defect term. -/
  defectFactor : LoopFactor
  /-- The named factor carrying this step's entropy-change term. -/
  entropyFactor : LoopFactor

/-- **The trace-defect term of one step at a visited weight
state**, in `ViscousLine.traceDefect` form: the closed form of
`traceDefect_eq_sum` (`sum i, w i * (1 - exp (-2 * t * lam i))`)
with the step's own time, rate data, and the visited state.
Tier T2 (definition). -/
noncomputable def loopStepDefect (s : LoopStep) (w : compIndex → ℝ) : ℝ :=
  ∑ x, w x * (1 - Real.exp (-2 * s.param.time * s.rate x))

/-- **The factor entropy-change term of one step at a visited
weight state**, in T-ENT's form: the change of `entropyW`
(`ThetLogos.FiniteEntropy`) across the step. The term is carried
by the step's named `entropyFactor`. Tier T2 (definition). -/
noncomputable def loopStepEntropyChange (s : LoopStep)
    (w : compIndex → ℝ) : ℝ :=
  entropyW (s.applyState w) - entropyW w

/-! ## Section 2. Loop data -/

/-- **Loop data on the composite**: a finite step sequence, an
initial weight state, the protocol parameters at the start and at
the end (stated protocol data - `IndexClosed` compares exactly
these), the stated ledger total (`LedgerClosed` compares the
internal sum against exactly this), and the external work term
(an explicit component, never silently absent).

Concrete enough for LOOP-1/2/3 to instantiate without
redefinition: autonomous loops use a constant one-step list,
protocol loops use the graded step list, factor-exchange loops
use steps whose `defectFactor` / `entropyFactor` fields name the
receiving factors. -/
structure LoopData where
  /-- The finite step sequence, in application order. -/
  steps : List LoopStep
  /-- The initial weight state on `compIndex`. -/
  initialState : compIndex → ℝ
  /-- Protocol parameters at the start of the loop. -/
  initialParam : LoopStepParam
  /-- Protocol parameters at the end of the loop, as stated by
  the protocol. -/
  finalParam : LoopStepParam
  /-- The stated total the internal ledger must equal. -/
  statedLedgerTotal : ℝ
  /-- The external work term: work crossing the composite's
  boundary during the loop. Explicit field of the data. -/
  externalWork : ℝ

/-- **The total state map of a step list**: the literal
composition of the stated steps, in list order, applied to a
weight state. Defined by recursion on the list; it is NOT a
return-map or a projection, and for arbitrary step-data its value
at the initial state differs from the initial state - which is
exactly what makes `StateClosed` a non-vacuous Prop
(K-LOOP-1). -/
def applyLoopSteps : List LoopStep → (compIndex → ℝ) → (compIndex → ℝ)
  | [], w => w
  | s :: rest, w => applyLoopSteps rest (s.applyState w)

/-- **The final state of a loop**: its steps composed, applied to
its initial state. -/
def loopFinalState (L : LoopData) : compIndex → ℝ :=
  applyLoopSteps L.steps L.initialState

/-- **The internal defect sum of a step list**: each step's
trace-defect term (`loopStepDefect`, `ViscousLine.traceDefect`
form) evaluated at the state that step actually visits, summed
in order. Every summand is indexed by a step, hence carried by
that step's named `defectFactor`. -/
noncomputable def loopDefectSum :
    List LoopStep → (compIndex → ℝ) → ℝ
  | [], _ => 0
  | s :: rest, w =>
      loopStepDefect s w + loopDefectSum rest (s.applyState w)

/-- **The internal entropy-change sum of a step list**: each
step's `entropyW` change (`loopStepEntropyChange`, T-ENT form)
evaluated across the state that step actually visits, summed in
order. Every summand is indexed by a step, hence carried by that
step's named `entropyFactor`. -/
noncomputable def loopEntropyChangeSum :
    List LoopStep → (compIndex → ℝ) → ℝ
  | [], _ => 0
  | s :: rest, w =>
      loopStepEntropyChange s w
        + loopEntropyChangeSum rest (s.applyState w)

/-- **The loop's internal ledger total**: defect sum plus
entropy-change sum, both over the loop's own steps and visited
states only. -/
noncomputable def loopLedgerSum (L : LoopData) : ℝ :=
  loopDefectSum L.steps L.initialState
    + loopEntropyChangeSum L.steps L.initialState

/-- **Gibbs-initial registration**: a loop is Gibbs-initial at
`beta` when its initial state is Q7CR-5's Gibbs weight family
`dynGibbs beta` - the distinguished thermal state form admitted
by the memo's THERMAL paragraph (with `dynGibbsState` its
expectation form). A registration Prop only; nothing about the
loop's closure follows from it. -/
def IsGibbsInitial (L : LoopData) (beta : ℝ) : Prop :=
  L.initialState = dynGibbs beta

/-! ## Section 3. The three closure Props - THREE SEPARATE
definitions, never conflated -/

/-- **IndexClosed** - the control/protocol parameters return
exactly: the loop's final protocol parameters (times, grades,
couplings) equal its initial ones. A statement about the
*protocol*, not about any state. -/
def IndexClosed (L : LoopData) : Prop :=
  L.finalParam = L.initialParam

/-- **StateClosed** - the state returns exactly: the loop's total
step, applied to its initial state, equals its initial state, as
an equality in the state space (`compIndex -> R`).

This Prop CAN FAIL for stated step-data (K-LOOP-1): the total
step is the literal composition `applyLoopSteps` of unconstrained
stated step maps, not a return-map or projection, so step-data
whose maps move the initial state make this an equality that
does not hold. -/
def StateClosed (L : LoopData) : Prop :=
  loopFinalState L = L.initialState

/-- **LedgerClosed** - the accounting closes internally: the
loop's internal ledger sum (defect terms in trace-defect form
plus factor entropy changes, every term carried by a named
factor via its step's `defectFactor` / `entropyFactor` fields)
equals the loop's stated total. No term is an unnamed
environment, a boundary sink, or prose. -/
def LedgerClosed (L : LoopData) : Prop :=
  loopLedgerSum L = L.statedLedgerTotal

/-! ## Section 4. Self-contained -/

/-- **SelfContainedLoop** - in the memo's words:
`StateClosed AND LedgerClosed AND (external work term = 0)`.
No work or energy crosses the composite's boundary during the
loop; every term of production is accounted by a named factor
inside. Note what this definition does NOT include:
`IndexClosed` - protocol return is a separate, weaker notion,
and a self-contained loop is not defined by it. -/
def SelfContainedLoop (L : LoopData) : Prop :=
  StateClosed L ∧ LedgerClosed L ∧ L.externalWork = 0

/-! ## Section 5. The clock miniature - IndexClosed ONLY

The Z4 clock shift, registered as the IndexClosed-only miniature.
Its defect is CITED from Z4-KMS-1 (`z4_clock_defect_factor`,
`z4_clock_not_invariant` in `ThetLogos.ThermalZ4ClockDefect`),
not re-proved here. Its thermal content as a loop is zero: at
`beta > 0` its ladder state is moved by the first turn, not
returned. No closure Prop beyond the index reading is registered
for it in this module. -/

/-- **The clock turn on composite indices**: advance the C4
factor's `Fin 4` coordinate by one (mod 4), the composite seat of
the Z4 clock shift `z4Shift`. All other coordinates are fixed. -/
def z4ClockShiftIndex (t : compIndex) : compIndex :=
  ((t.1.1, (t.1.2.1 + 1, t.1.2.2)), t.2)

/-- **One clock step as loop-step data**: grade advanced by one,
time and coupling zero (no heat step is taken), state map the
clock pullback along `z4ClockShiftIndex`, rate data zero, both
ledger terms carried by the C4 factor. -/
def z4ClockStep (k : Fin 4) : LoopStep where
  param := { time := 0, grade := k + 1, coupling := 0 }
  applyState := fun w t => w (z4ClockShiftIndex t)
  rate := fun _ => 0
  defectFactor := LoopFactor.c4
  entropyFactor := LoopFactor.c4

/-- **The clock miniature as loop data** (a stated instance
schema at ladder parameter `beta`): four clock turns at grades
0, 1, 2, 3; protocol parameters start and end at grade 0, time 0,
coupling 0 - the protocol returns exactly, which is the whole
content of its registration. The initial state is the ladder
weight `z4Weight beta` read along the C4 factor's `Fin 4`
coordinate. Stated ledger total and external work term are both
registered as 0 as DATA; no `LedgerClosed` or
`SelfContainedLoop` statement is made about this data here.

Per Z4-KMS-1 (CITED, not re-proved): `z4_clock_defect_factor`
gives the per-turn defect factor `exp (-beta / 4)` on the ladder
weights (`exp (3 * beta / 4)` at the wrap), and
`z4_clock_not_invariant` gives that for `beta > 0` the turned
weights are not the weights - the miniature's state does not
return at `beta > 0`, and its thermal content as a loop is
zero. -/
noncomputable def z4ClockLoopData (beta : ℝ) : LoopData where
  steps := [z4ClockStep 0, z4ClockStep 1, z4ClockStep 2, z4ClockStep 3]
  initialState := fun t => z4Weight beta t.1.2.1
  initialParam := { time := 0, grade := 0, coupling := 0 }
  finalParam := { time := 0, grade := 0, coupling := 0 }
  statedLedgerTotal := 0
  externalWork := 0

/-- **The miniature's registered closure reading, named as
such**: the clock miniature is registered under the index
reading - `IndexClosed (z4ClockLoopData beta)` is the Prop its
registration states. This definition names the reading only; it
asserts nothing (no proof is attempted in this module), and no
`StateClosed`, `LedgerClosed`, or `SelfContainedLoop` reading of
the miniature is registered anywhere in this module. -/
def Z4ClockMiniatureReading (beta : ℝ) : Prop :=
  IndexClosed (z4ClockLoopData beta)

end ThetLogos
