import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Language

namespace ThetLogos

/-!
# ThetLogos.PvsNPDefs — P vs NP definitions brick (PNP-1a)

Board charter: **NO CLAIM.** Parts of P vs NP closed by this house:
**0** — now, and after this brick lands (a definitions brick closes
no part of the problem). This module is the definitions half of
PNP-1 (Lane 3), split per the PNP-0 audit
(`routeb-general-scratch/scoping-pnp-0-2026-11-02.md`): it DEFINES
the polytime decider wrapper, the class `P`, the pairing function,
and the class `NP` in verifier form, in the audit's §3 shapes. The
board statement `Prop`s are carried here as definitions only
(`PeqNP`, `NPSubsetP` — PNP-1b states the board against them); the
K-PNP-1 diagonal witness (audit item D5) lands in PNP-1c. Jeff's T5
identification (verification/construction asymmetry) is NOT pin
content and appears nowhere below.

## Shelf used (free from the pin, cited — PNP-0 §1)

- `Language Bool = Set (List Bool)` — `Mathlib/Computability/Language.lean`.
  The alphabet is fixed to `Bool` (audit §3: Cook-standard binary;
  fixing one alphabet is what a statement pin should do).
- `Turing.FinTM2`, `Turing.TM2OutputsInTime`,
  `Turing.TM2ComputableAux` — `Mathlib/Computability/TuringMachine/Computable.lean`.
- `Polynomial ℕ` with `Polynomial.eval` as the time bound — the
  pin's own unit in `TM2ComputableInPolyTime` (Computable.lean).
- Step counting is the pin's `EvalsToInTime` over `FinTM2.step`:
  one step = one TM2 statement execution (PNP-0 §1.2, §4A.1). No
  house step-counting relation is defined and the time unit is NOT
  redefined anywhere in this module.

## K-PNP-1 fence — carried on the face (PNP-0 §4)

Kill condition: a pin whose polytime notion is satisfiable by
construction artifacts — every language polytime by construction —
is vacuous; kill and re-enter. Part A of the audit's test PASSED
against these shapes, and that PASS is inherited **only while both
of the following stay exact**:

1. **Genuine step-count unit.** `PolyDecider.correct` bounds
   `Turing.TM2OutputsInTime` by `time.eval x.length` — the pin's
   own step count, undistorted except by the pin's noted constant
   factor. No rescaling in this module.
2. **Total deciders only.** `correct` quantifies over EVERY input
   `x` and demands the correct output bit (`[true]` iff `x ∈ L`,
   else `[false]`) within the bound. There is no partiality, no
   "accepts if it halts", no promise restriction to hide in.

Part B (time-hierarchy witness statability) is CONDITIONAL on
audit item D5, which is PNP-1c's brick, not this one — see the D5
interface note at the end of this header. Without D5 the witness
cannot be stated and K-PNP-1 is unarmed; this brick does not
pretend otherwise.

## NP guards — both load-bearing, verbatim in `InNP` below

1. **Certificate bounded by a polynomial in `|x|` ALONE:**
   `w.length ≤ (x.length + 1) ^ c` — the bound mentions `x.length`
   and the constant `c` only; never `w`, never the pair length.
2. **The verifier itself is a polytime decider:** the pair
   language `VL` is required to satisfy `InP VL`, i.e. a
   `PolyDecider` over paired inputs (`pairStr x w ∈ VL`), total
   and polytime in the pair length.

Drop either guard and every RE language would satisfy the shape
(PNP-0 §4A.3); the definition below drops neither.

## Form rulings (PNP-0 §3.1, §3.2)

- **NP is defined in VERIFIER form.** The pin has no
  nondeterministic Turing machine (PNP-0 §1.4); NO machine/NDTM
  form is defined here and NO equivalence is stated. If a later
  brick wants the machine form, it enters as a named hypothesis,
  never as a house theorem at pin grade.
- **`PeqNP` is set equality** `PClass = NPClass` — both
  directions, neither baked in; its negation is equally statable.
  The one-way form `∀ L, L ∈ NP → L ∈ P` as the board statement
  is FORBIDDEN: it silently presupposes `P ⊆ NP`, an inclusion
  unproved in this corpus. `NPSubsetP` is named separately as the
  substantive working direction — as a definition only; no
  inclusion is proved or asserted anywhere in this module.

## D5 interface note (for PNP-1c — PNP-0 §4B, §5)

D5 (the decider-code decoding for the K-PNP-1 witness) belongs to
PNP-1c by the audit's price split, and NO D5 definition is landed
here. The exact interface PNP-1c will consume is the audit's
route (ii): `Nat.Partrec.Code` — pin data, `Denumerable`
(`Mathlib/Computability/PartrecCode.lean`) — from which PNP-1c
owns its decode `List Bool → Option (Nat.Partrec.Code ×
Polynomial ℕ)` and its step-bounded acceptance predicate, then
states `Ldiag` and `KPNP1Witness : Prop := Ldiag ∉ PClass`
against `PClass` below. Route (ii) needs nothing extracted from
`PolyDecider` (the decode reads the input string, not a bundled
machine — route (i)'s `FinTM2` normal form was rejected by the
audit because `FinTM2` has Type-valued fields), so `PolyDecider`
exposes no code field and needs none for D5 to stay usable.

## One plumbing deviation from the audit's draft text (named)

The audit's §3 draft writes `if x ∈ L then [true] else [false]`
inside `PolyDecider.correct`. Membership in a `Language` carries
no `Decidable` instance in the pin, so the literal draft does not
elaborate; the structure below supplies the instance with
`open Classical in` and is otherwise character-for-character the
audit's shape — same fields, same bound, same output bits. The
`correct` field is a `Prop`, so nothing computational depends on
the classical instance.

Honesty tiers in this file:
- **T1 (proved):** only the `Iff.rfl` unfold self-checks at the
  end — about these definitions, not about P vs NP.
- **Definitions (no tier):** everything else. A definition asserts
  nothing; no membership, non-membership, inclusion, or
  non-vacuity content is stated or proved here.
- **NO CLAIM:** P vs NP itself. Unproved here, unrefuted here,
  untouched here.
-/

open Classical in
/-- **D1 (owned): a bundled polytime decider for a language `L`.**

A `Turing.TM2ComputableAux Bool Bool` (the pin's bundled `FinTM2`
plus input/output alphabet equivs to `Bool`), a polynomial time
bound, and total correctness: for EVERY input `x` the machine
outputs `[true]` if `x ∈ L` and `[false]` otherwise, within
`time.eval x.length` steps of the pin's genuine step count
(`Turing.TM2OutputsInTime`). Totality is the K-PNP-1 fence: a
construction artifact would have to actually decide `L`. -/
structure PolyDecider (L : Language Bool) where
  aux : Turing.TM2ComputableAux Bool Bool
  time : Polynomial ℕ
  correct : ∀ x : List Bool,
    Turing.TM2OutputsInTime aux.tm
      (x.map aux.inputAlphabet.invFun)
      (some ((if x ∈ L then [true] else [false]).map
        aux.outputAlphabet.invFun))
      (time.eval x.length)

/-- `L` is decidable in polynomial time: some `PolyDecider`
for `L` exists. -/
def InP (L : Language Bool) : Prop := Nonempty (PolyDecider L)

/-- **The class P**: the set of languages over `Bool` decidable
by a total polytime decider. -/
def PClass : Set (Language Bool) := {L | InP L}

/-- **D2 (owned): length-prefixed pairing of strings.** The
unary length prefix (`x.length` many `true`s, then one `false`)
makes the split point recoverable, so verifier inputs
`pairStr x w` encode the pair `(x, w)` unambiguously. -/
def pairStr (x w : List Bool) : List Bool :=
  (List.replicate x.length true ++ [false]) ++ x ++ w

/-- **NP, VERIFIER FORM (the definition — PNP-0 §3.1).**
`L ∈ NP` iff there is a constant `c` and a pair language `VL`
decidable in polynomial time (`InP VL` — the verifier is itself
a polytime decider, guard 2) such that for every `x`,
`x ∈ L ↔ ∃ w, w.length ≤ (x.length + 1) ^ c ∧ pairStr x w ∈ VL`
— the certificate `w` bounded by a polynomial in `|x|` ALONE
(guard 1). Both guards are load-bearing (K-PNP-1, PNP-0 §4A.3).
No machine/NDTM form is defined; no equivalence is stated. -/
def InNP (L : Language Bool) : Prop :=
  ∃ (c : ℕ) (VL : Language Bool), InP VL ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool,
      w.length ≤ (x.length + 1) ^ c ∧ pairStr x w ∈ VL

/-- **The class NP** (verifier form): the set of languages over
`Bool` satisfying `InNP`. -/
def NPClass : Set (Language Bool) := {L | InNP L}

/-- **The board statement, as a definition only** (PNP-1b states
the board against it): `P = NP` as SET EQUALITY of the two
classes — both directions, neither baked in (PNP-0 §3.2). The
one-way inclusion form is forbidden as the board statement: it
presupposes the unproved `P ⊆ NP`. NO CLAIM — this definition
asserts neither the equality nor its negation. -/
def PeqNP : Prop := PClass = NPClass

/-- **The substantive working direction, named separately
(definition only):** every NP language is in P. Stating this
Prop is not proving it, and it is NOT the board statement —
`PeqNP` above is. -/
def NPSubsetP : Prop := ∀ L : Language Bool, L ∈ NPClass → L ∈ PClass

/-- Pin self-check (T1, statement grade): `InP` unfolds
definitionally to the existence of a `PolyDecider`. Proved by
`Iff.rfl`. Asserts nothing about P vs NP. -/
theorem inP_iff (L : Language Bool) :
    InP L ↔ Nonempty (PolyDecider L) :=
  Iff.rfl

/-- Pin self-check (T1, statement grade): `InNP` unfolds
definitionally to its literal verifier-form text, with both
guards on the face (certificate bound in `|x|` alone; verifier
language in `InP`). Proved by `Iff.rfl`. -/
theorem inNP_iff (L : Language Bool) :
    InNP L ↔
      ∃ (c : ℕ) (VL : Language Bool), InP VL ∧
        ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool,
          w.length ≤ (x.length + 1) ^ c ∧ pairStr x w ∈ VL :=
  Iff.rfl

/-- Pin self-check (T1, statement grade): `PeqNP` unfolds
definitionally to set equality of the classes — the honest
both-directions form, not the forbidden one-way inclusion.
Proved by `Iff.rfl`. -/
theorem peqNP_iff :
    PeqNP ↔ PClass = NPClass :=
  Iff.rfl

end ThetLogos
