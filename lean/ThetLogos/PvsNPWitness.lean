import ThetLogos.PvsNPDefs
import Mathlib.Computability.PartrecCode

namespace ThetLogos

/-!
# ThetLogos.PvsNPWitness — K-PNP-1 witness brick (PNP-1c)

Board charter: **NO CLAIM.** Parts of P vs NP closed by this house:
**0** — now, and after this brick lands (a witness-statement brick
closes no part of the problem). This module is PNP-1c, Lane 3's last
priced item, split per the PNP-0 audit
(`routeb-general-scratch/scoping-pnp-0-2026-11-02.md` §5): it owns
audit item D5 — the route-(ii) decode and the diagonal language —
against ONLY the frozen names of `ThetLogos.PvsNPDefs` (PNP-1a).
Nothing in PNP-1a is renamed, extended, or edited, and `PClass`
(the pin's polytime, via the total `PolyDecider` over `FinTM2`)
is not touched, weakened, or redefined anywhere below.

## What this brick is: the K-PNP-1 Part B receipt

K-PNP-1 (PNP-0 §4) kills a pin whose polytime notion is
satisfiable by construction artifacts. Part A passed in PNP-1a
and is inherited unchanged. Part B — time-hierarchy witness
statability — was CONDITIONAL on D5: the diagonal language and
its non-membership in `PClass` must be *statable* in the pin's
own vocabulary, with every constituent defined. That is exactly
what lands here: `decode`, `AcceptsWithin`, `Ldiag`, and

  `KPNP1Witness : Prop := Ldiag ∉ PClass`

— STATED, NOT PROVED. The Prop being fully formed, in the
pin's own vocabulary, with every constituent defined without
weakening, IS the Part B receipt. Nothing below asserts that
`KPNP1Witness` holds.

## `decode` — route (ii), and its totality convention (on the face)

A string is read, little-endian, as the natural number
`natOfBoolList x`; that number is split by the pin's
`Nat.unpair` into a code number and a polynomial number:

- the code number is decoded by the pin's own total Gödel
  decoder `Nat.Partrec.Code.ofNatCode` (the inverse of
  `encodeCode`; `Nat.Partrec.Code` is `Denumerable`,
  `Mathlib/Computability/PartrecCode.lean`) — NOT by any
  extraction from `PolyDecider` (route (i)'s `FinTM2` normal
  form was rejected by the audit: `FinTM2` has Type-valued
  fields);
- the polynomial number is decoded as a pair-chain code for a
  coefficient list (`listOfNat`: `0` = empty list,
  `Nat.pair a m + 1` = `a` consed onto the list coded by `m`,
  read with fuel equal to the code itself), and the list is
  read as a polynomial in low-to-high coefficient order
  (`polyOfCoeffList`: `C a + X * rest`).

**Totality convention:** both Gödel decodings used here are
TOTAL, so `decode` returns `some (M, p)` for EVERY string `x`
and never returns `none`. There are NO undecodable strings
under this convention — the `Option` in the audit's D5 shape
`List Bool → Option (Nat.Partrec.Code × Polynomial ℕ)` is
kept, with its `none` branch unused — and no hidden reject
class is smuggled in through it. The decoding is many-to-one
(trailing `false` bits do not change `natOfBoolList x`, and a
number's unpairing is read at the string's own length in
`Ldiag` below), which does not trivialize it: the decoded
`Nat.Partrec.Code` carries the pin's real partial-recursive
semantics (`Code.eval`, tied to the bounded form by the
soundness theorem proved below).

## Step-bounded acceptance — as far as the pin honestly reaches

The pin's TM2 step-count conventions (`EvalsToInTime` over
`FinTM2.step`, PNP-0 §1.2) govern `PolyDecider` / `PClass` in
PNP-1a. They do NOT transfer to `Nat.Partrec.Code`: the pin
supplies no TM2 execution of a partial-recursive code, and no
such transfer or TM2 step claim is made or improvised here.
What the pin DOES supply for `Code` is its own bounded
evaluation, `Nat.Partrec.Code.evaln` — a total, bounded
approximant to `Code.eval`, with `evaln_sound` (a bounded
acceptance is a genuine `eval` acceptance) and
`evaln_complete` (every `eval` acceptance appears at some
bound) in the pin. `AcceptsWithin M x b` is therefore defined
through `evaln`, and nothing stronger is claimed for it:

- the `evaln` parameter is `b + natOfBoolList x + 1`: the
  decoded polynomial supplies the ALLOWANCE `b` on top of the
  input's own magnitude. The offset is on the face because
  `evaln`'s parameter also guards the numbers it encounters
  (pin: a successful `evaln k` evaluation forces the input
  `< k`, `evaln_bound`), so an un-offset bound could fail
  purely on the input guard rather than on the computation;
- the acceptance output convention is output exactly `1`
  (the `ℕ`-valued analogue of `PolyDecider`'s `[true]`
  output). Any other output, or no output within the
  allowance, is NOT acceptance.

This predicate does not weaken `PClass`: it is not used to
define `P`, it imposes no totality on a `Code` (a code's
unbounded `eval` is partial recursive, as in the pin), and a
construction artifact would still have to actually compute.

## `Ldiag` — the audit's diagonal clause, verbatim in shape

`Ldiag` is the PNP-0 §4B draft's clause, with `<decider code
type>` instantiated to the route-(ii) type
`Nat.Partrec.Code`:

  `x ∈ Ldiag` iff `∀ (M : Nat.Partrec.Code) (p : Polynomial ℕ),
    decode x = some (M, p) → ¬ AcceptsWithin M x (p.eval x.length)`

— self-reference through the decoded code evaluated on the
string `x` itself, under the decoded polynomial's own bound
at `x`'s own length, with the answer flipped. Under the
totality convention above, `decode x` is always a `some`, so
the universal clause is the flip of `x`'s own decoded pair —
no string escapes the diagonal by being undecodable.

## Fences

- **The time-hierarchy theorem itself is T4 classical
  knowledge**, cited as such: it motivates the diagonal shape
  and is NEVER a house theorem. No transfer of that theorem
  to this pin's `evaln`-bounded acceptance is proved or
  asserted in this module.
- K-PNP-1 Part A's PASS is inherited unchanged from PNP-1a;
  this brick neither re-opens nor re-proves it.
- Nothing here asserts `Ldiag ∉ PClass`, asserts anything
  about `PeqNP` or `NPSubsetP`, or touches the board
  statement in `ThetLogos.PvsNPStatement`.

Honesty tiers in this file:
- **T1 (proved):** only the definitional unfold self-checks
  and the `evaln`-soundness link at the end — about these
  definitions and the pin's bounded evaluation, not about
  P vs NP.
- **T4 (cited, not proved):** the deterministic time-hierarchy
  theorem, in the fence above only; never a house theorem.
- **Definitions (no tier):** everything else. A definition
  asserts nothing; in particular `KPNP1Witness` is a stated
  `Prop`, not a proved one.
- **NO CLAIM:** P vs NP itself. Unproved here, unrefuted
  here, untouched here.
-/

/-- **Input / code number of a string:** the little-endian
binary value of `x` (head bit least significant). Used both
as the number `decode` splits and as the `ℕ` input on which
a decoded `Nat.Partrec.Code` is evaluated — the code is run
on the string itself, under this fixed reading. -/
def natOfBoolList : List Bool → ℕ
  | [] => 0
  | b :: t => (if b then 1 else 0) + 2 * natOfBoolList t

/-- **Coefficient-list decoding, fuelled form:** reads the
pair-chain code `0` = empty list, `Nat.pair a m + 1` = `a`
consed onto the list coded by `m`; `fuel` bounds the chain
length read. Structural recursion on `fuel`. -/
def listOfNatAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, n + 1 => (Nat.unpair n).1 :: listOfNatAux fuel (Nat.unpair n).2

/-- **Coefficient-list decoding:** `listOfNat n` is
`listOfNatAux n n` — fuel equal to the code itself, which
bounds the length of any list it codes. -/
def listOfNat (n : ℕ) : List ℕ := listOfNatAux n n

/-- **A coefficient list as a polynomial,** low-to-high:
`[a₀, a₁, …]` ↦ `C a₀ + X * (rest as a polynomial)`. -/
noncomputable def polyOfCoeffList : List ℕ → Polynomial ℕ
  | [] => 0
  | a :: t => Polynomial.C a + Polynomial.X * polyOfCoeffList t

/-- **Polynomial decoding:** the polynomial whose
low-to-high coefficient list is coded by `n`. -/
noncomputable def polyOfNat (n : ℕ) : Polynomial ℕ := polyOfCoeffList (listOfNat n)

/-- **D5 (owned, audit route (ii)): decoding of an input
string as a (machine code, time-bound polynomial) pair.**

`decode x = some (Nat.Partrec.Code.ofNatCode (Nat.unpair
(natOfBoolList x)).1, polyOfNat (Nat.unpair (natOfBoolList
x)).2)`.

**Totality convention (on the face):** both Gödel decodings
composed here are total, so `decode x` is a `some` for EVERY
`x` and is never `none`; there are no undecodable strings
under this convention and the `none` branch of the audit's
`Option` shape is unused. -/
noncomputable def decode (x : List Bool) : Option (Nat.Partrec.Code × Polynomial ℕ) :=
  let n := natOfBoolList x
  some (Nat.Partrec.Code.ofNatCode (Nat.unpair n).1, polyOfNat (Nat.unpair n).2)

/-- **Step-bounded acceptance, as far as the pin reaches for
`Nat.Partrec.Code`:** the decoded code `M`, evaluated on the
string `x` itself (read as `natOfBoolList x`), outputs
exactly `1` under the pin's bounded evaluation
`Nat.Partrec.Code.evaln`, with allowance `bound` on top of
the input's magnitude: the `evaln` parameter is
`bound + natOfBoolList x + 1` (see the header for why the
offset is on the face — `evaln`'s parameter also guards the
input's magnitude). This is NOT a TM2 step count: the pin
supplies no TM2 execution of a partial-recursive code, and
none is claimed. -/
def AcceptsWithin (M : Nat.Partrec.Code) (x : List Bool) (bound : ℕ) : Prop :=
  Nat.Partrec.Code.evaln (bound + natOfBoolList x + 1) M (natOfBoolList x) = some 1

/-- **The diagonal (time-hierarchy witness) language,**
defined — the PNP-0 §4B clause verbatim in shape, with the
code type instantiated to route (ii)'s
`Nat.Partrec.Code`: `x ∈ Ldiag` iff for every code `M` and
polynomial `p` that `x` decodes to, `M` does NOT accept `x`
itself within bound `p.eval x.length`. Self-reference is
through the decoded code evaluated on the string itself. -/
def Ldiag : Language Bool :=
  {x | ∀ (M : Nat.Partrec.Code) (p : Polynomial ℕ),
    decode x = some (M, p) → ¬ AcceptsWithin M x (p.eval x.length)}

/-- **K-PNP-1 Part B witness statement: `Ldiag ∉ PClass`.**

STATED, NOT PROVED. This `Prop`, fully formed in the pin's
own vocabulary (`Ldiag` above, `PClass` from the frozen
PNP-1a) with every constituent defined, IS the K-PNP-1
Part B receipt: the pin's `P` is the kind of notion a
diagonal language can be stated outside of. The
time-hierarchy theorem that would prove it is T4 classical
knowledge (see the header fence), never a house theorem,
and no proof or assertion of this `Prop` appears here. -/
def KPNP1Witness : Prop := Ldiag ∉ PClass

/-- Pin self-check (T1, statement grade): `decode` unfolds
definitionally to its total Gödel decoding — a `some` for
every input, never `none` (the totality convention, proved
here only as an unfold). Proved by `rfl`. -/
theorem decode_eq (x : List Bool) :
    decode x = some (Nat.Partrec.Code.ofNatCode (Nat.unpair (natOfBoolList x)).1,
      polyOfNat (Nat.unpair (natOfBoolList x)).2) :=
  rfl

/-- Pin self-check (T1, statement grade): membership in
`Ldiag` unfolds definitionally to the audit's diagonal
clause verbatim. Proved by `Iff.rfl`. Asserts nothing about
whether any string is or is not in `Ldiag`. -/
theorem ldiag_iff (x : List Bool) :
    x ∈ Ldiag ↔ ∀ (M : Nat.Partrec.Code) (p : Polynomial ℕ),
      decode x = some (M, p) → ¬ AcceptsWithin M x (p.eval x.length) :=
  Iff.rfl

/-- Soundness link (T1): bounded acceptance is genuine
acceptance — if `M` accepts `x` within an allowance, then
the pin's unbounded semantics `Nat.Partrec.Code.eval M`
really does output `1` on `x`. This is the pin's own
`evaln_sound`; it is what keeps `AcceptsWithin` from being
an invented semantics disconnected from `Code.eval`. -/
theorem acceptsWithin_sound (M : Nat.Partrec.Code) (x : List Bool) (bound : ℕ)
    (h : AcceptsWithin M x bound) :
    (1 : ℕ) ∈ Nat.Partrec.Code.eval M (natOfBoolList x) := by
  apply Nat.Partrec.Code.evaln_sound (k := bound + natOfBoolList x + 1) (x := 1)
  rw [Option.mem_def]
  exact h

/-- Pin self-check (T1, statement grade): `KPNP1Witness`
unfolds definitionally to `Ldiag ∉ PClass` — the witness
statement in the pin's own vocabulary. Proved by `Iff.rfl`.
Stating this unfold proves no non-membership. -/
theorem kPNP1Witness_iff :
    KPNP1Witness ↔ Ldiag ∉ PClass :=
  Iff.rfl

end ThetLogos
