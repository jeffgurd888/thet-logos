import Mathlib.Tactic
import ThetLogos.HyperchargeForcing
import ThetLogos.DialOneSeatTiePin

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation

namespace ThetLogos.DialOneGammaTracePin

/-!
# ThetLogos.DialOneGammaTracePin — D1-C3: the γ_F-trace escape condition, PINNED

Governing text: the escape scoping dossier §4
(`routeb-general-scratch/scoping-d1-escape-2026-11-01.md`,
Family 3, ranked #1 of the surviving families). This brick is
the STATEMENT PIN only: one new definition (`u1Gen`), the
condition `C3`, the strengthened set `DialOneBase ∧ C3`, the
forcing target cited from the D1-A′ pin, and the kills
K-ESC-4/5/6 registered on the face. The pre-checks are the
next stage (the checks module `DialOneGammaTraceChecks`, to
come), NOT this brick. **This pin asserts NEITHER pre-check
and attempts NO forcing.**

## Relabeling fence

D1-C3 is a NEW ENTRY under the relabeling rule. D1-A's kill
(`ThetLogos.HyperchargeForcing.dial1_forcing_killed`) and
D1-A′'s kill (`seatTie_universal` /
`kD1A1_fires_by_piFlip`, `DialOneSeatTieChecks`) stand
untouched beside it at full rank. Nothing in this module
rescues, weakens, or re-reads either theorem; the landed
modules are cited, never edited.

## The mechanism (dossier §4.1)

The landed symmetry `lifted_diag_partner` is a statement
about a **quadratic, partner-even** object: the diagonal of
`M * piOp M`. It identifies every seat's lifted entry with
its partner seat's, which is what killed D1-A and D1-A′.
`C3` escapes it by two independent features:

1. **First power.** `C3` takes `π` itself, not
   `π * piOp π`. No landed (and no true) identity forces a
   linear functional of `π a` to be partner-symmetric:
   `piOp` enters only if the statement puts it there, and
   this statement does not.
2. **Partner-odd weight.** `gammaF` is the landed grading
   (`Scaffold32`), with `gammaF (partner i) (partner i)
   = -gammaF i i` (`gammaF_partner_flip`, T1): the grading
   `diag(+I₈, −I₈, −I₈, +I₈)` on `(H_L, H_R, H_L^c, H_R^c)`.
   A γ-weighted trace therefore *adds* a seat's contribution
   and *subtracts* its partner's, instead of identifying
   them. A conjugation flip at ONE seat — piFlip's whole
   content — moves the trace by twice that seat's
   γ-weighted contribution, with no compensating move at
   the partner seat, whose π-entry piFlip does not touch.

The placement is the whole mechanism: the same `gammaF`
inserted against the *lifted* product gives `0` for every
π (dossier §1.2 (R2), kill K-ESC-7, fired at scoping). γ_F
must multiply π to the first power only.

`C3` names no weight, no sector, no Yukawa, no table. It is
a condition on π as a whole, of exactly the species of the
base set's grading clause (`∀ a, gammaF * π a = π a *
gammaF`) — γ_F was already a condition-set citizen before
this family was proposed; nothing is imported for the
purpose. γ_F's entries are the chirality grading (±1 by
L/R block), structural input of the same standing as the
sector decomposition itself: it encodes *handedness*, not
hypercharge (sectors with equal γ_F carry weights −3, 1, 0,
4 in π₁; γ_F cannot be a table in costume).

## What is pinned

* `u1Gen` — the one new definition, the only vocabulary
  gap in this family: the Lie-algebra element of
  `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)` whose exponential curve is the
  landed `u1ParamGen α β` (same seat pattern: ℂ-component,
  zero ℍ-component, scalar M₃-component; α, β bound, no
  value named).
* `C3` — the γ_F-trace condition:
  `∀ α β : ℤ, Matrix.trace (gammaF * π (u1Gen α β)) = 0`.
* `DialOneStrengthenedC3` — `DialOneBase π ∧ C3 π`, with
  `DialOneBase` the landed D1-A condition set as assembled
  by the D1-A′ pin (`DialOneSeatTiePin`). **Face note: the
  D1-A′ SeatTie is omitted because it is a theorem for
  every π (`seatTie_universal`, D1-A′ kill module) —
  including it would add nothing.**
* The forcing target, cited unchanged: the entry's target
  is `DialOneForcing` from the D1-A′ pin
  (`ThetLogos.DialOneSeatTiePin.DialOneForcing`) — forcing
  the COMMON HYPERCHARGE MATRIX's weights
  (`commonHyperchargeMatrix`, STEP 0 of that pin).
  **This pin does NOT state a new forcing Prop and does
  NOT attempt forcing** (see K-ESC-6 below); the dossier
  scopes this entry as pin + pre-checks only.

## The pre-checks — stated here, proved in the checks module to come

* **Pre-check (i): `C3 pi1`** — expected to HOLD (dossier
  §4.3, T2 arithmetic on the landed `pi1AVal`/`pi1BVal`
  tables: the γ-weighted α-coefficient sums to
  `(−1) + (+1) + 0 + (+2) + (−2) = 0` and the β-coefficient
  to `+6 − 6 = 0`). Registered below as the named Prop
  `C3Pi1Check`, to be proved in
  `DialOneGammaTraceChecks`.
* **Pre-check (ii): `¬ C3 piFlip`** — expected: piFlip
  differs from π₁ only at seat 8, where the generator entry
  flips `+iα → −iα` and `gammaF 8 8 = −1`, so the trace at
  piFlip is `2α·i`, nonzero at `(α, β) = (1, 0)`.
  Registered below as the named Prop `C3PiFlipCheck`, to
  be proved in `DialOneGammaTraceChecks`.

**This pin asserts neither `C3 pi1` nor `¬ C3 piFlip`.**
Both are scoping arithmetic (T2) until the checks module
lands them at T1.

## The kills, pre-registered on the face

* **K-ESC-4 (consistency).** If π₁ fails `C3` — i.e.
  `C3Pi1Check` is false — the entry dies as mis-posed: the
  strengthened set would exclude the corpus's one landed
  model (the K-D1A′-3 shape).
* **K-ESC-5 (counterexample / no discrimination).** If
  piFlip satisfies `C3` — i.e. `C3PiFlipCheck` is false —
  the entry dies at the gate: the clause does not
  discriminate the known counterexample (the K-D1A′-1
  shape).
* **K-ESC-6 (compensator — pre-registered against any
  forcing claim at base + C3).** `C3` is ONE linear
  equation in the raw weights (two scalar equations: the
  α- and β-coefficients). It does not, and cannot, force
  the ratios: flipping BOTH the ν_R seat (γ-trace change
  `+2α`) and the e_R seat (seat 9: γ = −1, generator
  weight `−α → +α`, change `−2α`) restores `Tr = 0` —
  the named first compensator candidate (dossier §4.5,
  T2 arithmetic; whether that double flip satisfies the
  full base set is unproved). If a representation
  satisfying `DialOneBase ∧ C3` is exhibited whose lifted
  weights are not proportional to the COMMON HYPERCHARGE
  MATRIX, then base + C3 forcing is FALSE, permanently,
  at that set. Any forcing attempt at base + C3 alone is
  therefore not priced and not attempted by this entry.

**NO CLAIM. Dial 1 = 0; all dials 0/4. A pin is not a
derivation: parts of any official statement closed by this
module: 0.**
-/

/-! ## The one new definition: the U(1) generator -/

/-- **The U(1) generator** (the only new vocabulary of
D1-C3): the Lie-algebra element of `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)`
whose exponential curve is the landed `u1ParamGen α β` —
ℂ-component `(α : ℂ) * Complex.I`, zero ℍ-component,
scalar M₃-component `(β : ℂ) * Complex.I • 1`, mirroring
`u1ParamGen`'s seat pattern. No value is named: `α` and
`β` are bound variables. -/
def u1Gen (α β : ℤ) : AF :=
  ⟨(α : ℂ) * Complex.I, 0, ((β : ℂ) * Complex.I) • (1 : Matrix I3 I3 ℂ)⟩

/-- Read-back: `u1Gen` is visibly the registered generator,
seat by seat. -/
theorem u1Gen_unfold (α β : ℤ) :
    u1Gen α β
      = ⟨(α : ℂ) * Complex.I, 0, ((β : ℂ) * Complex.I) • (1 : Matrix I3 I3 ℂ)⟩ :=
  rfl

/-! ## The condition -/

/-- **C3 — the γ_F-trace condition** (D1-C3's one new
clause): for every integer direction `(α, β)`, the trace
of the partner-odd grading `gammaF` against `π` at the
FIRST power, evaluated on the generator `u1Gen α β`,
vanishes. C3 names no weight, no sector, no Yukawa, no
table; it escapes `lifted_diag_partner` by π at the first
power against the partner-odd γ_F (see the header). -/
def C3 (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∀ α β : ℤ, Matrix.trace (gammaF * π (u1Gen α β)) = 0

/-- Read-back: `C3` is visibly the registered clause. -/
theorem c3_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    C3 π ↔
      ∀ α β : ℤ, Matrix.trace (gammaF * π (u1Gen α β)) = 0 :=
  Iff.rfl

/-! ## The strengthened set -/

/-- **The strengthened condition set of D1-C3**: the landed
base set ∧ C3, as one predicate. The D1-A′ SeatTie is
omitted because it is a theorem for every π
(`seatTie_universal`, D1-A′ kill module) — including it
would add nothing. -/
def DialOneStrengthenedC3
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ThetLogos.DialOneSeatTiePin.DialOneBase π ∧ C3 π

/-- Read-back: the strengthened set is visibly base ∧ C3. -/
theorem dialOneStrengthenedC3_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    DialOneStrengthenedC3 π
      ↔ ThetLogos.DialOneSeatTiePin.DialOneBase π ∧ C3 π :=
  Iff.rfl

/-! ## The pre-check statements (stated, NOT proved)

The two checks the next stage — the module
`DialOneGammaTraceChecks`, to come — must land before any
further step is priced. They are registered here as named
Props so the checks module proves exactly these statements.
**Neither is asserted by this pin.** K-ESC-4 is armed
against the first, K-ESC-5 against the second (see the
header). -/

/-- **Pre-check (i), as a statement**: `C3` holds for the
corpus's one landed model π₁. Expected to hold (dossier
§4.3). NOT proved here — its proof is the first stage of
`DialOneGammaTraceChecks`. If it is false, K-ESC-4 fires
and D1-C3 dies as mis-posed. -/
def C3Pi1Check : Prop :=
  C3 ThetLogos.Track1RouteB.pi1

/-- **Pre-check (ii), as a statement**: `C3` fails for
piFlip, the D1-A/D1-A′ counterexample. Expected: the trace
at piFlip is `2α·i`, nonzero at `(α, β) = (1, 0)`. NOT
proved here — its proof is the second stage of
`DialOneGammaTraceChecks`. If it is false, K-ESC-5 fires
and D1-C3 dies at the gate. -/
def C3PiFlipCheck : Prop :=
  ¬ C3 ThetLogos.HyperchargeForcing.piFlip

/-- Read-back: pre-check (i) is visibly `C3 pi1`. -/
theorem c3Pi1Check_unfold :
    C3Pi1Check ↔ C3 ThetLogos.Track1RouteB.pi1 :=
  Iff.rfl

/-- Read-back: pre-check (ii) is visibly `¬ C3 piFlip`. -/
theorem c3PiFlipCheck_unfold :
    C3PiFlipCheck ↔ ¬ C3 ThetLogos.HyperchargeForcing.piFlip :=
  Iff.rfl

end ThetLogos.DialOneGammaTracePin
