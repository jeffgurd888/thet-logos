import Mathlib.Tactic
import ThetLogos.HyperchargeForcing
import ThetLogos.DialOneSeatTiePin
import ThetLogos.DialOneGammaTracePin

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin

namespace ThetLogos.DialOneDoubleFlipPin

/-!
# ThetLogos.DialOneDoubleFlipPin — D1-CMP: the double-flip counterexample, PINNED

Governing text: the compensator scoping dossier
(`routeb-general-scratch/scoping-d1-compensator-2026-11-01.md`),
which fired **K-ESC-6 AT SCOPING LEVEL (T2)** and ranked this
entry first (§4 there). This brick is the STATEMENT PIN only:
the double-flip representation `piDouble` in the landed
vocabulary of `HyperchargeForcing`, the three confirmation
statements as named Props for the confirmation module
(`DialOneDoubleFlipChecks`, to come), and the kills
K-ESC-6 / K-CMP-1 / K-CMP-2 / K-CMP-3 registered on the face.
**This pin asserts NONE of the three confirmation facts.**
Entry D1-CMP is the T1 confirmation of the scoping firing —
nothing more is claimed here.

## Relabeling fence

D1-CMP is a NEW ENTRY under the relabeling rule. D1-A's kill
(`ThetLogos.HyperchargeForcing.dial1_forcing_killed`), D1-A′'s
kill (`seatTie_universal` / `kD1A1_fires_by_piFlip`), and
D1-C3's landed exclusion of piFlip (`DialOneGammaTraceChecks`:
the strengthened set `DialOneBase ∧ C3` holds for π₁ and
excludes piFlip) all stand untouched beside it at full rank.
Nothing in this module rescues, weakens, or re-reads any of
them; the landed modules are cited, never edited.

## The candidate

`piFlip` (landed, `HyperchargeForcing`) is π₁ with the ν_R
seat (slot 8) flipped to act by `star a.u1` instead of
`a.u1`. D1-C3's clause `C3` excludes piFlip because the
seat-8 perturbation alone moves the γ_F-trace by `+2α·i`.
But π₁ **already conjugates** the e_R seat (slot 9):
`pi1 a 9 9 = star a.u1` (landed `pi1_entry_eR`). The
compensator is therefore the double flip

```
piDouble a := pi1 a
  + Matrix.single s8 s8 (star a.u1 − a.u1)   -- piFlip's term, landed form
  + Matrix.single s9 s9 (a.u1 − star a.u1)   -- seat-9 mirror: un-conjugation
```

so seat 8 acts by `star a.u1`, seat 9 acts by `a.u1`, and
every other entry is π₁'s. Vocabulary note: the landed tree
names `s8` (and `s24`, `s0`) in `HyperchargeForcing` but has
no `s9`; this pin introduces `s9 := ⟨9, by omega⟩` following
the `s8` pattern exactly. No other deviation from the
scoping's formula (§1.1 there).

## The three confirmation statements — stated here, proved in the checks module to come

* **(i) `C3PiDoubleCheck : C3 piDouble`** — expected TRUE
  (scoping §1.2, T2): the seat-8 perturbation contributes
  `+2α·i` to the γ_F-trace (landed half,
  `trace_gammaF_single_s8` in `DialOneGammaTraceChecks`),
  and the seat-9 perturbation contributes `−2α·i`
  (`gammaF 9 9 = −1`, same `H_R` block; perturbation value
  at `u1Gen α β` is `α·i − star (α·i) = +2α·i`); they cancel
  exactly, over the landed `Tr (γ_F · π₁ (u1Gen α β)) = 0`.
* **(ii) `BasePiDoubleCheck : DialOneBase piDouble`** —
  expected TRUE at proof-shaped level (scoping §§1.4–1.5,
  T2): every clause of the landed base set transports off
  piFlip's landed proofs, clause by clause; the bulk is
  first-order, whose three seat coincidences at the
  (0 ↔ 8) Dirac pairing hold verbatim at the (1 ↔ 9)
  pairing (`md 9 = 1`, `md 1 = 9`; `Dval 9 = Dval 1 = Ye`;
  equal ρ-diagonal values `star b.u1` at the paired seats).
* **(iii) `NonProportionalCheck`** — expected TRUE
  (scoping §1.3, T2 arithmetic on landed tables):
  piDouble's determinant exponent is π₁'s exactly (the
  seat-8 flip's `−2α` and the seat-9 flip's `+2α` cancel),
  so its primitive unimodular direction is π₁'s own
  `(3, −1)`, and its lifted sector weights along `(3, −1)`,
  in sector order `(ν_L, e_L, u_L, d_L, ν_R, e_R, u_R, d_R)`,
  are `(−3, −3, 1, 1, −6, 0, 4, −2)` — exactly the table's
  `(−3, −3, 1, 1, 0, −6, 4, −2)` with the ν_R and e_R
  entries **swapped**. Not proportional to the COMMON
  HYPERCHARGE MATRIX: any proportionality constant is fixed
  by ν_L (`κ = 1` in this normalization), which would force
  the ν_R weight to be `0`; piDouble's is `−6`.

  **Form note (checked against the landed Prop).**
  `ThetLogos.DialOneSeatTiePin.DialOneForcing` takes no `π`
  argument: it quantifies over every `π` satisfying
  `DialOneStrengthened` (base ∧ SeatTie — not base + C3).
  So `¬ DialOneForcing piDouble` is not a well-formed
  statement, and negating `DialOneForcing` outright would
  assert a different, stronger claim than the scoping's.
  `NonProportionalCheck` therefore states the sector-vector
  non-proportionality **directly**, in `DialOneForcing`'s
  own conclusion shape instantiated at `piDouble` along
  `(3, −1)`: no scalar `κ` makes piDouble's lifted
  eigenvalues along that direction equal
  `exp (κ · t · (COMMON HYPERCHARGE MATRIX entry) · I)` at
  every sector.

**This pin asserts none of (i), (ii), (iii).** All three are
scoping arithmetic / proof-shaped transport (T2) until the
checks module lands them at T1.

## The kills, pre-registered on the face

* **K-ESC-6 (the compensator — the scoping firing, for T1
  confirmation).** Fires at T1 when all three checks land:
  a representation satisfying `DialOneBase ∧ C3` whose
  lifted weights are not proportional to the COMMON
  HYPERCHARGE MATRIX then exists in Lean, and **base + C3
  forcing is FALSE, permanently**.
* **K-CMP-1 (transport failure).** If the base transport
  FAILS at a named clause — i.e. `BasePiDoubleCheck` is
  false — piDouble is not a counterexample, the scoping
  firing is overturned, and base + C3 forcing survives this
  candidate. The failing clause is reported at full rank:
  it would localize the base set's first cross-seat grip.
* **K-CMP-2 (proportionality arithmetic).** If piDouble's
  lifted weights prove proportional to the COMMON
  HYPERCHARGE MATRIX after all — `NonProportionalCheck`
  false — K-ESC-6 does not fire and the scoping's §1.3 swap
  arithmetic is wrong at T2, reported at full rank.
* **K-CMP-3 (gate consistency).** If `C3 piDouble` fails —
  `C3PiDoubleCheck` false — the scoping's trace arithmetic
  (§1.2 there) breaks and the entry dies at the gate
  (the K-ESC-4 shape transposed).

## The lesson the scoping recorded

The base set's grip on particle seats is **per-Dirac-pair
local**: each ℂ particle seat is tied only to its own
`md`-partner through (equal `Dval`, equal ρ-diagonal). It
never sees patterns **across** particle seats. That is why
single flips passed in D1-A, and why compensating pairs
pass now (scoping §1.5, T2).

## Fence

This entry confirms a KILL of base + C3 forcing; it is not
itself a forcing attempt, and **Dial 1 stays 0 on every
outcome** — including the T1 firing of K-ESC-6 (a kill is
not a dial move). **NO CLAIM. Dial 1 = 0; all dials 0/4.
A pin is not a derivation: parts of any official statement
closed by this module: 0.**
-/

/-! ## The e_R slot -/

/-- The e_R slot (seat 9). The landed tree names `s8` in
`HyperchargeForcing` but no `s9`; this abbrev follows the
`s8` pattern exactly. -/
abbrev s9 : Fin 32 := ⟨9, by omega⟩

/-! ## The double-flip representation -/

/-- **The double-flip representation** (the K-ESC-6
compensator candidate): π₁ plus piFlip's seat-8 flip
(`star a.u1 − a.u1` at `s8`) plus the seat-9
un-conjugation (`a.u1 − star a.u1` at `s9` — π₁ already
conjugates e_R, so the mirror flip there is
un-conjugation). Seat 8 acts by `star a.u1`, seat 9 acts
by `a.u1`, every other entry is π₁'s. Defined, NOT verified
against any clause here: its `C3` membership, base-set
membership, and weight non-proportionality are the three
named checks below, asserted by no statement in this pin. -/
def piDouble (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  pi1 a + Matrix.single s8 s8 (star a.u1 - a.u1)
    + Matrix.single s9 s9 (a.u1 - star a.u1)

/-- Read-back: `piDouble` is visibly the registered
two-single perturbation of π₁. -/
theorem piDouble_unfold (a : AF) :
    piDouble a
      = pi1 a + Matrix.single s8 s8 (star a.u1 - a.u1)
        + Matrix.single s9 s9 (a.u1 - star a.u1) :=
  rfl

/-! ## The three confirmation statements (stated, NOT proved)

The checks the next stage — the module
`DialOneDoubleFlipChecks`, to come — must land for K-ESC-6
to fire at T1. They are registered here as named Props so
the checks module proves exactly these statements.
**None is asserted by this pin.** K-CMP-3 is armed against
the first, K-CMP-1 against the second, K-CMP-2 against the
third (see the header). -/

/-- **Confirmation (i), as a statement**: `C3` holds for
piDouble — the seat-8 and seat-9 γ_F-trace contributions
`+2α·i` and `−2α·i` cancel exactly (scoping §1.2).
Expected TRUE. NOT proved here — its proof is a stage of
`DialOneDoubleFlipChecks`. If it is false, K-CMP-3 fires. -/
def C3PiDoubleCheck : Prop :=
  C3 piDouble

/-- **Confirmation (ii), as a statement**: piDouble
satisfies the landed D1-A base set `DialOneBase` (as
assembled by the D1-A′ pin), clause by clause by transport
off piFlip's landed proofs; first-order over the (1 ↔ 9)
Dirac pairing is the bulk (scoping §§1.4–1.5). Expected
TRUE at proof-shaped level. NOT proved here — its proof is
a stage of `DialOneDoubleFlipChecks`. If it is false,
K-CMP-1 fires and the failing clause is the result. -/
def BasePiDoubleCheck : Prop :=
  DialOneBase piDouble

/-- **Confirmation (iii), as a statement**: piDouble's
lifted weights along its own unimodular direction
`(3, −1)` are NOT proportional to the COMMON HYPERCHARGE
MATRIX — stated directly in `DialOneForcing`'s conclusion
shape (see the header's form note): no scalar `κ` makes
the lifted eigenvalue at every sector `f` equal
`exp (κ · t · (common matrix entry at `f`) · I)`. The
scoping's concrete content (T2): the sector weight vector
is `(−3, −3, 1, 1, −6, 0, 4, −2)`, the ν_R ↔ e_R swap of
the table. Expected TRUE. NOT proved here — its proof is
a stage of `DialOneDoubleFlipChecks`. If it is false,
K-CMP-2 fires. -/
def NonProportionalCheck : Prop :=
  ¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
    (piDouble (u1ParamGen 3 (-1) t)
        * piOp (piDouble (u1ParamGen 3 (-1) t)))
        (fermionIndex f 0) (fermionIndex f 0)
      = Complex.exp (↑(κ * t)
          * commonHyperchargeMatrix (fermionIndex f 0)
              (fermionIndex f 0)
          * Complex.I)

/-- Read-back: confirmation (i) is visibly `C3 piDouble`. -/
theorem c3PiDoubleCheck_unfold :
    C3PiDoubleCheck ↔ C3 piDouble :=
  Iff.rfl

/-- Read-back: confirmation (ii) is visibly
`DialOneBase piDouble`. -/
theorem basePiDoubleCheck_unfold :
    BasePiDoubleCheck ↔ DialOneBase piDouble :=
  Iff.rfl

/-- Read-back: confirmation (iii) is visibly the registered
non-proportionality statement along `(3, −1)` against the
COMMON HYPERCHARGE MATRIX. -/
theorem nonProportionalCheck_unfold :
    NonProportionalCheck ↔
      ¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
        (piDouble (u1ParamGen 3 (-1) t)
            * piOp (piDouble (u1ParamGen 3 (-1) t)))
            (fermionIndex f 0) (fermionIndex f 0)
          = Complex.exp (↑(κ * t)
              * commonHyperchargeMatrix (fermionIndex f 0)
                  (fermionIndex f 0)
              * Complex.I) :=
  Iff.rfl

end ThetLogos.DialOneDoubleFlipPin
