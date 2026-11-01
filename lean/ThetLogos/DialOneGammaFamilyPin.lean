import Mathlib.Tactic
import ThetLogos.HyperchargeForcing
import ThetLogos.DialOneSeatTiePin
import ThetLogos.DialOneGammaTracePin
import ThetLogos.DialOneDoubleFlipPin

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin

namespace ThetLogos.DialOneGammaFamilyPin

/-!
# ThetLogos.DialOneGammaFamilyPin — D1-CMP-FAM: the clean-tier γ-trace family, PINNED

Governing text: the compensator scoping dossier §2.3 and §4
Rank 2 (`routeb-general-scratch/scoping-d1-compensator-2026-11-01.md`).
This brick is the STATEMENT PIN only: the diagonal seat
projections, the four functionals (five clauses) of the
clean tier, the family predicate `GammaFamily`, the
strengthened set `DialOneBase ∧ C3 ∧ GammaFamily`, the
pre-check statements for the checks module
(`DialOneGammaFamilyChecks`, to come), and the kills
K-CMP-F1/F2/F3 registered on the face. **This pin asserts
NONE of its pre-checks. No forcing is attempted at this
set, ever, in this entry** (the scoping's fence: the honest
frontier after D1-CMP is the base-set realizability
classification, L+, unscoped).

## Relabeling fence

D1-CMP-FAM is a NEW ENTRY under the relabeling rule.
D1-A's kill (`dial1_forcing_killed`), D1-A′'s kill
(`seatTie_universal` / `kD1A1_fires_by_piFlip`), D1-C3's
landed exclusion of piFlip (`DialOneGammaTraceChecks`), and
D1-CMP's landed firing of K-ESC-6 at T1 (`piDouble`
satisfies `DialOneBase ∧ C3` with ν_R ↔ e_R swapped,
non-table weights — base + C3 forcing is FALSE) all stand
untouched beside it at full rank. Nothing in this module
rescues, weakens, or re-reads any of them; the landed
modules are cited, never edited. The forcing target is
cited unchanged from the D1-A′ pin: `DialOneForcing`,
forcing the COMMON HYPERCHARGE MATRIX's weights
(`commonHyperchargeMatrix`). **This pin does NOT state a
new forcing Prop and does NOT attempt forcing.**

## The projections — one definition pattern, exact seat sets

One pattern (`seatProj`): a diagonal 0/1 seat indicator,
`Matrix.diagonal` of the indicator of a partner-closed
seat set. The set is named by its particle-side pair
representatives (the dossier's pair-set notation: pair `p`
is the seat pair `{p, partner p}` under the landed
`partner` involution, `partner i = i + 16` for `i < 16`),
and `seatProj` takes the union of the named pairs' seats —
each representative together with its partner. No table
VALUES are named anywhere: the projections are 0/1 seat
indicators only. The exact seat sets are:

* **Lepton** (`lepProj`), representatives `{0, 1, 8, 9}`
  (the pairs ν_L, e_L, ν_R, e_R): seats
  `{0, 1, 8, 9, 16, 17, 24, 25}`.
* **Colour `c`** (`colProj c`), for `c : Fin 3`,
  representatives `{2+2c, 3+2c, 10+2c, 11+2c}` (the pairs
  q_L of colour `c` — up and down — and u_R^c, d_R^c):
  seats `{2+2c, 3+2c, 10+2c, 11+2c, 18+2c, 19+2c, 26+2c,
  27+2c}`; concretely `{2, 3, 10, 11, 18, 19, 26, 27}` for
  `c = 0`, `{4, 5, 12, 13, 20, 21, 28, 29}` for `c = 1`,
  `{6, 7, 14, 15, 22, 23, 30, 31}` for `c = 2`.
* **e_R** (`eRProj`), representative `{9}`: seats
  `{9, 25}` — the e_R pair, named by its particle side
  (seat 9), per the dossier.

Seat-set exactness is gated by the π₁ pre-checks in the
checks module: a wrong seat set fails loudly there (the
`(0, 0)` values are the test; K-CMP-F2 is armed).

## The functionals — one pattern

Each clause is γ_F composed with a projection, π at the
FIRST power (the D1-C3 placement: no `piOp`, no lifted
product), stated in the order
`Matrix.trace (gammaF * proj * π (u1Gen α β))` — matrix
multiplication is left-associative, and trace cyclicity
makes the other readings of the composition agree; this
order is the one registered. The clauses:

* `C3lep π` — γ_F · lepton projection; π₁ value expected
  `(0, 0)` (dossier §2.3, T2: a NEW computation, a sub-sum
  of C3's; not implied by it). Toggle form: `f₈ − f₉`.
* `C3col c π` for `c : Fin 3` — γ_F · colour-`c`
  projection; π₁ value expected `(0, 0)` each (T2, new
  computations). Toggle form: `f_{u^c} − f_{d^c}`.
* `FeR π` — γ_F · e_R projection; π₁ value `(0, 0)` (T2):
  pair 9 is the unique pair whose particle and
  antiparticle raw weights already agree in π₁.

C3 is implied by `C3lep + Σ_c C3col c` (the pair-sets
partition the 16 pairs) — C3 is kept in the strengthened
set anyway; it is the landed clause.

**Joint toggle kernel (dossier §2.3, T2, enumerated):**
with all five clauses the kernel over the 256 particle-seat
conjugation toggles is exactly the three per-colour quark
double flips `{(10,11)}`, `{(12,13)}`, `{(14,15)}` and
their unions — 8 of 256 toggles. The named ν_R+e_R
compensator (piDouble) is dead in this tier. The scoping
no-go (§2.5 there) stands beside this pin at full rank:
no family of γ-trace functionals built from γ_F and landed
sector/colour projections separates u_R^c from d_R^c within
a colour — the per-colour swaps are invisible in principle
to the clean tier, which is exactly why their base tests
are this entry's remaining content.

## F_eR's weak motivation — on the face, load-bearing flag

**F_eR is a two-seat tie in raw weights** (`A₉ = A₂₅ ∧
B₉ = B₂₅` over the base set): it names no value and fixes
no seat, so it passes the fence under the operational
reading — **but it holds for π₁ at exactly one pair, and
that accident is its entire motivation. It is the clean
tier's weakest member, and it is LOAD-BEARING against the
lepton swap: without it the joint kernel is 16 toggles,
not 8** (the `(8, 9)` double flip — piDouble itself —
re-enters). **The family is to be reported with and
without F_eR**, in the checks module and in any public
sentence, at every stage of this entry.

## The pre-checks — stated here, proved in the checks module to come

* **(i) `GammaFamilyPi1Check : GammaFamily pi1`** —
  expected to HOLD, every clause at `(0, 0)` (dossier
  §2.3, T2). These are NEW computations, sub-sums of C3's
  landed sums; C3 does not imply them.
* **(ii) `PiDoubleFamilyCheck`** — expected to HOLD in the
  registered shape: `C3lep piDouble` holds (the ν_R/e_R
  compensation is internal to the lepton sector), every
  `C3col c piDouble` holds (piDouble's quark entries are
  π₁'s), and `FeR piDouble` FAILS — piDouble fails the
  family **by F_eR alone**, which is the load-bearing flag
  above made concrete.
* **(iii) `QuarkSwapCheck piSwap`** — for the per-colour
  double flip `piSwap c` (constructed in the checks module
  on piDouble's pattern: conjugation toggles at colour
  `c`'s `(u_R^c, d_R^c)` particle seats `10+2c`, `11+2c`),
  the conjunction, for every colour `c`, of: family
  vanishing (`GammaFamily (piSwap c)` — expected to HOLD,
  by the kernel enumeration: the swaps are the family's
  kernel), base membership (`DialOneBase (piSwap c)` —
  the transport test, the same species as piDouble's
  §1.5 transport at the md-pairs `2 ↔ 10`, `3 ↔ 11`), and
  non-proportionality of the lifted weights along
  `(3, −1)` in `DialOneForcing`'s own conclusion shape
  (expected to HOLD: the sector vector differs from the
  table in colour `c`'s sectors only — the u_R^c ↔ d_R^c
  lifted weights are swapped; the direction is `(3, −1)`
  because the two toggles' determinant contributions
  `−2α` and `+2α` cancel, exactly as for piDouble).
  `piSwap` is a bound argument of the registered Prop:
  this pin names no swap candidate of its own.

**This pin asserts none of (i), (ii), (iii).** All are
scoping arithmetic / proof-shaped transport (T2) until the
checks module lands them — or kills them — at T1.

## The kills, pre-registered on the face

* **K-CMP-F1 (quark-swap counterexample).** If a quark swap
  satisfies base + family with non-table weights — i.e.
  `QuarkSwapCheck piSwap` lands for the checks module's
  `piSwap` — then **forcing at base + clean family is
  FALSE, permanently**, exactly as K-ESC-6 fired for
  base + C3.
* **K-CMP-F2 (consistency / seat-set).** If π₁ fails a
  family clause — `GammaFamilyPi1Check` false — that
  clause is mis-posed / its seat set is wrong: it dies
  from the family and the pin is corrected at full rank,
  never quietly (the K-ESC-4 shape).
* **K-CMP-F3 (F_eR arithmetic).** If piDouble passes the
  whole family — in particular if `FeR piDouble` holds —
  the F_eR arithmetic was wrong and the family's lepton
  exclusion claim dies: the clean tier then does NOT
  exclude the ν_R+e_R compensator.

**Standing outcome fence.** If the swaps FAIL base, the
landed conclusion is exactly "base + clean family excludes
every toggle compensator" — a **toggle-level exclusion,
NOT a forcing theorem**: non-toggle representations are
the unscoped classification question (base-set
realizability, L+), and no sentence of this entry may be
read past that fence.

**NO CLAIM. Dial 1 = 0; all dials 0/4. A pin is not a
derivation: parts of any official statement closed by this
module: 0.**
-/

/-! ## The projections: one definition pattern -/

/-- **The seat-projection pattern**: the diagonal 0/1
indicator of the partner-closed seat set named by its
particle-side pair representatives `reps` — seat `i` is
selected iff `i ∈ reps ∪ partner '' reps`, i.e. iff `i`
is a named representative or the `partner` of one. The
only projection pattern of this pin; no table values are
named, only seats. -/
def seatProj (reps : Finset (Fin 32)) : Matrix (Fin 32) (Fin 32) ℂ :=
  Matrix.diagonal (fun i => if i ∈ reps ∪ Finset.image partner reps then 1 else 0)

/-- **The lepton projection**: representatives
`{0, 1, 8, 9}` (pairs ν_L, e_L, ν_R, e_R), seat set
`{0, 1, 8, 9, 16, 17, 24, 25}`. -/
def lepProj : Matrix (Fin 32) (Fin 32) ℂ :=
  seatProj {0, 1, 8, 9}

/-- **The colour-`c` quark projection**, for `c : Fin 3`:
representatives `{2+2c, 3+2c, 10+2c, 11+2c}` (pairs q_L
up/down of colour `c`, u_R^c, d_R^c), seat set
`{2+2c, 3+2c, 10+2c, 11+2c, 18+2c, 19+2c, 26+2c, 27+2c}`. -/
def colProj (c : Fin 3) : Matrix (Fin 32) (Fin 32) ℂ :=
  seatProj {⟨2 + 2 * c.val, by have hc := c.isLt; omega⟩,
    ⟨3 + 2 * c.val, by have hc := c.isLt; omega⟩,
    ⟨10 + 2 * c.val, by have hc := c.isLt; omega⟩,
    ⟨11 + 2 * c.val, by have hc := c.isLt; omega⟩}

/-- **The e_R projection**: representative `{9}` (the
particle side, per the dossier), seat set `{9, 25}` — the
e_R pair. This projection's clause is the family's
weakest-motivation, load-bearing member (see the header). -/
def eRProj : Matrix (Fin 32) (Fin 32) ℂ :=
  seatProj {9}

/-! ## The functionals: one pattern, five clauses -/

/-- **C3lep — the lepton γ-trace clause**: for every
integer direction `(α, β)`, the trace of γ_F composed
with the lepton projection against `π` at the FIRST
power, evaluated on the generator `u1Gen α β`, vanishes.
Expected π₁ value `(0, 0)` (T2, new computation). -/
def C3lep (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∀ α β : ℤ, Matrix.trace (gammaF * lepProj * π (u1Gen α β)) = 0

/-- **C3col `c` — the per-colour γ-trace clause** for
colour `c : Fin 3`: γ_F composed with the colour-`c`
projection, π at the first power, trace vanishing at
every direction. Expected π₁ value `(0, 0)` for each `c`
(T2, new computations). -/
def C3col (c : Fin 3) (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∀ α β : ℤ, Matrix.trace (gammaF * colProj c * π (u1Gen α β)) = 0

/-- **FeR — the e_R γ-trace clause**: γ_F composed with
the e_R projection, π at the first power, trace vanishing
at every direction. **Weak motivation, on the face**: a
two-seat tie in raw weights (`A₉ = A₂₅ ∧ B₉ = B₂₅`)
holding for π₁ at exactly one pair — that accident is its
entire motivation; it is the clean tier's weakest member
and is **LOAD-BEARING** against the lepton swap (without
it the joint kernel is 16 toggles, not 8). The family is
reported with and without it. -/
def FeR (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∀ α β : ℤ, Matrix.trace (gammaF * eRProj * π (u1Gen α β)) = 0

/-- Read-back: `C3lep` is visibly the registered clause. -/
theorem c3lep_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    C3lep π ↔
      ∀ α β : ℤ, Matrix.trace (gammaF * lepProj * π (u1Gen α β)) = 0 :=
  Iff.rfl

/-- Read-back: `C3col` is visibly the registered clause. -/
theorem c3col_unfold (c : Fin 3) (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    C3col c π ↔
      ∀ α β : ℤ, Matrix.trace (gammaF * colProj c * π (u1Gen α β)) = 0 :=
  Iff.rfl

/-- Read-back: `FeR` is visibly the registered clause. -/
theorem feR_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    FeR π ↔
      ∀ α β : ℤ, Matrix.trace (gammaF * eRProj * π (u1Gen α β)) = 0 :=
  Iff.rfl

/-! ## The family predicate and the strengthened set -/

/-- **The clean-tier γ-trace family**: the lepton clause,
every per-colour clause, and the e_R clause, as one
predicate. Reported with and without `FeR` (its weakest,
load-bearing member — see the header). -/
def GammaFamily (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  C3lep π ∧ (∀ c, C3col c π) ∧ FeR π

/-- **The strengthened condition set of D1-CMP-FAM**: the
landed base set ∧ the landed C3 ∧ the clean-tier family,
as one predicate. **No forcing is attempted at this set,
ever, in this entry.** -/
def DialOneStrengthenedFam
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ThetLogos.DialOneSeatTiePin.DialOneBase π ∧ C3 π ∧ GammaFamily π

/-- Read-back: the family is visibly
`C3lep ∧ (∀ c, C3col c) ∧ FeR`. -/
theorem gammaFamily_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    GammaFamily π ↔ C3lep π ∧ (∀ c, C3col c π) ∧ FeR π :=
  Iff.rfl

/-- Read-back: the strengthened set is visibly
base ∧ C3 ∧ family. -/
theorem dialOneStrengthenedFam_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    DialOneStrengthenedFam π
      ↔ ThetLogos.DialOneSeatTiePin.DialOneBase π ∧ C3 π ∧ GammaFamily π :=
  Iff.rfl

/-! ## The pre-check statements (stated, NOT proved)

The checks the next stage — the module
`DialOneGammaFamilyChecks`, to come — must land before any
further step is priced. They are registered here as named
Props so the checks module proves exactly these statements.
**None is asserted by this pin.** K-CMP-F2 is armed against
the first, K-CMP-F3 against the second, K-CMP-F1 against
the third (see the header). -/

/-- **Pre-check (i), as a statement**: the family holds
for the corpus's one landed model π₁, every clause at
`(0, 0)`. Expected TRUE (dossier §2.3, T2 — new
computations, sub-sums of C3's; not implied by C3). NOT
proved here. If it is false, K-CMP-F2 fires: the failing
clause is mis-posed / its seat set is wrong. -/
def GammaFamilyPi1Check : Prop :=
  GammaFamily ThetLogos.Track1RouteB.pi1

/-- **Pre-check (ii), as a statement**: piDouble — the
landed K-ESC-6 compensator — passes the lepton clause
(the compensation is internal to the lepton sector) and
every colour clause (its quark entries are π₁'s), and
FAILS `FeR`: piDouble fails the family **by F_eR alone**.
Expected TRUE in this shape (dossier §2.3, T2). NOT proved
here. If the `¬ FeR piDouble` conjunct is false, K-CMP-F3
fires and the family's lepton exclusion claim dies. -/
def PiDoubleFamilyCheck : Prop :=
  C3lep piDouble ∧ (∀ c, C3col c piDouble) ∧ ¬ FeR piDouble

/-- **Pre-check (iii), as a statement**: for the
per-colour double flip `piSwap` (constructed in the checks
module on piDouble's pattern at colour `c`'s
`(u_R^c, d_R^c)` toggle seats — a bound argument here;
this pin names no swap candidate), every colour `c`'s
swap lies in the family's kernel, satisfies the landed
base set, and has lifted weights along `(3, −1)` not
proportional to the COMMON HYPERCHARGE MATRIX — stated in
`DialOneForcing`'s own conclusion shape, mirroring
`DialOneDoubleFlipPin.NonProportionalCheck`. Expected:
family vanishing and non-proportionality HOLD (the sector
vector differs from the table in colour `c`'s sectors
only); base membership is the transport test. NOT proved
here. If it lands in full, K-CMP-F1 fires: forcing at
base + clean family is FALSE, permanently. If instead
some swap's base membership fails, the standing outcome
fence applies (toggle-level exclusion only — see the
header). -/
def QuarkSwapCheck
    (piSwap : Fin 3 → AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∀ c, ThetLogos.DialOneSeatTiePin.DialOneBase (piSwap c)
    ∧ GammaFamily (piSwap c)
    ∧ ¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      ((piSwap c) (u1ParamGen 3 (-1) t)
          * piOp ((piSwap c) (u1ParamGen 3 (-1) t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * t)
            * commonHyperchargeMatrix (fermionIndex f 0)
                (fermionIndex f 0)
            * Complex.I)

/-- Read-back: pre-check (i) is visibly
`GammaFamily pi1`. -/
theorem gammaFamilyPi1Check_unfold :
    GammaFamilyPi1Check ↔ GammaFamily ThetLogos.Track1RouteB.pi1 :=
  Iff.rfl

/-- Read-back: pre-check (ii) is visibly the registered
piDouble shape — lepton and colour clauses hold, `FeR`
fails. -/
theorem piDoubleFamilyCheck_unfold :
    PiDoubleFamilyCheck ↔
      C3lep piDouble ∧ (∀ c, C3col c piDouble) ∧ ¬ FeR piDouble :=
  Iff.rfl

/-- Read-back: pre-check (iii) is visibly the registered
per-colour conjunction (base ∧ family ∧
non-proportionality along `(3, −1)`), for the bound
`piSwap`. -/
theorem quarkSwapCheck_unfold
    (piSwap : Fin 3 → AF → Matrix (Fin 32) (Fin 32) ℂ) :
    QuarkSwapCheck piSwap ↔
      ∀ c, ThetLogos.DialOneSeatTiePin.DialOneBase (piSwap c)
        ∧ GammaFamily (piSwap c)
        ∧ ¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
          ((piSwap c) (u1ParamGen 3 (-1) t)
              * piOp ((piSwap c) (u1ParamGen 3 (-1) t)))
              (fermionIndex f 0) (fermionIndex f 0)
            = Complex.exp (↑(κ * t)
                * commonHyperchargeMatrix (fermionIndex f 0)
                    (fermionIndex f 0)
                * Complex.I) :=
  Iff.rfl

end ThetLogos.DialOneGammaFamilyPin
