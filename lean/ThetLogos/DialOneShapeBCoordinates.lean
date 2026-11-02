import Mathlib.Tactic
import ThetLogos.DialOneLeptonChapter
import ThetLogos.DialOneSwapColourChapter

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneLeptonChapter
open ThetLogos.DialOneSwapColourChapter

namespace ThetLogos.DialOneShapeBCoordinates

/-!
# ThetLogos.DialOneShapeBCoordinates — CLS-B PIN: Shape B trace-form coordinates

Governing texts: the next-rotation scoping
(`whitepaper/next-rotation-scoping-2026-11-01.md`, Lane 1
line 117 + §1.5) and the escape scoping
(`routeb-general-scratch/scoping-d1-escape-2026-11-01.md`,
§2.1–§2.2). This brick is the PIN only: the coordinate
map, the sector-polynomial side, and the identification
Prop, stated and NOT proved. The toggle-family
identification proof is a SEPARATE later brick (priced M
in the scoping). **NO CLAIM; Dial 1 = 0; all dials 0/4.
A pin is not a derivation: parts of any official
statement closed by this module: 0.**

## What Shape B is here — and what it is not

Shape B is **DEAD as a forcing entry** (the compensator
scoping's symmetry verdict: every anomaly coefficient
sees swap-symmetric combinations only, so the whole
conjunction is blind to the full (ℤ/2)⁴ swap group;
buying it for forcing purchases a filter strictly weaker
than the clean γ-family). It is never re-ranked as a
forcing entry anywhere in this module. Its only
legitimate use, and the only one made here, is as
**coordinates on representation space**: trace
functionals of a representation `π`, defined for EVERY
`π` today — no weight-extraction gap (CLS-1's gap does
not touch them) — serving as the classification's
invariant map while CLS-1 stands open.

## The coordinate set, as frozen

The fixed AF Lie elements (`shapeBGen`, `Fin 4 → AF`),
each named with its source in the escape scoping §2.2
("the U(1) generator of §4.2; ℍ- and M₃-summand
generators for the SU(2)/SU(3) factors"):

* `genU1A := u1Gen 1 0` — the U(1) generator's
  ℂ-direction (escape §4.2's `u1Gen`, at `(α, β) = (1, 0)`);
* `genU1B := u1Gen 0 1` — the U(1) generator's
  M₃-scalar direction (at `(α, β) = (0, 1)`);
* `genHdiag := ⟨0, !![i, 0; 0, -i], 0⟩` — a diagonal
  ℍ-summand Lie element (the `iσ₃` shape in the landed
  `Matrix I2 I2 ℂ` seat of the ℍ summand);
* `genCdiag := ⟨0, 0, !![i, 0, 0; 0, -i, 0; 0, 0, 0]⟩`
  — a diagonal M₃-summand Lie element (the `iλ₃` shape).

The coordinates (`shapeBCoord π : Fin 4 → ℂ`), in the
two moment shapes of the scoping — `π ↦ Tr(γ_F · π(g))`
and `Tr(π(g) · π(h))`-type product moments over the
fixed elements above:

* index 0 — `Tr (π genCdiag * π genU1B)`: the quadratic
  M₃ × U(1) moment, mirroring the SU(3)²U(1) shape;
* index 1 — `Tr (π genHdiag * π genU1A)`: the quadratic
  ℍ × U(1) moment, mirroring the SU(2)²U(1) shape;
* index 2 — `Tr (γ_F * π genU1A)`: the γ-weighted linear
  moment, mirroring the grav–U(1) (linear) shape;
* index 3 — `Tr (π genU1A * π genU1A * π genU1A)`: the
  cubic U(1) moment, mirroring the U(1)³ shape.

These are the ANOMALY-shaped traces. They are DISTINCT
from the clean family's γ-trace coordinates
(`DialOneGammaFamilyPin` / `DialOneGammaTracePin`: the
finer instrument, already landed) — see Limit (1).

## The sector-polynomial side

`sectorPoly v : Fin 4 → ℂ` is the escape scoping §2.1's
four sector polynomials, verbatim, as functions of a
weight vector `v` in the tree's landed weight-vector
type (`Fin 32 → ℤ`, the type of `weightAt`'s vectors in
`DialOneClassificationPin`). The sector weight of a
sector `f` is read at its colour-0 representative seat,
`sectorWeight v f := v (fermionIndex f 0)` (the landed
`ThetLogos.fermionIndex`); that this representative read
is the sector's value on the toggle family is part of
the identification brick's finite check, not assumed
anywhere in this pin. In sector order
`(ν_L, e_L, u_L, d_L, ν_R, e_R, u_R, d_R)`:

* `A3  = (x_uL + x_dL) − x_uR − x_dR`
* `A2  = (x_nuL + x_eL) + 3·(x_uL + x_dL)`
* `Agrav = (x_nuL + x_eL) + 3·(x_uL + x_dL)
           − (x_nuR + x_eR) − 3·(x_uR + x_dR)`
* `A111 = (x_nuL³ + x_eL³) + 3·(x_uL³ + x_dL³)
           − (x_nuR³ + x_eR³) − 3·(x_uR³ + x_dR³)`

## The identification — stated, NOT proved

`ShapeBIdentification`: on the TOGGLE FAMILY ONLY, the
coordinates equal the sector polynomials evaluated at
the representation's weights. Its exact quantification:

* over `π₁`, over `piFlip`, and over `piEFlip`: for
  every `v` with `weightAt π v` (the LANDED relation of
  `DialOneClassificationPin` — no vector is named for
  these members in the Prop, and none is invented);
* over the landed orbit enumeration: for every bit
  pattern `b : Fin 4 → Bool` and every `v` with
  `weightAt (orbitRep b) v`. This one clause covers
  `pi1` (`orbitRep_zero`), `piDouble`
  (`orbitRep_bit0`), and every `piSwap c`
  (`orbitRep_bitSwap`), as well as the all-swap point
  `orbitRep allSwapBits`.

**THE WEIGHT-DATA GAP, named on the face.** Landed
theorems exhibiting a SPECIFIC weight vector exist for
exactly one toggle family: the single-colour swaps,
`weightAt_piSwap_swapped : weightAt (piSwap c)
(swappedWeightVector c)` (CLS-3b,
`DialOneSwapColourChapter`). For `π₁` the landed record
is existential only (`pi1_has_weights`,
`DialOneExtraction`: `∃ v, weightAt pi1 v`), with
`commonWeightVector` named as the table vector in
CLS-0's pin but no landed theorem of the form
`weightAt pi1 commonWeightVector` cited here. For
`piFlip`, `piEFlip`, `piDouble`, and the orbit points
other than the three single-colour swaps, NO landed
theorem exhibits a specific weight vector at all (for
the all-swap point the landed weight fact is negative:
`allSwap_not_weightAt_common`). The Prop therefore
quantifies over the landed `weightAt` RELATION for
every member — if some member admits no `v` at all, its
clause is vacuous, and that vacuity is part of this
named gap. It is NOT filled by inventing weights.

## The two honest limits, on the face (§1.5, verbatim in substance)

**(1) Swap-invariance.** The anomaly-shaped traces are
swap-invariant, so as coordinates they classify **at
best up to swap orbits** — which is a feature for
Grade T (they coordinatize the quotient the swaps act
on) and a hard ceiling for Grade W. The γ-trace
coordinates of the clean family are the finer
instrument and are already landed.

**(2) K-ESC-2(c) — the costume fence.** The words
"anomaly cancellation" appear in this module ONLY
inside this fence sentence: calling these coordinates
by that name anywhere without the CLS-B identification
theorem is costume — kill on sight. An unproved Shape B
is a different condition wearing that name; this pin
ships the coordinates and the stated Prop, and no such
name.

## Kills registered on the face

* **K-ESC-2(c)** (costume, inherited): as in Limit (2)
  above.
* **K-CLS-B** (resolution, registered here): if the
  trace coordinates fail to separate two realized toggle
  orbits, the instrument's resolution is reported at
  exactly that coarseness — a verdict for the
  identification brick, never silently upgraded.
-/

/-! ## The fixed AF Lie elements -/

/-- **The U(1) generator, ℂ-direction**: the landed
`u1Gen` (escape §4.2 / `DialOneGammaTracePin`) at
`(α, β) = (1, 0)`. -/
def genU1A : AF := u1Gen 1 0

/-- **The U(1) generator, M₃-scalar direction**: the
landed `u1Gen` at `(α, β) = (0, 1)`. -/
def genU1B : AF := u1Gen 0 1

/-- **A diagonal ℍ-summand Lie element**: zero ℂ- and
M₃-components, ℍ-component the `iσ₃` shape
`!![i, 0; 0, -i]` in the landed `Matrix I2 I2 ℂ` seat
of the ℍ summand of `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)`. -/
def genHdiag : AF :=
  ⟨0, !![Complex.I, 0; 0, -Complex.I], 0⟩

/-- **A diagonal M₃-summand Lie element**: zero ℂ- and
ℍ-components, M₃-component the `iλ₃` shape
`!![i, 0, 0; 0, -i, 0; 0, 0, 0]`. -/
def genCdiag : AF :=
  ⟨0, 0, !![Complex.I, 0, 0; 0, -Complex.I, 0; 0, 0, 0]⟩

/-- **The named finite set of fixed AF Lie elements**
over which the Shape B moments are taken, as a function
on `Fin 4`: index 0 = `genU1A`, 1 = `genU1B`,
2 = `genHdiag`, 3 = `genCdiag`. -/
def shapeBGen : Fin 4 → AF :=
  ![genU1A, genU1B, genHdiag, genCdiag]

/-- Read-back: the fixed set is visibly the four named
elements, in the registered order. -/
theorem shapeBGen_unfold :
    shapeBGen = ![genU1A, genU1B, genHdiag, genCdiag] :=
  rfl

/-! ## The moment shapes -/

/-- **The γ-weighted linear moment**: `Tr (γ_F · π g)`
— the first of the scoping's two Shape B moment shapes.
Defined for every `π` and every fixed `g`; no weight
extraction is involved. -/
def gammaMoment (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (g : AF) : ℂ :=
  Matrix.trace (gammaF * π g)

/-- **The quadratic product moment**: `Tr (π g * π h)`
— the second of the scoping's two Shape B moment
shapes. Defined for every `π`; no weight extraction is
involved. -/
def prodMoment (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (g h : AF) : ℂ :=
  Matrix.trace (π g * π h)

/-- **The cubic product moment**: `Tr (π g * π g * π g)`
— the product-moment shape at three factors, mirroring
the U(1)³ coefficient's degree. Defined for every `π`. -/
def cubicMoment (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (g : AF) : ℂ :=
  Matrix.trace (π g * π g * π g)

/-- Read-back: the γ-weighted linear moment is visibly
`Tr (γ_F · π g)`. -/
theorem gammaMoment_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (g : AF) :
    gammaMoment π g = Matrix.trace (gammaF * π g) :=
  rfl

/-- Read-back: the quadratic product moment is visibly
`Tr (π g * π h)`. -/
theorem prodMoment_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (g h : AF) :
    prodMoment π g h = Matrix.trace (π g * π h) :=
  rfl

/-- Read-back: the cubic product moment is visibly
`Tr (π g * π g * π g)`. -/
theorem cubicMoment_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (g : AF) :
    cubicMoment π g = Matrix.trace (π g * π g * π g) :=
  rfl

/-! ## The coordinate map -/

/-- **The Shape B coordinate map** (CLS-B's instrument):
the finite tuple of anomaly-shaped trace functionals,
as a function on `Fin 4`. Index 0 is the quadratic
M₃ × U(1) moment (the SU(3)²U(1) mirror), index 1 the
quadratic ℍ × U(1) moment (the SU(2)²U(1) mirror),
index 2 the γ-weighted linear U(1) moment (the
grav–U(1) mirror), index 3 the cubic U(1) moment (the
U(1)³ mirror). Defined for EVERY representation `π` —
this is the classification's invariant map while the
CLS-1 extraction gap stands. **Swap-invariance limit
(Limit (1) of the header): these coordinates classify
at best up to swap orbits.** -/
def shapeBCoord (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    Fin 4 → ℂ :=
  ![prodMoment π genCdiag genU1B,
    prodMoment π genHdiag genU1A,
    gammaMoment π genU1A,
    cubicMoment π genU1A]

/-- Read-back: the coordinate tuple is visibly the four
registered moments, in the registered order. -/
theorem shapeBCoord_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    shapeBCoord π
      = ![prodMoment π genCdiag genU1B,
          prodMoment π genHdiag genU1A,
          gammaMoment π genU1A,
          cubicMoment π genU1A] :=
  rfl

/-! ## The sector-polynomial side -/

/-- **The sector weight of a sector, from a weight
vector**: the value of the per-seat vector `v` (the
tree's weight-vector type, `Fin 32 → ℤ`) at the
sector's colour-0 representative seat
`fermionIndex f 0` (landed, `ThetLogos.SMFermions`). -/
def sectorWeight (v : Fin 32 → ℤ) (f : SMFermion) : ℤ :=
  v (fermionIndex f 0)

/-- **A3, the SU(3)²U(1) sector polynomial** (escape
scoping §2.1, verbatim): `(x_uL + x_dL) − x_uR − x_dR`
in the sector weights of the weight vector `v`. -/
def sectorA3 (v : Fin 32 → ℤ) : ℤ :=
  (sectorWeight v .uL + sectorWeight v .dL)
    - sectorWeight v .uR - sectorWeight v .dR

/-- **A2, the SU(2)²U(1) sector polynomial** (escape
scoping §2.1, verbatim): `(x_nuL + x_eL) + 3·(x_uL +
x_dL)`. -/
def sectorA2 (v : Fin 32 → ℤ) : ℤ :=
  (sectorWeight v .nuL + sectorWeight v .eL)
    + 3 * (sectorWeight v .uL + sectorWeight v .dL)

/-- **Agrav, the grav–U(1) sector polynomial** (escape
scoping §2.1, verbatim): `(x_nuL + x_eL) + 3·(x_uL +
x_dL) − (x_nuR + x_eR) − 3·(x_uR + x_dR)`. -/
def sectorAgrav (v : Fin 32 → ℤ) : ℤ :=
  (sectorWeight v .nuL + sectorWeight v .eL)
    + 3 * (sectorWeight v .uL + sectorWeight v .dL)
    - (sectorWeight v .nuR + sectorWeight v .eR)
    - 3 * (sectorWeight v .uR + sectorWeight v .dR)

/-- **A111, the U(1)³ sector polynomial** (escape
scoping §2.1, verbatim): `(x_nuL³ + x_eL³) + 3·(x_uL³ +
x_dL³) − (x_nuR³ + x_eR³) − 3·(x_uR³ + x_dR³)`. -/
def sectorA111 (v : Fin 32 → ℤ) : ℤ :=
  (sectorWeight v .nuL ^ 3 + sectorWeight v .eL ^ 3)
    + 3 * (sectorWeight v .uL ^ 3 + sectorWeight v .dL ^ 3)
    - (sectorWeight v .nuR ^ 3 + sectorWeight v .eR ^ 3)
    - 3 * (sectorWeight v .uR ^ 3 + sectorWeight v .dR ^ 3)

/-- **The sector-polynomial side**: the four Shape B
sector polynomials of the weight vector `v`, cast to
`ℂ`, as a function on `Fin 4` in the registered order
`![A3, A2, Agrav, A111]` — the same index order as
`shapeBCoord`. -/
def sectorPoly (v : Fin 32 → ℤ) : Fin 4 → ℂ :=
  ![(sectorA3 v : ℂ), (sectorA2 v : ℂ),
    (sectorAgrav v : ℂ), (sectorA111 v : ℂ)]

/-- Read-back: the sector-polynomial tuple is visibly
the four registered polynomials, in the registered
order. -/
theorem sectorPoly_unfold (v : Fin 32 → ℤ) :
    sectorPoly v
      = ![(sectorA3 v : ℂ), (sectorA2 v : ℂ),
          (sectorAgrav v : ℂ), (sectorA111 v : ℂ)] :=
  rfl

/-! ## The identification — stated, NOT proved -/

/-- **The CLS-B identification, as a statement — OPEN,
NOT proved here.** On the toggle family only, the
Shape B coordinates equal the sector polynomials at the
representation's weights. The quantification is exactly:

* `π₁`: every `v` with the landed relation
  `weightAt pi1 v`;
* `piFlip`: every `v` with `weightAt piFlip v`;
* `piEFlip` (CLS-3a's fourth lepton toggle): every `v`
  with `weightAt piEFlip v`;
* the landed orbit enumeration: every bit pattern
  `b : Fin 4 → Bool` (the 16 points of
  `DialOneSwapOrbit.orbitRep`, covering `piDouble` and
  every `piSwap c` by the landed `orbitRep_bit0` /
  `orbitRep_bitSwap`) and every `v` with
  `weightAt (orbitRep b) v`.

**Weight-data gap (named on the face of the header):**
a specific landed weight vector exists only for the
single-colour swaps (`weightAt_piSwap_swapped`, CLS-3b);
for the other members the Prop speaks through the
landed `weightAt` relation alone, and a member admitting
no `v` contributes a vacuous clause — the gap is named,
never filled by invented weights. The proof of this
Prop, where it is a finite computation on the toggle
family, is the SEPARATE identification brick; K-ESC-2(c)
and K-CLS-B are armed against it and against any use of
these coordinates beyond it (see the header). -/
def ShapeBIdentification : Prop :=
  (∀ v, weightAt pi1 v → shapeBCoord pi1 = sectorPoly v)
    ∧ (∀ v, weightAt ThetLogos.HyperchargeForcing.piFlip v
        → shapeBCoord ThetLogos.HyperchargeForcing.piFlip
          = sectorPoly v)
    ∧ (∀ v, weightAt piEFlip v
        → shapeBCoord piEFlip = sectorPoly v)
    ∧ (∀ (b : Fin 4 → Bool) v, weightAt (orbitRep b) v
        → shapeBCoord (orbitRep b) = sectorPoly v)

/-- Read-back: the identification is visibly the
registered four-clause quantification over the toggle
family, through the landed `weightAt` relation only. -/
theorem shapeBIdentification_unfold :
    ShapeBIdentification ↔
      (∀ v, weightAt pi1 v → shapeBCoord pi1 = sectorPoly v)
        ∧ (∀ v, weightAt ThetLogos.HyperchargeForcing.piFlip v
            → shapeBCoord ThetLogos.HyperchargeForcing.piFlip
              = sectorPoly v)
        ∧ (∀ v, weightAt piEFlip v
            → shapeBCoord piEFlip = sectorPoly v)
        ∧ (∀ (b : Fin 4 → Bool) v, weightAt (orbitRep b) v
            → shapeBCoord (orbitRep b) = sectorPoly v) :=
  Iff.rfl

end ThetLogos.DialOneShapeBCoordinates
