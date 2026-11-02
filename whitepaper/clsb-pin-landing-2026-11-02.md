# CLS-B PIN LANDING DOSSIER — 2026-11-02

**Item:** CLS-B pin (Dial-1 classification lane) — Shape B
trace-form coordinates, pinned as a classification
instrument ONLY (dead as a forcing entry; never re-ranked).

## VERDICT: PIN LANDED

**Artifact:** `lean/ThetLogos/DialOneShapeBCoordinates.lean`
— strict 7, defs 16. Verified by the coordinator in the
main tree (build green, 3531 jobs). Pin-grade: definitions
+ a stated Prop; the identification proof is the separate
M brick behind this pin.

**Frozen coordinates:** `shapeBGen : Fin 4 → AF` — four
fixed Lie elements: the two landed U(1) generators
`u1Gen 1 0`, `u1Gen 0 1`, an ℍ-summand diagonal, and an
M₃-summand diagonal. `shapeBCoord π : Fin 4 → ℂ` = the four
trace moments mirroring the escape scoping's Shape B
shapes — Tr(π genCdiag · π genU1B) (SU(3)²U(1) mirror),
Tr(π genHdiag · π genU1A) (SU(2)²U(1) mirror),
Tr(γF · π genU1A) (grav–U(1) mirror), Tr(π genU1A³)
(U(1)³ mirror) — defined for **every** π: no extraction
gap. `sectorPoly v : Fin 4 → ℂ` = the scoping §2.1 sector
polynomials verbatim, as functions of the weight-vector
type `Fin 32 → ℤ` (colour-0 representative read, flagged
on the face as the identification brick's check).

**The stated identification** (`ShapeBIdentification`, NOT
proved here): coordinates = sector polynomials at the
representation's weights, quantified over the landed
toggle family THROUGH THE LANDED `weightAt` RELATION ALONE
— π₁, piFlip, piEFlip, and every orbitRep point (covering
piDouble and every piSwap c via the landed bit lemmas).
**The weight-data gap is named on the face:** only the
single-colour swaps carry a landed specific weight vector
(CLS-3b); π₁ has only the existential `pi1_has_weights`;
several members have no landed specific vector, and a
member admitting no v contributes a vacuous clause —
recorded as part of the gap, never filled by invention.

**Face fences:** the swap-invariance limit (the coordinates
classify **at best up to swap orbits** — a feature for
Grade T, a hard ceiling for Grade W; the clean family's
γ-trace coordinates are the finer instrument and are
already landed); **K-ESC-2(c)** — the phrase "anomaly
cancellation" occurs exactly once in the module, inside
its fence sentence; **K-CLS-B** registered (the
instrument's resolution is reported at its true coarseness
by the identification brick, never silently upgraded).

## Fences

NO CLAIM; **Dial 1: 0.**

**Census after landing: 12,252 strict / 12,657 total / 421 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
