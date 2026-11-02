# CLS-B-ID DOSSIER — K-CLS-B FIRED: ShapeBIdentification REFUTED — 2026-11-02

**Item:** CLS-B-ID (Lane 1, behind the CLS-B pin) — prove or
refute the frozen `ShapeBIdentification` on the toggle family.

## VERDICT: REFUTED (T1) — K-CLS-B FIRES

**Artifact:** `lean/ThetLogos/DialOneShapeBIdentification.lean`
— strict 127, defs 13. Verified by the coordinator in the
main tree (build green); all 13 headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

**The fiber question closed completely** — no PARTIAL seam
was needed: at every realized member the weight fiber is
exactly `{E_π, −E_π}` (directions pinned: π₁ ±(3,−1) by det
shape −4α−12β; piFlip ±(−2,1); piEFlip ±(−6,1); colour
swaps never move the determinant character). **And the
identification fails at the positive fiber point of every
member, at a named index:**

| member | clause killed at | coordinate | sector value |
|---|---|---|---|
| pi1 | index 3 | 4i | 0 |
| piFlip | index 1 | 0 | −2 |
| piEFlip | index 1 | 0 | 6 |
| orbitRep b (all 16) | index 3 | 4i | 0 |

Headline `not_shapeBIdentification`, with the per-clause
kills in-tree. The frozen Prop was never weakened — it was
tested as frozen and it is false as frozen.

**Pin-shape finding (on the record):** the colour-0
representative read in `sectorPoly` is NOT the obstruction
(the sector polynomials see only the symmetric pair sums);
the obstruction is structural — the coordinates are π-alone
traces, the sector side is built from the lifted (π⊗π°)
object, and they already disagree at π₁, index 3 (index 0
agrees everywhere: both sides 0).

## The K-CLS-B resolution table (the brick's second deliverable, landed as registered)

| member | shapeBCoord | sectorPoly(E_π) |
|---|---|---|
| pi1 | ![0,0,0,4i] | ![0,0,0,0] |
| piFlip | ![0,0,2i,6i] | ![0,−2,−4,−40] |
| piEFlip | ![0,0,−2i,2i] | ![0,6,12,1080] |
| orbitRep b (all 16) | ![0,0,0,4i] | ![0,0,0,0] |

The coordinate invariant's true resolution on the realized
family: **three classes** — {pi1 + all sixteen orbit
points}, {piFlip}, {piEFlip}. That is strictly coarser than
the pin's "at best up to swap orbits": the whole orbit blob,
π₁ included, is ONE class. `shapeBCoord` survives as a
defined instrument with a proved resolution table; the
identification conjecture is dead and stays dead under the
relabeling rule (a repaired identification would be a NEW
entry).

**Lane 1 state:** Grade T is closed except the piAnti
base-status cell (named open since CLS-3c); Grade W stands
as posed (CLS-1 PARTIAL at ExtractionLemma; BR1-029 probe
in flight on the conjugation route); the Shape B lane is
COMPLETE at verdict — pin landed, identification refuted,
resolution table proved.

## Fences

NO CLAIM; Dial 1 = 0; all dials 0/4. Nothing here touches
the base, the family, or any landed exclusion.

**Census after landing: 12,424 strict / 12,845 total / 429 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
