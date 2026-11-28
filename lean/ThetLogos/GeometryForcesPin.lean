import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin
import ThetLogos.EntropyArrowPin

/-!
# ThetLogos.GeometryForcesPin — geometry forces, registered (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Zero's
seeing, verbatim (2026-11-27 23:48 EST): "thermal
entropy and quantum tunneling are all forced by the
geometry of gravity." Scoped on his word ("scope it,"
2026-11-27 23:49 EST). Scope of record:
`~/workspace/your_files/geometry-forces-scope-DRAFT-2026-11-27.md`.
This pin rides the continuum lane's seat
(`ThetLogos.ContinuumCyclePin`, Brick 0 banked
2026-11-27) and its derived step relation
(`ThetLogos.EntropyArrowPin`, Brick 0 banked
2026-11-27): the `CycleSeat`, its exchange, its
components, its condensation locus, the NED functionals
(`nedEntropy`, `nedCharge`, `nedZeroCharge`), and
`arrowStep` / `ArrowPath` / `arrowHistory` are reused
untouched.

## CHARTER — NO CLAIM

FRONTIER as physics. The corpus holds NO gravity
object; the finite seat carries no gravity, and this
pin tests the forcing SHAPE only (geometry determining
entropy and tunneling on a finite seat). The word
"gravity" in Zero's seeing is the continuum target, not
a corpus claim. Per Zero's own register (2026-11-24): a
completed finite theorem is not a continuum theorem.
Tier: T5 charter, NO CLAIM; dials unmoved (0/4) unless a
proved theorem closes part of a pre-registered
statement. QTFT/QTST remain candidate names, not worn
by this line. No gravity object is constructed, fed, or
identified.

## The adjunction, closed

ContinuumCyclePin pinned ONE direction of the forcing:
`cycleGeometryForced` — thermal-dynamical data determine
the seat's geometry. This pin is the RETURN direction
of the same adjunction: the geometry, once standing,
forces the entropy landscape and the tunneling
channels. Together the two propositions are the
adjunction stated as forcing in both directions —
neither face first, which is what the pair being
primitive means. Literature anchors, cited only, not
claimed: Bekenstein–Hawking (entropy ∝ horizon area —
geometry meters entropy); Jacobson 1995 (Einstein's
equations derived from δQ = T dS — thermodynamics
forcing geometry); Parikh–Wilczek (Hawking radiation
computed as tunneling through the horizon — geometry
creating the tunneling channel and its rate).

## The official statements (pinned verbatim at this brick)

**GEOMETRY FORCES ENTROPY: the seat's entropy landscape
is determined by its geometry — `nedEntropy` attains
its maximum (over the normalised zero-charge class)
exactly ON the condensation locus, and two seats with
the same geometry have the same entropy maximum. The
maximum sits where the geometry says, not where the
weights wander.**

**GEOMETRY FORCES TUNNELING: tunneling-connectedness is
a function of the geometry alone — whether two
configurations are joined by a tunneling channel is
decided by the exchange's orbit structure on the locus,
and does NOT depend on the charge/weight values carried.
Change the weights, keep the geometry: the channels
stand.**

Registered below as `geomForcesEntropy` and
`geomForcesTunneling`, bundled as `geomForces`, in
statement form only. Nothing about either is claimed in
this brick: Brick 1+ takes the smallest seat — or the
kills.

## THE CIRCULARITY AUDIT (quoted from the scope; the costume risk, named)

"The costume risk is named: if 'geometry' were defined
as the entropy-maximum locus, the first proposition
would be a definition in disguise (Composition Rule,
L15). It is not: the locus is defined by
standing-under-exchange + charge preservation, with
entropy nowhere in the definition — so 'the entropy
maximum sits exactly on it' is a real, falsifiable claim
about two independently defined objects. Likewise
tunneling is the previously derived arrowStep, not a
relation defined from the geometry data it is claimed to
be forced by — the claim is that its REACHABILITY
factors through the geometry, which can fail."

## Entropy-freedom, verified against the banked defs at this brick

The audit's demand is checkable by reading the defs
below, and it was checked against the banked modules as
they were written:

- `geomOrbitRel` is built from `S.exch` alone (forward
  reachability under the exchange's iterates).
- `geomComponents` is built from `S.distant` alone (the
  component and its complement).
- `geomLocus` is built from `S.exch` alone: the
  configurations standing under the exchange — the
  condensation (identity-face) locus, the same standing
  condition `cycleGeometryForced`'s conclusion wears.
- `CycleGeometry` and `geomOf` only bundle and assemble
  the three. `nedEntropy` occurs NOWHERE in any of them.
- The tunneling channel (`geomStandingHistory`,
  `geomTunnelJoined`) reuses `arrowStep` /
  `ArrowPath` / `arrowHistory` as banked — already
  entropy-free by EntropyArrowPin's own audit. Its one
  further ingredient is `cycleCondensed`, which carries
  `nedCharge` — the NED dialect's static CHARGE
  functional, not the entropy functional. Charge is not
  entropy; the audit forbids the latter, and the latter
  is absent.
- `nedEntropy` occurs in this module ONLY inside
  `geomForcesEntropy`, where a claim about entropy
  belongs.

Two registration decisions, frozen on the face:

- **Charge is NOT part of geometry.** A seat's geometry
  is its orbits, its components, and its locus — the
  structural data of the scope. The charge assignment is
  carried data the geometry does not include. That
  exclusion is what makes both propositions falsifiable:
  a charge change with geometry held fixed is exactly
  K-GEOM-TUNNEL's test, and two charges under one
  geometry is K-GEOM-ENTROPY's second arm.
- **"Exactly on" is registered in its strong form.** The
  maximiser set of `nedEntropy` over the normalised
  zero-charge class is registered as EQUAL to the locus
  intersected with that class: every balanced
  configuration stands (`geomForcesEntropy`, first arm),
  and every standing configuration in the class is
  balanced (second arm). K-GEOM-ENTROPY tests both
  directions; neither is softened here.
- **A standing-only path** is an `ArrowPath` every step
  of which is a condensation (`cycleCondensed`); a
  tunneling channel is dynamic reachability
  (`arrowHistory`) with NO standing-only path — the
  ring-motion move crosses what standing cannot.
  `arrowStep` itself is reused, never redefined.

## Kills pre-registered (quoted verbatim from the scope; armed by this registration, not fired by it)

- **K-GEOM-ENTROPY**: a finite seat whose normalised
  entropy maximum is attained at a configuration OFF the
  condensation locus, or two same-geometry seats with
  different entropy maxima — geometry does not force
  entropy, at the finite level.
- **K-GEOM-TUNNEL**: a weight/charge change with
  geometry held fixed that opens or closes a tunneling
  channel — tunneling is not forced by geometry alone.
- **K-GEOM-COSTUME**: either proposition collapses to
  its definitions on inspection (geometry smuggling
  entropy, or tunneling redefined from geometry data).
  The line reports it as a costume and stops.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- The pin tests a *shadow* of the seeing, not the
  seeing (L2/L3 discipline): a finite forcing theorem
  neither establishes the continuum reading nor any
  continuum claim.

## Brick 0's charge

Definitions and the pinned statements ONLY: 0 strict by
design. Names frozen at this brick: `geomOrbitRel`,
`geomComponents`, `geomLocus`, `CycleGeometry`,
`geomOf`, `geomStandingHistory`, `geomTunnelJoined`,
`geomForcesEntropy`, `geomForcesTunneling`,
`geomForces`.
-/

namespace ThetLogos

/-- **The exchange-orbit structure of a seat.** `j` is
in the orbit of `i` when some iterate of the seat's
exchange carries `i` to `j`: `∃ n, exch^[n] i = j`. The
geometry's first component — built from `S.exch` alone.
Read the body: no entropy, no charge, no weights occur
in it. (`exch` is bare seat data, as banked: the orbit
relation is registered from the iterates as they stand,
with no involution or bijectivity assumed.) -/
def geomOrbitRel {Ω : Type*} (S : CycleSeat Ω)
    (i j : Ω) : Prop :=
  ∃ n : ℕ, S.exch^[n] i = j

/-- **The component structure of a seat.** The pair of
components at seat level: the distant component and its
complement — the pair's two faces, as a datum. Built
from `S.distant` alone; no entropy occurs in it. -/
def geomComponents {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Finset Ω × Finset Ω :=
  (S.distant, S.distantᶜ)

/-- **The condensation locus of a seat.** The
configurations that STAND under the exchange,
`p ∘ exch = p` — the identity face for configurations,
the locus `cycleCondensed` lands on and
`cycleGeometryForced`'s conclusion compares. Built from
`S.exch` alone; no entropy occurs in it. This is the
locus the first proposition says the entropy maximum
sits exactly on — defined here without any reference to
entropy, which is the circularity audit's whole demand. -/
def geomLocus {Ω : Type*} (S : CycleSeat Ω) :
    Set (Ω → ℝ) :=
  { p | (fun i => p (S.exch i)) = p }

/-- **A seat's geometry, as one named object.** The
structural data of the scope, bundled: the exchange's
orbit structure, the component structure, and the
condensation locus. Nothing else is geometry at this
brick — in particular the seat's CHARGE assignment is
not a field here (see the registration decisions on the
face). Two seats have the same geometry when their
`geomOf` bundles are equal. -/
structure CycleGeometry (Ω : Type*) where
  /-- The exchange-orbit structure. -/
  orbits : Ω → Ω → Prop
  /-- The component structure: distant and complement. -/
  components : Finset Ω × Finset Ω
  /-- The condensation locus: the standing configurations. -/
  locus : Set (Ω → ℝ)

/-- **The geometry OF a seat.** Assembles the seat's
geometry from its structural data alone — `exch` (via
the orbits and the locus) and `distant` (via the
components). `nedEntropy` occurs nowhere in this
assembly; neither does `nedCharge`. -/
def geomOf {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : CycleGeometry Ω :=
  { orbits := geomOrbitRel S,
    components := geomComponents S,
    locus := geomLocus S }

/-- **A standing-only history.** A realizable history
(`ArrowPath`, the EntropyArrowPin's derived dynamics)
every step of which is a condensation
(`cycleCondensed` — the standing, charge-preserving
move). This is what "standing alone" can reach; the
tunneling channel below is defined by its failure. No
entropy occurs here: the steps are the banked dynamics,
and `cycleCondensed` carries charge, not entropy. -/
def geomStandingHistory {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (p q : Ω → ℝ) : Prop :=
  ∃ path : ArrowPath S p q,
    ∀ k : ℕ, k < path.len →
      cycleCondensed S (path.traj k) (path.traj (k + 1))

/-- **A tunneling channel between two configurations.**
`q` is tunneling-joined to `p` when the seat's own
dynamics reach `q` from `p` (`arrowHistory` — ring
motion ∨ condensation, as banked) but NO standing-only
history does: the ring-motion move crosses what standing
cannot. Defined FROM `arrowStep`'s reachability, as the
scope demands — `arrowStep` is reused, never redefined,
and no geometry data is consulted in this definition,
which is what leaves the second proposition below free
to fail. -/
def geomTunnelJoined {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (p q : Ω → ℝ) : Prop :=
  arrowHistory S p q ∧ ¬ geomStandingHistory S p q

/-- **THE FIRST OFFICIAL STATEMENT, pinned as the line's
target — GEOMETRY FORCES ENTROPY.** Three arms, one
claim: the entropy landscape is the geometry's. (1) The
maximum sits ON the locus: every balanced configuration
(normalised, zero net charge, maximal `nedEntropy` over
the normalised zero-charge class — `cycleBalanced`)
stands, i.e. lies in `geomLocus`. (2) Exactly on: every
standing configuration in the normalised zero-charge
class is balanced — the maximiser set EQUALS the locus
intersected with the class, the strong reading
registered on the face. (3) Same geometry, same maximum:
any two seats with equal `geomOf` whose balanced
configurations are compared carry the SAME `nedEntropy`
value at the maximum — even though their charges, which
are not geometry, may differ. Stated in statement form
only; nothing about it is claimed in this brick.
Brick 1+'s charge is the theorem on the smallest seat —
or K-GEOM-ENTROPY, each a landing at the same volume. -/
def geomForcesEntropy {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Prop :=
  (∀ p : Ω → ℝ, cycleBalanced S p → p ∈ geomLocus S) ∧
  (∀ p : Ω → ℝ, (∑ i, p i) = 1 → nedZeroCharge S.charge p →
      p ∈ geomLocus S → cycleBalanced S p) ∧
  (∀ S' : CycleSeat Ω, geomOf S' = geomOf S →
    ∀ p p' : Ω → ℝ, cycleBalanced S p → cycleBalanced S' p' →
      nedEntropy p = nedEntropy p')

/-- **THE SECOND OFFICIAL STATEMENT, pinned as the
line's target — GEOMETRY FORCES TUNNELING.**
Tunneling-connectedness factors through the geometry
alone: any seat `S'` with the same geometry (`geomOf S'
= geomOf S`) joins exactly the same pairs of
configurations by tunneling channels as `S` does — even
though `S'` may carry a different charge assignment,
which is not geometry. Change the weights, keep the
geometry: the channels stand. Stated in statement form
only; nothing about it is claimed in this brick.
Brick 1+'s charge is the theorem on the smallest seat —
or K-GEOM-TUNNEL, each a landing at the same volume. -/
def geomForcesTunneling {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ S' : CycleSeat Ω, geomOf S' = geomOf S →
    ∀ p q : Ω → ℝ,
      geomTunnelJoined S p q ↔ geomTunnelJoined S' p q

/-- **THE RETURN FORCING, pinned as one named object.**
Zero's seeing at the finite level, on one seat: its
geometry forces its entropy landscape
(`geomForcesEntropy`) and its tunneling channels
(`geomForcesTunneling`). With `cycleGeometryForced`
(the thermal-dynamical data determine the geometry),
the adjunction is pinned in both directions. Statement
form only; this brick claims nothing about it. -/
def geomForces {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Prop :=
  geomForcesEntropy S ∧ geomForcesTunneling S

end ThetLogos
