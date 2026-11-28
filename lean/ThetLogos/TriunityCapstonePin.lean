import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin
import ThetLogos.EntropyArrowPin
import ThetLogos.GeometryForcesPin
import ThetLogos.ThreeRoutesPin

/-!
# ThetLogos.TriunityCapstonePin — the Triunity Triple Capstone, Brick 1: ASSEMBLY (T5 charter; NO CLAIM)

Working file name only — the OBJECT is named by Zero, in
his own words, and the module carries his name for it:
the **Triunity Triple Capstone Crystal matrix**.
Commissioned by Zero tonight (2026-11-28, 00:08–00:09
EST), in three fragments, filed verbatim:

1. "build all three bricks the the Triunity Triple
   Capstone Crystal matrix"
2. "as the peral" [pearl]
3. "it a 3 way bridge highway"

This is Brick 1 of the three: the ASSEMBLY. Brick 2
(the three ways — the bridge) and Brick 3 (the capstone
proposition) are separate modules, banked after this
one, each its own brick.

## Parents — all banked, reused untouched

The capstone assembles tonight's three continuum lines
on the continuum lane's seats, all banked in this tree:
the cycle seat and its forcings
(`ThetLogos.ContinuumCyclePin`, tip `0015a2b`), the
derived arrow dynamics (`ThetLogos.EntropyArrowPin`,
tip `534aeb7`), the geometry and its return forcing
(`ThetLogos.GeometryForcesPin`, tip `4b8c9f5`), and the
three routes on the 0g sphere seat
(`ThetLogos.ThreeRoutesPin`, tip `2e4da15`, itself
riding the transplanted Gibbs Jump seat). Nothing in
the parents is redefined here; the assembly only
bundles, names, and registers.

## CHARTER — NO CLAIM

This line is aimed at the continuum reading (its
direction and target), and graded at the finite level
only. Per Zero's own register (2026-11-24): a completed
finite theorem is not a continuum theorem. Tier: T5
charter, NO CLAIM; dials unmoved (0/4) unless a proved
theorem closes part of a pre-registered statement.
QTFT/QTST remain candidate names, not worn by this
line. No gravity object is constructed, fed, or
identified.

## What the assembly is (registered, not claimed)

The **crystal matrix** is ONE bundled datum: a pearl
(the routes line's 0g sphere seat — a cycle seat on the
`Fin 3` ring with a core component, the shell its
complement, a Gibbs landscape and temperature, and the
one-jump relation) grown around its **grain** (a
configuration thermally separated on that seat — the
pearl's layers are the core, the shell, and the grain
at their centre), together with the seat's **geometry**
carried as a field and tied to the seat by a coherence
field: the matrix's geometry IS `geomOf` of its seat,
by registration — the assembly does not invent a second
geometry that might disagree with the seat's own.

The matrix's **three faces** are tonight's three
forcings, registered below as named Props of the one
matrix: the geometry forced by the thermal-dynamical
data (`cycleGeometryForced`), the arrow on the derived
dynamics (`arrowNoBackwardReturn`), and the return
forcing (`geomForces` — geometry forces entropy and
tunneling). Registering a face is not claiming it: all
three are stated here as the matrix's faces, unproved,
and Brick 3 states the triunity of the three as the
capstone claim.

## Kills pre-registered (on the capstone's face from this brick; armed by this registration, not fired by it)

- **K-CAPSTONE-SPLIT**: the three faces are provably
  independent — no bridge exists; the triunity dies.
- **K-CAPSTONE-COSTUME**: the assembly is mere bundling
  and the "triunity" a relabeling — Composition Rule
  L15. (Armed against this brick itself: if the bundle
  is all there is, the kill fires on the capstone, and
  the later bricks' bridge and triunity statements are
  where it is tested — they must say something the
  bundle alone does not.)
- **K-CAPSTONE-EMPTY**: the assembled object has no
  instance on the smallest seat — a pearl with no
  grain. (The grain field demands a thermally separated
  configuration on the seat; whether one exists on
  `Fin 3` is an exhibit question for a later brick, not
  assumed here.)

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- The pin assembles *shadows* of the seeings, not the
  seeings (L2/L3 discipline): a finite assembly neither
  establishes the continuum reading nor any continuum
  claim.

## Brick 1's charge

Definitions and registrations ONLY: 0 strict by design.
Names frozen at this brick: `CrystalMatrix`,
`capstoneSeat`, `capstoneCore`, `capstoneShell`,
`capstoneLayers`, `capstoneFaceForced`,
`capstoneFaceArrow`, `capstoneFaceReturn`.
-/

namespace ThetLogos

/-- **The crystal matrix: the Triunity Triple Capstone,
assembled.** One bundled datum carrying the whole
object:

- `pearl` — the 0g sphere seat of the routes line
  (`RouteSphereSeat`): a cycle seat on the `Fin 3` ring,
  a core component (the shell is its complement), the
  Gibbs landscape and inverse temperature, and the
  one-jump relation. The seat, its arrow dynamics, and
  its three routes all live on this field.
- `geometry` — the seat's geometry, carried as data,
  and `geometry_is` — the coherence field tying it to
  the seat: the matrix's geometry IS `geomOf` of its
  seat, by registration. The assembly invents no second
  geometry.
- `grain` — the configuration the pearl is grown
  around, and `grain_separated` — its registration: the
  grain is thermally separated on the seat
  (`routeSeparated`: the heat held at the shell, the
  charge split across the pair, an actual distant-heat
  datum carried). A matrix with no separated grain is
  not a matrix at all — that demand is
  K-CAPSTONE-EMPTY's hunting ground, and no instance is
  exhibited at this brick.

The pearl's layers are registered by `capstoneCore`,
`capstoneShell`, and `capstoneLayers` below; the grain
sits at their centre by this structure's own shape. -/
structure CrystalMatrix where
  /-- The pearl: the 0g sphere seat (routes line). -/
  pearl : RouteSphereSeat
  /-- The matrix's geometry, carried as data. -/
  geometry : CycleGeometry (Fin 3)
  /-- Coherence: the carried geometry IS the seat's own
  geometry (`geomOf`), by registration. -/
  geometry_is : geometry = geomOf pearl.cycle
  /-- The grain: the configuration at the pearl's
  centre. -/
  grain : Fin 3 → ℝ
  /-- The grain is thermally separated on the seat. -/
  grain_separated : routeSeparated pearl grain

/-- **The matrix's cycle seat.** The seat the whole
assembly rides: the pearl's underlying cycle seat, with
its charge assignment, its distant component, and its
exchange. Every face and every route of the capstone is
a statement about this seat (through the pearl), and
this def names that fact in the capstone's dialect. -/
def capstoneSeat (M : CrystalMatrix) : CycleSeat (Fin 3) :=
  M.pearl.cycle

/-- **The pearl's inner layer: the core.** The sphere
seat's distinguished component — the layer the grain
sits in, with the shell grown around it. -/
def capstoneCore (M : CrystalMatrix) : Finset (Fin 3) :=
  M.pearl.core

/-- **The pearl's outer layer: the shell.** The core's
complement — not a second datum, so the two layers
exhaust the seat by construction, exactly as the routes
line registered them. The shell is where the seat's
heat is held (the separated grain's distant component
IS the shell, by `routeSeparated`'s first clause). -/
def capstoneShell (M : CrystalMatrix) : Finset (Fin 3) :=
  M.pearl.coreᶜ

/-- **The pearl's layers, as one named datum.** Core
and shell, in growth order — the layers the pearl is
grown in around its grain. (The grain itself is the
structure's `grain` field; the layers are the two
components around it.) -/
def capstoneLayers (M : CrystalMatrix) :
    Finset (Fin 3) × Finset (Fin 3) :=
  (capstoneCore M, capstoneShell M)

/-- **FACE ONE of the matrix: geometry forced.** The
seat's geometry is determined by its thermal-dynamical
data — `cycleGeometryForced` of the matrix's seat, the
first direction of the adjunction, registered as this
matrix's face. A face is a registration, not a claim:
nothing about it is proved at this brick, and
K-CAPSTONE-SPLIT is armed against its independence from
the other faces. -/
def capstoneFaceForced (M : CrystalMatrix) : Prop :=
  cycleGeometryForced M.pearl.cycle

/-- **FACE TWO of the matrix: the arrow.** No realizable
history of the seat's own derived dynamics lowers
entropy — `arrowNoBackwardReturn` of the matrix's seat,
the Entropy-Arrow conjecture on this seat, registered
as this matrix's face. Registration, not claim: the
conjecture stands unproved here exactly as it stands on
its own module's face, with K-ARROW armed against it
there. -/
def capstoneFaceArrow (M : CrystalMatrix) : Prop :=
  arrowNoBackwardReturn M.pearl.cycle

/-- **FACE THREE of the matrix: the return forcing.**
The seat's geometry forces its entropy landscape and
its tunneling channels — `geomForces` of the matrix's
seat, the return direction of the adjunction,
registered as this matrix's face. Registration, not
claim: K-GEOM-ENTROPY and K-GEOM-TUNNEL remain armed
against it on its own module's face. -/
def capstoneFaceReturn (M : CrystalMatrix) : Prop :=
  geomForces M.pearl.cycle

end ThetLogos
