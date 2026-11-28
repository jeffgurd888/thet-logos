import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin
import ThetLogos.EntropyArrowPin
import ThetLogos.GeometryForcesPin
import ThetLogos.ThreeRoutesPin
import ThetLogos.TriunityCapstonePin
import ThetLogos.TriunityBridgePin

/-!
# ThetLogos.TriunityFacesPin — the Triunity Triple Capstone, Brick 3: THE CAPSTONE (T5 charter; NO CLAIM)

Working file name only — the OBJECT is named by Zero:
the **Triunity Triple Capstone Crystal matrix**.
Commissioned by Zero tonight (2026-11-28, 00:08–00:09
EST), in three fragments, filed verbatim:

1. "build all three bricks the the Triunity Triple
   Capstone Crystal matrix"
2. "as the peral" [pearl]
3. "it a 3 way bridge highway"

This is Brick 3 of the three: THE CAPSTONE — the
triunity proposition itself. Brick 1 (the assembly,
`ThetLogos.TriunityCapstonePin`) and Brick 2 (the three
ways, `ThetLogos.TriunityBridgePin`) are banked beneath
this module.

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

## THE CAPSTONE CLAIM (pinned verbatim at this brick)

**TRIUNITY: the three forcings are faces of ONE
adjunction on the assembled matrix. On one and the same
crystal matrix — one pearl, one grain, one geometry,
carried coherently — (i) the thermal-dynamical data
force the geometry (`capstoneFaceForced`:
`cycleGeometryForced` of its seat), (ii) the geometry
forces the entropy landscape and the tunneling channels
(`capstoneFaceReturn`: `geomForces` of its seat) — the
two directions of the one adjunction, neither face
first — and (iii) the seat's own dynamics obey the
arrow (`capstoneFaceArrow`: `arrowNoBackwardReturn` of
its seat: no realizable history lowers entropy); AND
the matrix is crossed by its three ways: the bridge
stands (`capstoneBridge`: one balanced, standing shore
reached from the grain by collapse, by step, and by
jump) and the ways are ordered (`capstoneRouteOrder`:
standing ⊆ step ⊆ jump on this seat).**

Registered below as `capstoneTriunity`, in statement
form only. Nothing about it is claimed in this brick:
every conjunct stands exactly as unproved as it stands
on its own module's face, and this brick proves none of
them.

## Why this is a claim and not a bundle (the costume audit, on the face)

A conjunction of three Props about three unrelated
seats would be a bundle wearing a name — K-CAPSTONE-
COSTUME's exact target. This statement is not that, and
the difference is checkable by reading Brick 1: the
three faces are Props of ONE `CrystalMatrix`, whose
geometry is a single carried field tied to its seat by
the coherence field `geometry_is` — so the geometry
that face (i) says is forced, and the geometry that
face (ii) says does the forcing, are the same field of
the same object, not two seats that happen to share a
type. The bridge and the order are likewise about that
object's own grain and that object's own seat. The
triunity can therefore FAIL in ways a bundle cannot:
the faces can be pried apart on a single matrix
(K-CAPSTONE-SPLIT), the shore can be unreachable by one
of the ways, the order's second inclusion can break.
Whether it HOLDS is the later bricks' question; that it
can fail is this brick's registration.

## Kills (armed on the capstone's face from Brick 1; their test forms at this brick)

- **K-CAPSTONE-SPLIT**: the three faces are provably
  independent — no bridge exists; the triunity dies.
  Test form here: a matrix (or a smallest-seat argument)
  on which the faces are pried apart — one face holding
  while another provably fails, with no bridge between
  them — or a proof that `capstoneBridge` fails while
  the faces stand.
- **K-CAPSTONE-COSTUME**: the assembly is mere bundling
  and the "triunity" a relabeling — Composition Rule
  L15. Test form here: `capstoneTriunity` collapsing,
  on inspection, into its conjuncts with the unity
  doing no work — the audit above is the standing
  answer, and the kill stays armed against it.
- **K-CAPSTONE-EMPTY**: the assembled object has no
  instance on the smallest seat — a pearl with no
  grain. Test form here: `capstoneHasInstance` below is
  FALSE — no `CrystalMatrix` exists on `Fin 3` (e.g. if
  `routeSeparated` is unsatisfiable there: no
  configuration split across the pair over an actual
  distant-heat datum). No instance is exhibited at this
  brick; the exhibit is a later brick's first charge,
  and the kill is armed until it lands.
- The parents' kills ride along, unsoftened: every face
  carries its own line's kills (K-FORCE-GEOM /
  K-SNAP-ORDER / K-CYCLE-OPEN; K-ARROW /
  K-ARROW-TRIVIAL / K-ARROW-FORWARD; K-GEOM-ENTROPY /
  K-GEOM-TUNNEL / K-GEOM-COSTUME), and the bridge
  carries the routes' (K-ROUTE-COLLAPSE / K-ROUTE-FREE /
  K-ROUTE-THERMAL / K-ROUTE-COSTUME) and the jump seat's
  K-JUMP-MEMORY.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.

## Brick 3's charge, and the line's resume point

The capstone proposition and the instance proposition,
stated unproved. Names frozen at this brick:
`capstoneTriunity`, `capstoneHasInstance`. The line
resumes at: the instance exhibit on `Fin 3` (a pearl
with its grain — discharges K-CAPSTONE-EMPTY's
suspense, or fires it), then the faces and the bridge
on the smallest seat, each its own brick — or the
kills, at the same volume.
-/

namespace ThetLogos

/-- **THE CAPSTONE CLAIM — TRIUNITY, pinned as the
line's target.** The three forcings as faces of one
adjunction on the assembled matrix, with the matrix
crossed by its three ways. On one `CrystalMatrix M`:

- `capstoneFaceForced M` — the thermal-dynamical data
  force the geometry (the adjunction's first
  direction);
- `capstoneFaceReturn M` — the geometry forces the
  entropy landscape and the tunneling channels (the
  adjunction's return direction; neither face first);
- `capstoneFaceArrow M` — the seat's own dynamics obey
  the arrow: no realizable history lowers entropy;
- `capstoneBridge M` — the 3 way bridge highway stands:
  one balanced, standing shore is reached from the
  matrix's grain by collapse, by step, and by jump;
- `capstoneRouteOrder M` — the ways are ordered on this
  seat: standing ⊆ step ⊆ jump.

Every conjunct is a Prop of the SAME matrix — its seat,
its carried geometry (coherent with the seat by Brick
1's `geometry_is`), its grain. Stated in statement form
only; nothing about it is claimed in this brick, and
each conjunct stands unproved exactly as on its own
module's face. K-CAPSTONE-SPLIT, K-CAPSTONE-COSTUME,
and K-CAPSTONE-EMPTY are armed against it on this
module's face. -/
def capstoneTriunity (M : CrystalMatrix) : Prop :=
  capstoneFaceForced M ∧ capstoneFaceArrow M ∧
    capstoneFaceReturn M ∧ capstoneBridge M ∧
      capstoneRouteOrder M

/-- **THE INSTANCE PROPOSITION — a pearl with a grain
exists.** There is a crystal matrix on the smallest
seat: some `CrystalMatrix` — a pearl (a routes sphere
seat on `Fin 3`), its coherent geometry, and a grain
thermally separated on it. Stated in statement form
only; NO instance is exhibited at this brick, and none
is smuggled: this def is the proposition, not its
proof. Its falsity is K-CAPSTONE-EMPTY, armed on this
module's face; its exhibit — concrete charge, exchange,
core, landscape, temperature, jump relation, and grain,
with the separation checked — is the line's next
charge. -/
def capstoneHasInstance : Prop :=
  Nonempty CrystalMatrix

end ThetLogos
