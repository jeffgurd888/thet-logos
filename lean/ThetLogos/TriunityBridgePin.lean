import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin
import ThetLogos.EntropyArrowPin
import ThetLogos.GeometryForcesPin
import ThetLogos.ThreeRoutesPin
import ThetLogos.TriunityCapstonePin

/-!
# ThetLogos.TriunityBridgePin — the Triunity Triple Capstone, Brick 2: THE THREE WAYS (T5 charter; NO CLAIM)

Working file name only — the OBJECT is named by Zero:
the **Triunity Triple Capstone Crystal matrix**.
Commissioned by Zero tonight (2026-11-28, 00:08–00:09
EST), in three fragments, filed verbatim:

1. "build all three bricks the the Triunity Triple
   Capstone Crystal matrix"
2. "as the peral" [pearl]
3. "it a 3 way bridge highway"

This is Brick 2 of the three: THE THREE WAYS — the
bridge. Brick 1 (the assembly,
`ThetLogos.TriunityCapstonePin`) is banked beneath this
module; Brick 3 (the capstone proposition) follows as
its own brick.

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

## The three ways across the one matrix

Zero's third fragment names this brick: the matrix is
"a 3 way bridge highway." The three ways are the routes
line's three routes, restated here as crossings OF THE
ONE ASSEMBLED MATRIX, between the same endpoints:

- the near endpoint is the matrix's own **grain** — the
  thermally separated configuration the pearl is grown
  around (Brick 1's registration);
- the far endpoint is a configuration **balanced and
  standing in the matrix's own geometry** — the
  condensed/balanced end of the diagram
  (`capstoneEnd` below: `cycleBalanced`, and membership
  in the locus of the geometry the matrix CARRIES —
  which by Brick 1's coherence field is the seat's own
  `geomOf` locus);
- the three crossings are the collapse route
  (`routeStanding`), the step route (`routeStep` —
  tunneling proper is its channel against standing,
  `geomTunnelJoined`, referenced from the parents,
  never redefined), and the jump route (`routeJump`).

`capstoneBridge` states that one far endpoint is
reached by all three crossings from the grain — the
highway lands all three ways on the same shore. It is
stated UNPROVED: no crossing is exhibited at this
brick, and K-ROUTE-COLLAPSE / K-CAPSTONE-EMPTY are armed
against the shore and the traffic respectively.

## routeOrder on the assembled object, and the one construction

`capstoneRouteOrder` restates the routes line's
`routeOrder` on the assembled matrix — a restatement,
labeled as such, unproved as a whole.

ONE inclusion is discharged at this brick, and it is
discharged as a CONSTRUCTION, not a theorem —
`capstoneStandingStep` below. The standing route's
trajectory is an `ArrowPath` whose steps are
condensations; `ArrowPath` does not distinguish step
kinds, and condensation is a disjunct of `arrowStep` —
so the very same path is a dynamical path, and the
transport from standing reachability to step
reachability is the identity on paths. That is true by
the banked constructions, it is registered as a `def`,
it is claimed as NO theorem, and it is counted as
0 strict — the no-costume rule (K-CAPSTONE-COSTUME)
applied to ourselves. The second inclusion of
routeOrder (step ⊆ jump) has no such construction:
nothing in the jump seat's data promises it, it remains
a claim inside `capstoneRouteOrder`, and it can fail.

## Kills (armed on the capstone's face from Brick 1; carried here unsoftened)

- **K-CAPSTONE-SPLIT**: the three faces are provably
  independent — no bridge exists; the triunity dies.
  (This brick's bridge is one of the places a split
  would show: three crossings that provably never share
  a shore.)
- **K-CAPSTONE-COSTUME**: the assembly is mere bundling
  and the "triunity" a relabeling — Composition Rule
  L15.
- **K-CAPSTONE-EMPTY**: the assembled object has no
  instance on the smallest seat — a pearl with no
  grain.
- The parents' kills ride along, unsoftened:
  K-ROUTE-COLLAPSE, K-ROUTE-FREE, K-ROUTE-THERMAL,
  K-ROUTE-COSTUME (routes); K-ARROW and family (arrow);
  K-FORCE-GEOM, K-SNAP-ORDER, K-CYCLE-OPEN (cycle);
  K-GEOM-ENTROPY, K-GEOM-TUNNEL, K-GEOM-COSTUME
  (geometry); K-JUMP-MEMORY (jump seat).

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.

## Brick 2's charge

The bridge propositions, stated unproved, plus the one
construction, labeled as construction. Names frozen at
this brick: `capstoneEnd`, `capstoneCrossStanding`,
`capstoneCrossStep`, `capstoneCrossJump`,
`capstoneBridge`, `capstoneRouteOrder`,
`capstoneStandingStep`.
-/

namespace ThetLogos

/-- **The far endpoint of the bridge: condensed and
balanced.** A configuration `q` is a far endpoint of
the matrix `M` when it is **balanced** on the matrix's
seat (`cycleBalanced` — normalised, zero net charge,
maximal entropy over the normalised zero-charge class)
and it **stands in the matrix's own geometry**: `q`
lies in the locus of the geometry the matrix carries
(`M.geometry.locus` — by Brick 1's coherence field,
the seat's own `geomOf` locus, the condensation /
identity-face locus). This is the condensed shore all
three ways of the highway land on. A predicate, not an
exhibit: whether any far endpoint exists for a given
matrix is a later brick's question, and
K-CAPSTONE-EMPTY's neighbourhood. -/
def capstoneEnd (M : CrystalMatrix) (q : Fin 3 → ℝ) : Prop :=
  cycleBalanced M.pearl.cycle q ∧ q ∈ M.geometry.locus

/-- **The first way across: the collapse crossing.**
From the matrix's grain to `q` by the standing route
(`routeStanding` — standing-only histories, every step
a condensation). The classical way of the diagram:
continuous, standing, paying the full cost. -/
def capstoneCrossStanding (M : CrystalMatrix)
    (q : Fin 3 → ℝ) : Prop :=
  routeStanding M.pearl M.grain q

/-- **The second way across: the step crossing.** From
the matrix's grain to `q` by the step route
(`routeStep` — reachability by the seat's own derived
dynamics, ring motion ∨ condensation). Tunneling
proper is this route's channel against the first
(`geomTunnelJoined` on the parents' face): where the
step way crosses and the standing way cannot. -/
def capstoneCrossStep (M : CrystalMatrix)
    (q : Fin 3 → ℝ) : Prop :=
  routeStep M.pearl M.grain q

/-- **The third way across: the jump crossing.** From
the matrix's grain to `q` by the jump route
(`routeJump` — finite trajectories of the seat's
one-jump relation, the Gibbs Jump seat's owed field as
registered by the routes line). The diagram's purple
line: no dynamical path, only jumps. -/
def capstoneCrossJump (M : CrystalMatrix)
    (q : Fin 3 → ℝ) : Prop :=
  routeJump M.pearl M.grain q

/-- **THE BRIDGE, pinned as this brick's target — the
3 way bridge highway.** One far endpoint of the matrix
is reached from the matrix's grain by ALL THREE ways:
there is a balanced, standing configuration `q` with a
collapse crossing, a step crossing, and a jump crossing
from the grain to `q` — the three ways are three
crossings of the one matrix, between the same
endpoints, landing on the same shore. Stated in
statement form only; nothing about it is claimed in
this brick: no crossing is exhibited, and the kills on
this module's face are armed against exactly its
failure modes. Brick 3 carries it into the capstone
proposition; later bricks take the exhibits — or the
kills. -/
def capstoneBridge (M : CrystalMatrix) : Prop :=
  ∃ q : Fin 3 → ℝ, capstoneEnd M q ∧
    capstoneCrossStanding M q ∧ capstoneCrossStep M q ∧
      capstoneCrossJump M q

/-- **ROUTE ORDER, restated on the assembled object.**
The routes line's `routeOrder` of the matrix's pearl:
standing reachability ⊆ step reachability ⊆ jump
reachability, on this one matrix's seat. A restatement,
labeled as such — the statement is the parents', the
seat is the assembled object's. Unproved as a whole:
its first inclusion is discharged by construction
below (`capstoneStandingStep`); its second inclusion
(step ⊆ jump) is a claim about the jump seat's relation
that nothing yet promises, and it can fail —
K-ROUTE-COLLAPSE is its firing form on the smallest
seat. -/
def capstoneRouteOrder (M : CrystalMatrix) : Prop :=
  routeOrder M.pearl

/-- **CONSTRUCTION — not a theorem: the standing way is
a step way, at path level.** Given a standing crossing
of the matrix (a standing-only history from `p` to
`q`), the SAME trajectory is a dynamical path: an
`ArrowPath` does not distinguish step kinds, and each
of the standing path's steps is a condensation, which
is a disjunct of `arrowStep` — so the standing path
itself, unmodified, witnesses step reachability. The
transport is the identity on paths, true by the banked
constructions; it is registered as a `def`, claimed as
no theorem, and counted as 0 strict (see the module
face: the no-costume rule applied to ourselves). It
discharges the first inclusion of `capstoneRouteOrder`
at the level of paths; the proposition as stated there
remains unproved as a whole at this brick, its second
inclusion untouched by this construction. (The `defProp`
linter flags this def — "a proposition; use `theorem`
instead" — and the flag is noted, not silenced: the
`def` is the deliberate form, per the construction
labeling above.) -/
def capstoneStandingStep (M : CrystalMatrix)
    {p q : Fin 3 → ℝ} (h : routeStanding M.pearl p q) :
    routeStep M.pearl p q := by
  obtain ⟨path, -⟩ := h
  exact ⟨path⟩

end ThetLogos
