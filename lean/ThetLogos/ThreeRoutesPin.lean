import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin
import ThetLogos.EntropyArrowPin
import ThetLogos.GeometryForcesPin
import ThetLogos.GibbsJumpPin

/-!
# ThetLogos.ThreeRoutesPin — the three routes, registered (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Zero's ask,
verbatim (2026-11-28 00:01 EST): "we need to look at
thermal charge separation in a 0g sphere and compare
static charge collapse 4D mapped against quantum
tunneling and jumping into a diagram over time." Scoped
as a comparison pin on his word (2026-11-28 00:06 EST).
Scopes of record:
`~/workspace/your_files/thermal-charge-separation-scope-DRAFT-2026-11-28.md`
(the seeing, the diagram, the physics anchors) and
`~/workspace/your_files/three-routes-comparison-pin-scope-DRAFT-2026-11-28.md`
(this pin's charter, audit, and kills).

## Parents — all banked, reused untouched

This pin rides the continuum lane's seat
(`ThetLogos.ContinuumCyclePin`, tip `0015a2b`): the
`CycleSeat`, its components, `cycleChargeOn`,
`cycleChargeSplit`, `cycleDistantHeat`, and the NED
functionals (`nedEntropy`, `nedCharge`, `nedZeroCharge`)
are reused untouched. The step route reuses
`ThetLogos.EntropyArrowPin`'s derived dynamics
(`arrowStep` / `ArrowPath` / `arrowHistory`, tip
`534aeb7`), and the collapse route and the tunneling
channel reuse `ThetLogos.GeometryForcesPin`'s
`geomStandingHistory` / `geomTunnelJoined` (tip
`4b8c9f5`) — referenced, never redefined.

The fourth parent is the **Gibbs Jump seat**
(`ThetLogos.GibbsJumpPin`, Brick 0 banked 2026-11-27 in
the run-everything queue): located in worktree
`~/workspace/thet-logos-q27` at commit `a7cd161`, and
**transplanted byte-identical into this tree** for this
brick (sha256 `255ada2b…`, verified disk == committed
blob in one command before anything was built on it —
the PairPrimitivePin precedent). The module is the
parent's work, unmodified: a `Fin 3` ring of positions,
a landscape `E`, an inverse temperature `β`, and the
exact forecast law `gibbsForecast` (the row-normalised
Gibbs jump weights). Its own fence, K-JUMP-MEMORY, is
armed on its own face and is untouched by this pin.

## CHARTER — NO CLAIM

T5 comparison pin on the continuum lane's finite seats.
Per Zero's own register (2026-11-24): a completed finite
theorem is not a continuum theorem. Tier: T5 charter,
NO CLAIM; dials unmoved (0/4) unless a proved theorem
closes part of a pre-registered statement. QTFT/QTST
remain candidate names, not worn by this line. No
gravity object is constructed, fed, or identified. The
sphere and the 0g are the seeing's geometry; the seat
carries the comparison's shape only. Physics anchors
from the parent scope, cited only, not claimed: the
Seebeck effect (a temperature gradient drives an
electric potential) and the Soret effect / thermal
diffusion (a temperature gradient drives separation;
microgravity is where it is measured cleanly, because
buoyancy stops masking it).

## The setup — thermal charge separation in a 0g sphere

In gravity, heat stratifies and buoyancy masks the pure
thermal effect. In 0g there is no up or down: a thermal
gradient inside a sphere runs purely radial — hot core,
cold shell, or the reverse — and the gradient itself
drives charge apart along the radius. On the seat, this
is the snap's E stage (`cycleChargeSplit`) driven by
distant heat (`cycleDistantHeat`), registered on a
`Fin 3` ring (the Gibbs seat's own size) with a
distinguished core component; the shell is the core's
complement, and the seat's distant component is
registered AS the shell — the heat is held at the
shell, at a distance from the core.

**0g is registered as an ABSENCE, stated here, not
silent.** The field list of `RouteSphereSeat` below is
the seat's whole directional content: a core, and the
shell as its complement. No ordering field, no
preferred direction, no up or down exists in the
structure — there is nothing in the seat for gravity to
point along. That absence is the 0g registration.

## The official statements (pinned verbatim at this brick)

**ROUTE ORDER: standing reachability ⊆ step
reachability ⊆ jump reachability — each route reaches
at least what the poorer route reaches. The
comparison's spine.**

**JUMP STRICTNESS: some configuration is jump-reachable
but not step-reachable. The diagram's purple line goes
somewhere no path goes.**

**THERMAL ORDERS JUMPS: the jump relation's
availability on the seat depends on the thermal datum —
change the distant-heat profile and the jump-reachable
set changes. (Reachability shadow only: jump STATISTICS
proper need a measure on the seat; that is later-brick
debt, flagged here, not smuggled into this brick.)**

**NO FREE ROUTE: along all three reachabilities, the
total seat's `nedEntropy` (all components counted — the
functional already sums over the whole seat) does not
decrease. Every route pays its bill some way; none pays
nothing.**

Registered below as `routeOrder`, `jumpStrictness`,
`thermalOrdersJumps`, `noFreeRoute`, in statement form
only. Nothing about any of them is claimed in this
brick: Brick 1+ takes the smallest seat — or the kills.

## THE CIRCULARITY AUDIT (quoted from the pin scope; the costume risk, named)

"The costume risk is named: if routeJump were defined
as the complement of step reachability, JUMP STRICTNESS
would be true by definition and the pin would be a
relabeling (Composition Rule, L15). It is not: the jump
relation comes from the Gibbs Jump seat's own banked
data, independently of arrowStep — so strictness is a
real claim about two independently defined relations,
and it can fail. ROUTE ORDER's second inclusion
(step ⊆ jump) is likewise a claim, not a construction:
nothing in the jump seat's data promises it contains
the step relation."

## How routeJump is sourced at this brick (the audit's demand, made visible)

The sourcing is two-level, and both levels are stated
here at full rank:

- **At the position level, the jump reachability is
  DERIVED today, from the jump seat's own banked law.**
  `gibbsJumpReach` below is the positivity of the
  forecast: position `j` is one jump from position `i`
  when `gibbsForecast landscape β i j > 0`. That law is
  the Gibbs seat's own data — Gibbs weights over the
  landscape, row-normalised — assembled with no reference
  to `arrowStep`, to `arrowHistory`, or to their
  complement. Read both defs: the independence the audit
  demands is checkable.
- **At the configuration level — the level the three
  routes are compared at — the one-jump relation is
  registered as an OWED structure field.**
  `RouteSphereSeat.jumpRel` is a field of the seat,
  labeled OWED on its face. Its registered reading: `q`
  is one jump from `p` when the configuration's position
  content moves by one Gibbs jump under the seat's
  landscape and temperature. Deriving that field from
  `gibbsJumpReach` — saying exactly what a
  configuration's position content is, in the cycle
  dialect — is **Brick 1's first job**, registered here
  as owed, never faked at this brick. Nothing in this
  brick assumes any inclusion, strictness, or thermal
  property of the owed field: `routeOrder`'s second
  inclusion and `jumpStrictness` are claims ABOUT it,
  which is exactly why they can fail — and
  K-ROUTE-COSTUME is armed against any later brick that
  discharges the debt by defining the field as step's
  complement after all.

## The thermal headwind, named on the face

Gibbs factors `exp (-β * E j)` are positive at EVERY
`β`, so position-level jump reachability by positivity
(`gibbsJumpReach`) is temperature-blind: the same
positions are reachable at every temperature. The
seeing's thermal content therefore does NOT live in
bare reachability — it lives in the forecast VALUES
(the statistics), which is why the parent scope flags
statistics as later-brick debt rather than letting this
brick pretend otherwise. `thermalOrdersJumps` is
registered in the reachability-shadow form the scope
prescribes — through the distant-heat profile (the
seat's distant component, where the heat is held) — and
K-ROUTE-THERMAL is its exact test: if the derived jump
law's reachability turns out independent of the thermal
datum, the kill fires and the thermal-jump link retreats
to the statistics, where this face already says it
lives.

## Shared ground with the Entropy-Arrow line

`noFreeRoute`'s step arm IS the Entropy-Arrow
conjecture on this seat: `routeStep` is `arrowHistory`,
so "no step history lowers `nedEntropy`" is
`arrowNoBackwardReturn` verbatim. The two lines share
that ground openly: a free route found here is a
backward step found there. Accordingly K-ROUTE-FREE,
if it ever fires, wounds the Entropy-Arrow line too
and is reported jointly — the pin scope registers this,
and this face repeats it unsoftened.

## Kills pre-registered (quoted verbatim from the pin scope; armed by this registration, not fired by it)

- **K-ROUTE-COLLAPSE**: on the smallest seat, the three
  reachabilities coincide — the comparison is empty at
  the finite level; three names, one route.
- **K-ROUTE-FREE**: a route reaches a configuration
  whose entropy bill no component pays (total
  nedEntropy decreases along a reachability) — a
  perpetual-motion costume; also wounds the
  Entropy-Arrow line, reported jointly.
- **K-ROUTE-THERMAL**: jump reachability on the seat is
  provably independent of the thermal datum — the
  seeing's thermal-jump link dies at the finite level.
- **K-ROUTE-COSTUME**: routeJump collapses into step's
  complement (or any proposition into its definitions)
  on inspection. The line reports it as a costume and
  stops.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- The pin tests a *shadow* of the seeing, not the
  seeing (L2/L3 discipline): a finite route theorem
  neither establishes the continuum reading nor any
  continuum claim. The diagram in the parent scope is a
  schematic of the seeing, not data.

## Brick 0's charge

Definitions and the pinned statements ONLY: 0 strict by
design. Names frozen at this brick: `RouteSphereSeat`,
`routeSeparated`, `routeStanding`, `routeStep`,
`gibbsJumpReach`, `routeJump`, `routeOrder`,
`jumpStrictness`, `thermalOrdersJumps`, `noFreeRoute`.
-/

namespace ThetLogos

/-- **The sphere seat of the comparison.** One named
object carrying everything the three routes are compared
on: a cycle seat over the `Fin 3` ring (the Gibbs seat's
own size — the ring of balance at its smallest honest
size), a distinguished **core** component (the shell is
its complement, `coreᶜ` — not a second field, so the
pair exhausts the seat by construction), the Gibbs
landscape and inverse temperature of the jump seat, and
the one-jump relation on configurations.

**0g, registered as absence:** this field list is the
seat's whole directional content — a core and its
complement. No ordering, no preferred direction, no up
or down is a field here, because in 0g there is none to
register.

**`jumpRel` is an OWED field, labeled as such.** Its
registered reading: `jumpRel p q` when `q` is one Gibbs
jump from `p` — the configuration's position content
moved by one jump under `landscape` and `beta`, in the
sense of `gibbsJumpReach`. Deriving this field from the
jump seat's banked forecast law is Brick 1's first job;
at this brick it is bare seat data with its reading
stated, exactly as `CycleSeat.exch` is bare data with
its reading stated. It is NOT defined as the complement
of step reachability, nor from `arrowStep` in any way —
see the sourcing section on the module's face. -/
structure RouteSphereSeat where
  /-- The underlying cycle seat on the Fin 3 ring. -/
  cycle : CycleSeat (Fin 3)
  /-- The core component; the shell is `coreᶜ`. -/
  core : Finset (Fin 3)
  /-- The Gibbs landscape on the ring positions. -/
  landscape : Fin 3 → ℝ
  /-- The inverse temperature of the jump law. -/
  beta : ℝ
  /-- OWED: the one-jump relation on configurations
  (reading on the structure's docstring; derivation from
  `gibbsJumpReach` is Brick 1's first job). -/
  jumpRel : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop

/-- **Thermal charge separation, registered.** A
configuration `p` is thermally separated on the sphere
seat when the seat's distant component IS the shell
(the heat is held at the shell, at a distance from the
core), `p`'s charge is split across the pair in the
snap's E-stage sense (`cycleChargeSplit` — stated
across `distant`/`distantᶜ`, which under the first
clause is shell/core), and the seat actually carries a
distant-heat datum (`cycleDistantHeat`: an imbalance
supported on the distant component alone). The third
clause is the registration the scope demands: the split
is tied to the seat's thermal datum, not freely chosen —
no distant heat, no registered separation. -/
def routeSeparated (R : RouteSphereSeat) (p : Fin 3 → ℝ) : Prop :=
  R.cycle.distant = R.coreᶜ ∧ cycleChargeSplit R.cycle p ∧
    ∃ h : Fin 3 → ℝ, cycleDistantHeat R.cycle h

/-- **The collapse route: standing reachability,
REUSED.** Exactly `geomStandingHistory` on the sphere
seat's cycle seat — a realizable history every step of
which is a condensation. The classical route of the
diagram: continuous, standing, paying the full cost.
Named here in the pin's dialect; the parent def is
reused, never redefined. -/
def routeStanding (R : RouteSphereSeat)
    (p q : Fin 3 → ℝ) : Prop :=
  geomStandingHistory R.cycle p q

/-- **The step route: dynamical reachability, REUSED.**
Exactly `arrowHistory` on the sphere seat's cycle seat
— reachability by the seat's own derived dynamics (ring
motion ∨ condensation). Tunneling proper is the parent
notion `geomTunnelJoined` (step-reachable with no
standing-only path), referenced on the module's face
and in `routeOrder`'s reading; it is not redefined
here. -/
def routeStep (R : RouteSphereSeat)
    (p q : Fin 3 → ℝ) : Prop :=
  arrowHistory R.cycle p q

/-- **The jump seat's own reachability, DERIVED from its
banked law.** Position `j` is one jump from position
`i` when the Gibbs forecast gives the jump positive
weight: `gibbsForecast landscape β i j > 0`. This is
the Gibbs Jump seat's own data — its forecast law,
banked at `a7cd161` and transplanted byte-identical —
read as a relation. `arrowStep` and its complement
occur nowhere in it: the independence the circularity
audit demands, checkable by reading this def against
`gibbsForecast`'s. (At the position level this relation
is temperature-blind — Gibbs factors are positive at
every `β`; the thermal headwind is named on the
module's face, and the statistics where the thermal
content lives are later-brick debt.) -/
def gibbsJumpReach (R : RouteSphereSeat) (i j : Fin 3) : Prop :=
  0 < gibbsForecast R.landscape R.beta i j

/-- **The jump route: jump reachability on
configurations.** `q` is jump-reachable from `p` when a
finite trajectory of one-jump moves (`R.jumpRel`, the
seat's OWED field — see the sourcing section on the
module's face) runs from `p` to `q`. Registered in the
same trajectory shape as `ArrowPath`, but the moves are
the jump seat's, not the dynamics': no `arrowStep`
occurs in this definition, and the relation is not —
by construction or by registration — the complement of
step reachability. Whether it contains the step route
(`routeOrder`) and whether it exceeds it
(`jumpStrictness`) are claims about the owed field's
eventual derivation, and both can fail. -/
def routeJump (R : RouteSphereSeat)
    (p q : Fin 3 → ℝ) : Prop :=
  ∃ n : ℕ, ∃ traj : ℕ → (Fin 3 → ℝ),
    traj 0 = p ∧ traj n = q ∧
      ∀ k : ℕ, k < n → R.jumpRel (traj k) (traj (k + 1))

/-- **THE FIRST OFFICIAL STATEMENT, pinned as the line's
target — ROUTE ORDER.** The three routes are ordered by
reachability: every standing-reachable pair is
step-reachable, and every step-reachable pair is
jump-reachable. The first inclusion compares two banked
dynamics; the second is a claim about the jump seat's
relation against the derived dynamics — nothing in the
jump seat's data promises it, which is what makes it a
statement and not a construction. Stated in statement
form only; nothing about it is claimed in this brick.
Brick 1+'s charge is the theorem on the smallest seat —
or K-ROUTE-COLLAPSE, each a landing at the same
volume. -/
def routeOrder (R : RouteSphereSeat) : Prop :=
  (∀ p q : Fin 3 → ℝ, routeStanding R p q → routeStep R p q) ∧
    (∀ p q : Fin 3 → ℝ, routeStep R p q → routeJump R p q)

/-- **THE SECOND OFFICIAL STATEMENT, pinned as the
line's target — JUMP STRICTNESS.** Some configuration
is jump-reachable from some configuration without being
step-reachable from it: the jump route goes somewhere
no dynamical path goes — the diagram's purple line has
somewhere to go. A claim about two independently
sourced relations (the derived `arrowHistory` and the
jump seat's `jumpRel`, whose position-level source is
`gibbsJumpReach`); it is true by no definition in this
module, and its failure on the smallest seat is
K-ROUTE-COLLAPSE's firing form. Stated in statement form
only; nothing about it is claimed in this brick. -/
def jumpStrictness (R : RouteSphereSeat) : Prop :=
  ∃ p q : Fin 3 → ℝ, routeJump R p q ∧ ¬ routeStep R p q

/-- **THE THIRD OFFICIAL STATEMENT, pinned as the line's
target — THERMAL ORDERS JUMPS (reachability shadow).**
The jump-reachable set depends on the thermal datum:
there is a second sphere seat agreeing with `R` in its
charge assignment, its exchange, its core, its
landscape, and its temperature, differing ONLY in the
distant component — where the heat is held at a
distance — whose jump-reachable set differs from `R`'s.
Registered in this shadow form on purpose: the scope
flags jump statistics (the forecast values, where the
thermal headwind on the module's face says the thermal
content lives) as later-brick debt, and this statement
registers only what reachability can honestly carry at
this brick. Its failure — jump reachability provably
independent of the thermal datum — is K-ROUTE-THERMAL.
Stated in statement form only; nothing about it is
claimed in this brick. -/
def thermalOrdersJumps (R : RouteSphereSeat) : Prop :=
  ∃ R' : RouteSphereSeat,
    R'.cycle.charge = R.cycle.charge ∧
      R'.cycle.exch = R.cycle.exch ∧
        R'.core = R.core ∧ R'.landscape = R.landscape ∧
          R'.beta = R.beta ∧ R'.cycle.distant ≠ R.cycle.distant ∧
            ∃ p q : Fin 3 → ℝ, routeJump R p q ∧ ¬ routeJump R' p q

/-- **THE FOURTH OFFICIAL STATEMENT, pinned as the
line's target — NO FREE ROUTE.** Along each of the
three reachabilities, the total seat's `nedEntropy`
does not decrease: no route — collapse, step, or jump —
arrives at a configuration of lower entropy than it
started from. Every route pays its bill some way; none
pays nothing. The middle arm is the Entropy-Arrow
conjecture on this seat (`routeStep` is `arrowHistory`,
so that arm is `arrowNoBackwardReturn` verbatim) — the
shared ground is named on the module's face, and
K-ROUTE-FREE, the kill armed against this statement,
wounds both lines and is reported jointly. Stated in
statement form only; nothing about it is claimed in
this brick. -/
def noFreeRoute (R : RouteSphereSeat) : Prop :=
  (∀ p q : Fin 3 → ℝ, routeStanding R p q → nedEntropy p ≤ nedEntropy q) ∧
    (∀ p q : Fin 3 → ℝ, routeStep R p q → nedEntropy p ≤ nedEntropy q) ∧
      (∀ p q : Fin 3 → ℝ, routeJump R p q → nedEntropy p ≤ nedEntropy q)

end ThetLogos
