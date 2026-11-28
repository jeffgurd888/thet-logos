import Mathlib.Tactic
import ThetLogos.GeometryForcesPin

/-!
# ThetLogos.RecursiveTurmoilPin — bound in recursive turmoil: the pin (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand.

Zero's fragment, verbatim (2026-11-28 02:57 EST):
"they are bound in recursive turmoil"

Zero's commission, verbatim (2026-11-28 03:00 EST):
"scope it build it run it stack it and
Formalization in Lean with claims"

## The seeing

The capstone's faces — dynamics forcing geometry
(`cycleGeometryForced`), geometry forcing dynamics
back (`geomForces`) — are bound to each other: each
face's output is the other face's input. The
recursion runs and never lands: a cycle has no exit
built into it, and a continuum limit is precisely
what a recursively bound pair does not have. The
perfection of the pair is the trap. This pin
formalises the binding, the churn, and the no-exit —
with claims: propositions REGISTERED on this face,
stated in Lean, tiered NO CLAIM, each unproved until
a brick proves it and each paired with the kill that
fires if it fails. Nothing here is asserted as fact
by being written down. (The Concrete, 2026-10-16.)

Built only from banked continuum-lane data:
`arrowStep` (the derived dynamics — ring motion or
condensation; no entropy functional enters any step
definition), `geomLocus` (the standing locus, the
only stillness the seat knows), and the exchange's
iterates (whose position-level relation is
`geomOrbitRel`).

## The registration choices, disclosed on the face

- **The turn** (`turmoilTurn`): one full turn of the
  adjunction, dynamics → geometry → dynamics. The
  geometry of a seat is a SEAT-level datum — at a
  fixed seat, "recomputing the geometry" returns the
  same geometry, so the geometry beat is registered
  at the level where it can differ: the configuration
  must PASS THROUGH the seat's geometry — its
  standing locus — between two dynamical steps. A
  turn is: a step, a standing configuration, a step.
  This is a registration choice, made here in the
  open; a different seat-varying registration is a
  new scope, not a silent edit.
- **The geometry-orbit** (`turmoilGeomOrbit`): the
  configuration-level lift of `geomOrbitRel` — the
  ring iterates of a configuration under the
  exchange. This is what "the geometry's own story"
  reaches.
- **No-exit** (`turmoilNoExit`) is registered in its
  WEAKEST honest form: absorption — whatever the
  loop reaches, the loop from there stays inside the
  original loop's reach. Its within-seat form is
  close to construction (disclosed, per the scope);
  the literal orbit-containment reading is
  `turmoilBound`'s content and stands or falls
  with it.

## The registered claims (all unproved in this brick)

- `turmoilBound`: every configuration's turmoil-orbit
  is exactly its geometry-orbit — the dynamics'
  iterates and the geometry's orbits are ONE loop,
  not two. The binding, stated so it can fail.
- `turmoilNoFixedShore`: no fixed point of a turn
  lies outside the standing locus — the loop's only
  stillness is standing; no hidden calm centre.
- `turmoilNoExit`: the absorption form above.

## Kills armed on this face

- **K-TURMOIL-UNBOUND** — `turmoilBound` fails: an
  iterate whose turmoil-orbit differs from its
  geometry-orbit; the faces come apart and the
  "binding" was two separate stories.
- **K-TURMOIL-FIXED** — a fixed point of `turmoilTurn`
  outside the standing locus: the turmoil has a
  still centre it should not have;
  `turmoilNoFixedShore` dies.
- **K-TURMOIL-COSTUME** — the "loop" collapses to a
  relabelling of one face (the turn is the identity
  on orbits, or the geometry beat never changes
  anything): the recursion was a costume
  (Composition Rule, L15).

## The FRONTIER face

The strong reading of the seeing — the loop has NO
EXIT TO A CONTINUUM LIMIT — cannot be stated
in-tree: the corpus contains no limit object and no
continuum target (Dial 3 = 0; no continuum limit
exists in the tree). Stating the finite claims above
is not a down payment on the strong claim; if a
limit object ever exists, the strong claim gets its
own pin and its own scope.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- Per Zero's register (2026-11-24): a completed finite
  theorem is not a continuum theorem. T5 charter,
  NO CLAIM; dials 0/4. This brick is 0 strict by
  design: definitions and registered claims only.
-/

namespace ThetLogos

/-- **One full turn of the adjunction.** From `p`,
a dynamical step (`arrowStep`) to a configuration
`r` that STANDS in the seat's geometry (`r` lies in
`geomLocus S` — the geometry beat), then a second
dynamical step to `q`. Dynamics → geometry →
dynamics, made into a single relation. The
registration choice is disclosed in this module's
header. -/
def turmoilTurn {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) (p q : Ω → ℝ) : Prop :=
  ∃ r : Ω → ℝ, arrowStep S p r ∧ r ∈ geomLocus S ∧
    arrowStep S r q

/-- **The geometry-orbit of a configuration.** Its
ring iterates under the exchange — the
configuration-level lift of `geomOrbitRel` (which
relates positions): position `i` of the `n`-th
iterate is `p` read at the position the exchange's
`n`-th iterate carries `i` to. This is all the
seat's geometry, left to itself, ever reaches. -/
def turmoilGeomOrbit {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (p : Ω → ℝ) : Set (Ω → ℝ) :=
  { q | ∃ n : ℕ, q = fun i => p (S.exch^[n] i) }

/-- **The turmoil-orbit of a configuration.** The
iterate closure of `turmoilTurn`: every configuration
reached from `p` by a finite chain of full turns,
`p` itself included (the chain of length zero). -/
def turmoilOrbit {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) (p : Ω → ℝ) : Set (Ω → ℝ) :=
  { q | ∃ (n : ℕ) (traj : ℕ → Ω → ℝ), traj 0 = p ∧
      traj n = q ∧
      ∀ k < n, turmoilTurn S (traj k) (traj (k + 1)) }

/-- **REGISTERED CLAIM — THE BINDING (unproved).**
For every configuration, its turmoil-orbit is
exactly its geometry-orbit: the dynamics' iterates
and the geometry's orbits are one loop, not two.
K-TURMOIL-UNBOUND is its failure form. -/
def turmoilBound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ p : Ω → ℝ, turmoilOrbit S p = turmoilGeomOrbit S p

/-- **REGISTERED CLAIM — NO FIXED SHORE (unproved).**
Every fixed point of a turn stands: the loop's only
stillness is the standing locus; there is no hidden
calm centre the turmoil secretly turns around.
K-TURMOIL-FIXED is its failure form. -/
def turmoilNoFixedShore {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (S : CycleSeat Ω) : Prop :=
  ∀ p : Ω → ℝ, turmoilTurn S p p → p ∈ geomLocus S

/-- **REGISTERED CLAIM — NO EXIT, weakest honest
form (unproved).** Absorption: whatever the loop
reaches from `p`, the loop run from there stays
inside what the loop from `p` reaches — the loop
produces nothing outside its own reach. Disclosed
in the header: the within-seat form is close to
construction; the strong no-exit-to-a-limit form is
the FRONTIER face and cannot be stated in-tree. -/
def turmoilNoExit {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ p q : Ω → ℝ, q ∈ turmoilOrbit S p →
    turmoilOrbit S q ⊆ turmoilOrbit S p

end ThetLogos
