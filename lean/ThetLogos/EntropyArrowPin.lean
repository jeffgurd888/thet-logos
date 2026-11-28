import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin

/-!
# ThetLogos.EntropyArrowPin — the entropy arrow, registered (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Zero's
conjecture, in his words (2026-11-27 23:34 EST): "I would
like to prove the conjecture that thermal entropy
prevents backwards time travel. but not forward." Scope
of record:
`~/workspace/your_files/entropy-arrow-scope-DRAFT-2026-11-27.md`.
This pin rides the continuum lane's seat
(`ThetLogos.ContinuumCyclePin`, Brick 0 banked
2026-11-27): the `CycleSeat`, its exchange, its snap
stages, its balanced state, and the NED functionals
(`nedEntropy`, `nedCharge`) are reused untouched.

## CHARTER — NO CLAIM

This line proves the FINITE shadow only, in the corpus's
own seats. Per Zero's own register (2026-11-24): a
completed finite theorem is not a continuum theorem.
Tier: T5 charter, NO CLAIM; dials unmoved (0/4) unless a
proved theorem closes part of a pre-registered
statement. QTFT/QTST remain candidate names, not worn by
this line. No gravity object is constructed, fed, or
identified.

## TIERS, STATED ONCE

- **FORWARD**: time dilation is measured physics (muons,
  GPS clocks, Hafele–Keating) — traveling forward is
  what entropy increase already does. T1 as physics.
- **BACKWARD**: open in physics. The famous neighbor is
  Hawking's chronology protection conjecture (1992) —
  but Hawking's mechanism is quantum vacuum divergence
  at a chronology horizon, NOT entropy. Zero's entropic
  version is its own conjecture, with its own mechanism,
  and it stands or falls on its own. FRONTIER as
  physics, NO CLAIM.

## The official statements (pinned verbatim at this brick)

**FORWARD EXISTS: from a low-entropy configuration
there is a realizable history (decay) reaching the
balanced state with entropy strictly increasing along
the way. The future is reachable.**

**NO BACKWARD RETURN: no realizable history returns the
seat to a strictly earlier (lower-entropy)
configuration. The seat's past is unreachable BY THE
SEAT'S OWN DYNAMICS — the finite shadow of "thermal
entropy prevents backwards time travel."**

Registered below as `arrowForwardExists` and
`arrowNoBackwardReturn`, bundled as `arrowConjecture`,
in statement form only. Nothing about either is claimed
in this brick: Brick 1+ takes monotonicity from the
derived dynamics on the smallest seat — or the kills.

## THE CIRCULARITY AUDIT (quoted from the scope; the trap, named before it is stepped in)

"If the transition relation is DEFINED as
'entropy-nondecreasing steps,' the no-return theorem is
the definition wearing a costume — the Composition Rule
(L15) kills it as content. The non-trivial version, and
the only one this line accepts: the transition relation
is DERIVED from the seat's own dynamics (the exchange /
ring motion / decay already pinned in the pair and
cycle machinery), and entropy monotonicity is then
PROVED as a theorem about those dynamics — or it fails,
and the failure is the verdict."

## How the step relation is sourced at this brick (the audit's demand, made visible)

`arrowStep` below is assembled from the two relational
dynamics the tree already pins, and from nothing else:

- **ring motion** (`cycleRingMotion`): `p'` is `p`
  carried by the seat's exchange — the snap's M stage;
- **condensation** (`cycleCondensed`): `p'` stands
  under the exchange and carries `p`'s charge
  undiminished — the snap's C stage.

`nedEntropy` occurs NOWHERE in `arrowStep`, in
`ArrowPath`, or in `arrowHistory`. Entropy enters this
module only inside the two propositions, where a
conjecture about it belongs. The step relation is
therefore DERIVED (assembled from pinned dynamics), not
registered as an owed hypothesis, and not the entropy
inequality in disguise — K-ARROW-TRIVIAL is armed
against exactly that disguise, and this registration is
built so the kill can be checked by reading the def.

Three honest caveats, on the face:

- **The snap's E stage is not a step.** `cycleChargeSplit`
  is a property of a single configuration, not a move
  between configurations, so it does not appear in
  `arrowStep`. The steps are the snap's two relational
  stages, M and C.
- **No decay operator is invented here.** The cycle
  line registered decay as bare return and pinned no
  decay operator (see `ContinuumCyclePin`'s face);
  accordingly this pin registers no third "decay" step.
  A "decay history" at this brick is a path of motion
  and condensation steps reaching a balanced
  configuration. Registering a decay operator remains a
  later brick's stated change, never a silent one.
- **`exch` is still bare seat data.** It is not assumed
  involutive or bijective at this brick, so ring motion
  is NOT registered as entropy-preserving: whether these
  steps can lower entropy is a genuine question about
  the dynamics, which is exactly what
  `arrowNoBackwardReturn` asserts and K-ARROW tests.
  Nothing in the step definition rigs the answer either
  way.

## How it meshes with the cycle (Zero's two conjectures constrain each other)

The ContinuumCyclePin cycle re-fires the snap out of
the balanced (maximal-entropy) state — which on a
CLOSED seat would require an entropy decrease, exactly
what this conjecture forbids. Resolution already built
into the cycle's Brick 0: the snap is paid for by
DISTANT HEAT — a second component whose imbalance
settles the entropy bill. So: within one closed seat,
no backward return, ever; the cosmic cycle turns only
because no seat is alone. If the finite work shows the
cycle closing on a closed seat without the distant
component paying, one of tonight's two conjectures dies
at the finite level — and the kill says which.

## Kills pre-registered (quoted verbatim from the scope; armed by this registration, not fired by it)

- **K-ARROW**: the seat's derived dynamics contain a
  backward step — a realizable history returning to a
  lower-entropy configuration. The conjecture dies at
  the finite level.
- **K-ARROW-TRIVIAL**: monotonicity turns out
  definitional (the transition relation was the entropy
  inequality in disguise). The "theorem" is a costume;
  the line reports it as such and stops.
- **K-ARROW-FORWARD**: no entropy-increasing decay
  history to the balanced state exists on the smallest
  seat — even the forward direction fails, and the
  conjecture's easy half dies too.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- The pin tests a *shadow* of the conjecture, not the
  conjecture (L2/L3 discipline): a finite arrow theorem
  neither establishes backward-time-travel impossibility
  in the continuum nor any continuum claim.

## Brick 0's charge

Definitions and the pinned statements ONLY: 0 strict by
design. Names frozen at this brick: `arrowStep`,
`ArrowPath`, `arrowHistory`, `arrowForwardExists`,
`arrowNoBackwardReturn`, `arrowConjecture`.
-/

namespace ThetLogos

/-- **One step of the seat's own dynamics.** `p` steps
to `p'` when `p'` is obtained from `p` by one of the
two relational moves the cycle machinery already pins:
**ring motion** (`cycleRingMotion` — `p'` is `p`
carried by the exchange, the snap's M stage) or
**condensation** (`cycleCondensed` — `p'` stands under
the exchange and preserves `p`'s charge, the snap's C
stage). Read the body: `nedEntropy` does not occur in
this definition, nor anywhere in the history structure
below. That absence is the circularity audit's whole
demand — the steps come from the dynamics, and entropy
is what the propositions are *about*, never what a step
*is*. (The snap's E stage, `cycleChargeSplit`, is a
property of one configuration, not a move, and so is
not a step.) -/
def arrowStep {Ω : Type*} [Fintype Ω] (S : CycleSeat Ω)
    (p p' : Ω → ℝ) : Prop :=
  cycleRingMotion S p p' ∨ cycleCondensed S p p'

/-- **A realizable history: a finite path of dynamical
steps.** A trajectory `traj` of `len` steps from `p` to
`q`: `traj 0 = p`, `traj len = q`, and every consecutive
pair is one `arrowStep` — one move of the seat's own
dynamics. No entropy condition appears anywhere in this
structure; a history is realizable purely by the
dynamics, and whether entropy can fall along one is the
conjecture, not the definition. -/
structure ArrowPath {Ω : Type*} [Fintype Ω] (S : CycleSeat Ω)
    (p q : Ω → ℝ) where
  /-- The number of steps in the path. -/
  len : ℕ
  /-- The trajectory: the configuration at each step. -/
  traj : ℕ → Ω → ℝ
  /-- The path starts at `p`. -/
  start : traj 0 = p
  /-- The path ends at `q`. -/
  finish : traj len = q
  /-- Every consecutive pair is one dynamical step. -/
  steps : ∀ k : ℕ, k < len → arrowStep S (traj k) (traj (k + 1))

/-- **Reachability by the seat's own dynamics.** `q` is
reachable from `p` when a realizable history
(`ArrowPath`) runs from `p` to `q`. Pure dynamics:
entropy is not consulted. -/
def arrowHistory {Ω : Type*} [Fintype Ω] (S : CycleSeat Ω)
    (p q : Ω → ℝ) : Prop :=
  Nonempty (ArrowPath S p q)

/-- **THE FIRST OFFICIAL STATEMENT, pinned as the line's
target — FORWARD EXISTS.** From any configuration `p`
of strictly lower entropy than a balanced configuration
`b`, there is a realizable history from `p` to `b`
along which `nedEntropy` strictly increases at every
step: the future (the balanced state) is reachable, and
reachable uphill. This is the conjecture's forward
half — "but not forward": entropy does not prevent
forward travel; it is the road. Stated in statement
form only; nothing about it is claimed in this brick.
Brick 1+'s charge is the theorem on the smallest seat —
or K-ARROW-FORWARD, each a landing at the same
volume. -/
def arrowForwardExists {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ p b : Ω → ℝ, cycleBalanced S b → nedEntropy p < nedEntropy b →
    ∃ path : ArrowPath S p b,
      ∀ k : ℕ, k < path.len →
        nedEntropy (path.traj k) < nedEntropy (path.traj (k + 1))

/-- **THE SECOND OFFICIAL STATEMENT, pinned as the
line's target — NO BACKWARD RETURN.** No realizable
history lowers entropy: whenever `q` is reachable from
`p` by the seat's own dynamics, `nedEntropy p ≤
nedEntropy q`. Equivalently: no history returns the
seat to a configuration of strictly lower entropy than
its start — the seat's past is unreachable by the
seat's own dynamics, the finite shadow of "thermal
entropy prevents backwards time travel." Stated in
statement form only; nothing about it is claimed in
this brick. The statement is a genuine conjecture about
`arrowStep` as defined — `exch` is bare data here, and
a backward step, if one exists in these dynamics, is
K-ARROW, armed on this module's face. -/
def arrowNoBackwardReturn {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ p q : Ω → ℝ, arrowHistory S p q → nedEntropy p ≤ nedEntropy q

/-- **THE CONJECTURE, pinned as one named object.**
Zero's conjecture at the finite level, on one seat: the
future is reachable uphill (`arrowForwardExists`) and
the past is unreachable (`arrowNoBackwardReturn`) —
thermal entropy prevents backwards time travel, but not
forward. Statement form only; this brick claims nothing
about it. -/
def arrowConjecture {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) : Prop :=
  arrowForwardExists S ∧ arrowNoBackwardReturn S

end ThetLogos
