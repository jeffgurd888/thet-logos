import Mathlib.Tactic

/-!
# ThetLogos.SwimMemoryPin — the structured water / ice memory projection, registered (T5)

Zero's seeing of 2026-11-24 10:49 EST: "let's investigate the
structured water ice memory projection I don't think we quite
understand even the basics yet so let's make the simple math
work so we can explain the complex." Scope of record:
`~/workspace/your_files/structured-water-ice-memory-scope-DRAFT-2026-11-24.md`.
Brick 0 fired by Zero's word, 2026-11-24 23:26 EST.

TIER: T5 investigation of a finite toy. NO CLAIM — about real
water, real ice, or any physical system, under EVERY outcome
of this line, including total success. No dial moves; no
corpus object outside this line is fed by it. Nothing in this
module states, values, or approximates any constant of
nature, and no gravity object is constructed, fed, or
identified. The working label is Zero's; final module naming
is his hand.

## The three territories (carried on the face, every time)

The phrases "structured water" and "ice memory" are used in
the world for at least three different things. They are not
one subject, and this line lives or dies on keeping them
apart.

- **(a) ESTABLISHED physics — citable context only, never
  ground.** Ice and water genuinely store records. Ice cores
  carry isotope and trapped-gas archives — a physical sample
  whose present state encodes the path of its formation.
  Latent heat is stored thermal history: the energy a phase
  change absorbed is recoverable on reversal. Hysteresis and
  path-dependence are standard, measured behaviour of
  first-order transitions and of disordered systems
  generally. Proton disorder in ice Ih is a proved structural
  fact (the Bernal–Fowler ice rules leave a residual entropy;
  Pauling's count is textbook). This territory is the reason
  the words are not empty — but nothing in this line proves
  anything about it, and no definition below leans on it.
- **(b) CONTESTED — never ground.** Pollack's exclusion-zone
  water: the exclusion phenomenon near hydrophilic surfaces
  is observed and published; the claimed interpretation — a
  distinct, ordered, liquid-crystalline phase ("EZ water")
  with its own structure — is disputed in the literature. It
  is cited here as contested, by name, and nothing else: no
  definition, brick, or argument in this line leans on it,
  cites it as support, or borrows its vocabulary as if
  settled.
- **(c) NOT ESTABLISHED — fenced out by name.** "Water
  memory" in the Benveniste / homeopathic sense: information
  supposedly retained by water after dilution past the
  Avogadro limit. The original claims failed replication
  under controlled conditions and no mechanism consistent
  with established physics has been demonstrated. This
  territory is named only to fence it out. It is not a softer
  version of (a); it is a different claim, and it is dead on
  arrival here (K-SWIM-IMPORT, below).

The toy below is built entirely inside a fourth, much smaller
place: a finite cell whose behaviour can be defined, proved,
and killed without borrowing authority from any of the three.

## The simple math (the definitions this brick registers)

- **MEMORY, minimal definition.** A finite system has memory
  at a seat when its present state is NOT a function of its
  present input alone — the state depends on the path taken
  to reach that input. That is hysteresis, stated as a
  definition rather than an analogy. The minimal exhibit: a
  **bistable cell** — two stable states, switching thresholds
  asymmetric (the classic relay / hysteron): driven up past
  one threshold it flips one way, driven down past a
  *different* threshold it flips back, and between the
  thresholds it stays where its history put it. The drive is
  a finite input history: a finite list of input values,
  applied in order. The state is a function of the history,
  defined by recursion on the list — nothing else is hidden
  in the word "memory" anywhere in this line.
- **PROJECTION, minimal definition.** "Projection" is Zero's
  word and it gets an in-tree definition, not a borrowed one:
  a **readout map** — in this corpus's idiom, a pairing /
  readout on the finite seat (the Shadow line's pairing
  discipline is the local precedent: a pairing is asked what
  distinction it can and cannot recover) — applied to the
  cell's state, and asked to distinguish *histories*. The
  test question is exact: take two different input histories
  that end at the **same present input**; if the readout
  separates their end states, the projection reads the
  memory; where it cannot separate them, it does not, and
  Brick 2 prices what it identifies instead.
- **What a projection is not.** A readout that distinguishes
  *everything* — every pair of histories the cell can be
  driven through — is not a projection but a copy of the
  history itself, and calling it one would be a naming fraud
  this line refuses in advance. A projection earns its name
  by what it forgets as much as by what it keeps.

## The question (failable, stated as pins in this brick)

1. **(Q-memory)** Do two input histories exist that end at
   the same present input and leave the cell in different
   states — and does the registered readout separate those
   states? Registered below as `swimMemoryClaim`, in
   statement form only. Brick 1's charge: the theorem, or
   its kill.
2. **(Q-limits)** Exactly which history-distinctions does
   the readout identify — what is the projection's kernel?
   The kernel relation is registered below as `swimKernel`;
   its characterisation is Brick 2's charge.

The honest prior, stated at full rank before any proof is
attempted: Q-memory is priced as likely provable, because
separating two histories is what bistability IS. The content
of Brick 1 is the exact statement — the cell, the thresholds,
the two histories, the readout, all pinned — not surprise.

## Brick 0's charge, and the stopping condition

This brick registers objects and statement pins ONLY: the
cell, the drive, the state-as-function-of-history, the
readout, the projection, the two pins, and — per Amendments
A and B — Seat 2's dissolved-field and circulation
registrations. Nothing is proved in this brick: 0 strict by
design.

STOPPING CONDITION (pre-registered in the scope): if the
definitions could not be stated without smuggling territory
(b) or (c) into the ground, the line stops here and that
failure IS the finding. Discharge note, stated on the face:
every definition below is built from `Bool`, `ℚ`, finite
lists, and finite sums alone. No definition names, cites, or
borrows the vocabulary of territory (b) or (c); the words
"structured water" and "ice memory" appear in this module
only beside the three-territory distinction above, per the
naming fence. The condition does not trigger; the line
proceeds to its gate.

## Amendment A — Seat 2: the dissolved field (definitions only)

Zero, 2026-11-24 10:51 EST: "what I want to know about is
dissolved magnetism." The basics, at their tiers: pure water
is diamagnetic; the magnetism of a real water sample is
carried by what is DISSOLVED in it — dissolved O₂
(paramagnetic) and paramagnetic ions (Fe³⁺, Mn²⁺, Cu²⁺,
Gd³⁺) — measurable as susceptibility and as NMR relaxation
shortening (the MRI contrast principle). Ferrofluids are
suspensions, not solutions. Persistent "magnetized water" is
not established and is fenced out with territory (c)
discipline: Amendment A's seat is dissolved carriers only.

Registered below, as definitions only: a concentration field
over a finite seat (`c : V → ℚ`, a finite toy quantity named
for what it is — no def is needed to name a function type,
and none is registered), a mixing rule `swimMixStep` (one
dissolving step: each site moves halfway toward the seat
mean), and a susceptibility-weighted readout pairing
`swimMagReadout` (the magnetic projection: the concentration
read through a susceptibility field `χ`). The line's honest
race, stated in advance: **dissolution erases distinctions
while the projection reads them** — memory exists at this
seat only where the readout separates patterns faster than
mixing identifies them. Seat 2's own brick is priced after
Brick 2; this brick registers its objects and proves nothing
about them. NO CLAIM about any real solution.

## Amendment B — the circulation sector (definitions only)

Zero, 2026-11-24 10:53 EST: "graviomagnetic." The standard
term is gravitomagnetism: established GR (weak-field GEM
equations; frame-dragging measured by Gravity Probe B and
LAGEOS/LARES) — and at the same time **not a substance**: it
cannot be dissolved, stored, or shielded, and no
susceptibility of water exists for it. It enters this line
ONLY in the finite shape the corpus already owns and has
already fenced: the **circulation sector**. Seat 2's field is
therefore concentration **plus** current — a flow
`X : V → V → ℚ` on the seat's edges — and the readout is
asked to separate flow patterns as well as concentration
patterns. The edge pairing is registered below as
`swimFlowPairing`.

The Vortex fences ride verbatim: a circulation the readout
detects is a property of the finite pairing, **not a gravity
object (K-VORTEX-GRAVITY)**; and the pairing's antisymmetric
sector is not gravitomagnetism in any physical sense. NO
CLAIM about frame-dragging, GR, or any rotating fluid.

## Kills pre-registered (armed by this registration, not fired by it)

- **K-SWIM-EMPTY** — if the readout distinguishes **no** pair
  of histories that end at the same present input in
  different states, the "memory projection" is empty — a
  readout of nothing. The name does not survive its content
  failing; if this fires, the line's product is the
  refutation, stated that way.
- **K-SWIM-STATELESS** — if the cell's state, as registered,
  collapses to a function of its present input alone, there
  is **no memory at the seat, only response**. Fires as a
  theorem about the registered cell, at full rank.
- **K-SWIM-IMPORT** — fires on sight at ANY brick, in draft
  or in module text: any claim, definition, or argument
  importing territory (b) or (c) — EZ "structured water"
  treated as ground or as a phase this toy models, dilution /
  homeopathic memory in any form, or vocabulary borrowed
  from either to lend the toy authority — dies where it
  stands, and the brick that carried it is reported, not
  quietly edited.
- **K-SWIM-DISSOLVE-EMPTY** (Seat 2) — the weighted readout
  distinguishes no pair of concentration patterns.
- **K-SWIM-DISSOLVE-ERASE** (Seat 2) — one mixing step
  identifies every pair of patterns: no memory, only
  dissolution.
- **K-SWIM-CIRC-EMPTY** (Seat 2, Amendment B) — if the
  readout identifies every pair of distinct circulations,
  the current carries no memory at the seat.

## Fences

- **Naming fence.** The words "structured water" and "ice
  memory" appear in this line's module text **only** beside
  the three-territory distinction that fences them. The
  toy's own objects are named for what they are (cell, drive,
  history, readout) — the seeing's words name the
  investigation, never the toy's theorems.
- **No-physics fence.** No claim about real water, real ice,
  any material, any experiment, or any therapy, under any
  outcome. Ice cores, latent heat, and ice Ih proton disorder
  appear only as territory (a) context — established physics
  this line cites and does not extend. A proved finite
  theorem here is not evidence about a physical system, and
  the line never presents it as any.
- **No-dial fence.** No dial moves; no corpus object outside
  this line is fed by it; FRONTIER (any continuum, field, or
  physical-chemistry reading of the toy) is never priced.

## Queue

Brick 1 (the memory theorem, or its kill) does not draft
until Zero's fresh word, and Brick 2 does not draft until
Brick 1's verdict is known, since the kernel characterisation
depends on which readout survived.
-/

namespace ThetLogos

/-- **The switching rule of the bistable cell.** The cell
carries two stable states (`Bool`: `false` = low, `true` =
high) and two asymmetric thresholds `lo ≤ hi` in intention —
the asymmetry IS the memory: driven up to or past `hi`
(`hi ≤ u`) the cell flips high; driven down to or past `lo`
(`u ≤ lo`) it flips low; strictly between the thresholds it
stays where its history put it. One input, one step; nothing
else is hidden in the rule. (No hypothesis `lo ≤ hi` is
carried: the rule is registered as stated, and what the
thresholds do is Brick 1's to test, not this def's to
assume.) -/
def swimStep (lo hi : ℚ) (s : Bool) (u : ℚ) : Bool :=
  if hi ≤ u then true
  else if u ≤ lo then false
  else s

/-- **The state as a function of the history.** A drive is a
finite input history — a finite list of input values,
applied in order — and the cell's state after the drive is
the fold of the switching rule over that list, from the
initial state `s₀`. The recursion on the list is the whole
definition: the state is a function of the history, and of
nothing else. -/
def swimRun (lo hi : ℚ) (s₀ : Bool) (h : List ℚ) : Bool :=
  h.foldl (swimStep lo hi) s₀

/-- **The registered cell.** The line's one working exhibit:
thresholds `lo = 0` and `hi = 1` — asymmetric, with the whole
open interval `(0, 1)` as the band where the cell stays
where its history put it — starting low (`false`), driven by
the history `h`. Every later brick of this line speaks about
this cell, or says on its face that it has changed it. -/
def swimCellRun (h : List ℚ) : Bool :=
  swimRun 0 1 false h

/-- **The readout on the state space.** The projection's
measuring half, registered at its smallest honest size: the
end state read as a quantity — low reads `0`, high reads
`1`. A readout map on the finite seat, in the corpus's
pairing discipline (the Shadow line's precedent: a readout
is asked what distinction it can and cannot recover). What
this readout separates, and what it identifies, is the
line's question — not this def's claim. -/
def swimReadout (s : Bool) : ℚ :=
  if s then 1 else 0

/-- **The projection.** Zero's word, given an in-tree
definition: the readout applied to the state a history
leaves the registered cell in. A map from histories to
quantities that factors through the end state — it earns
the name "projection" by what it forgets (everything about
the history except where it left the cell) as much as by
what it keeps. Brick 2 prices the forgetting exactly. -/
def swimProjection (h : List ℚ) : ℚ :=
  swimReadout (swimCellRun h)

/-- **Q-memory, frozen as a pin.** Two input histories exist
that end at the same present input (the same last-applied
value, `List.getLast?` — both empty histories included, at
present input `none`) and leave the registered cell in
different states, AND the registered projection separates
those states. Stated in statement form only; nothing about
it is claimed in this brick. Brick 1's charge is the
theorem — or K-SWIM-STATELESS (the states never differ) or
K-SWIM-EMPTY (they differ and the readout does not separate
them), each a landing at the same volume. -/
def swimMemoryClaim : Prop :=
  ∃ h₁ h₂ : List ℚ, h₁.getLast? = h₂.getLast? ∧
    swimCellRun h₁ ≠ swimCellRun h₂ ∧ swimProjection h₁ ≠ swimProjection h₂

/-- **The projection's kernel, registered as a relation.**
Two histories stand in the kernel relation when they end at
the same present input and the projection reads them as
one. This is the identification Q-limits asks about, made an
object: Brick 2's charge is its characterisation — which
history-distinctions this relation erases, stated as an iff
or an explicit identification list at the seat — not its
existence, which is this def's whole content. -/
def swimKernel (h₁ h₂ : List ℚ) : Prop :=
  h₁.getLast? = h₂.getLast? ∧ swimProjection h₁ = swimProjection h₂

/-- **One mixing step (Seat 2, Amendment A).** The
dissolving, as a rule: each site moves halfway from its own
concentration toward the seat mean — the uniform pattern is
the step's fixed point, and distinctions shrink toward it.
A concentration field is a function `c : V → ℚ` over a
finite seat `V` (a finite toy quantity, named for what it
is; no real solution is modeled). Whether any distinction
survives repeated mixing long enough for the readout to read
it is Seat 2's race, priced in its own brick —
K-SWIM-DISSOLVE-ERASE is this step identifying every pair of
patterns, and it is armed, not fired, by this def. -/
def swimMixStep {V : Type*} [Fintype V] (c : V → ℚ) (v : V) : ℚ :=
  (c v + (∑ w, c w) / (Fintype.card V : ℚ)) / 2

/-- **The susceptibility-weighted readout (Seat 2,
Amendment A).** The magnetic projection: a concentration
pattern `c` read through a susceptibility field `χ` — the
seat's dissolved carriers weighted by how strongly each
site answers a field, summed over the seat. This is the MRI
contrast principle stated as a finite pairing: the signal is
carried by what is dissolved, and the readout sees the
pattern only through the carriers' weights. Whether it
distinguishes any pair of patterns is K-SWIM-DISSOLVE-EMPTY's
question, in Seat 2's brick — not this def's claim. -/
def swimMagReadout {V : Type*} [Fintype V] (χ c : V → ℚ) : ℚ :=
  ∑ v, χ v * c v

/-- **The edge pairing (Seat 2, Amendment B).** Seat 2's
current is a flow `X : V → V → ℚ` on the seat's edges; this
is the pairing the circulation readout is built from — the
full ordered double sum of one flow against a probe flow,
this tree's one pairing convention. A circulation this
pairing detects is a property of the finite pairing, not a
gravity object (K-VORTEX-GRAVITY, riding verbatim from the
Vortex line), and the pairing's antisymmetric sector is not
gravitomagnetism in any physical sense. Which pairs of
distinct circulations the readout identifies is
K-SWIM-CIRC-EMPTY's question, in Seat 2's brick. -/
def swimFlowPairing {V : Type*} [Fintype V] (X Y : V → V → ℚ) : ℚ :=
  ∑ i, ∑ j, X i j * Y i j

end ThetLogos
