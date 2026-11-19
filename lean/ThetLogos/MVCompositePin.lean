/-!
# ThetLogos.MVCompositePin — the MV stack's composite record: two seats, roles separated (MV-3, DRAFT)

STATUS: **DRAFT — UNVERDICTED** (lane thet-logos-og0,
branch mv3, drafted 2026-11-11). Design record:
`STATUS-MV3.md` in the lane root. Charter:
`monotonicity-vortex-equilibrium-scope-2026-11-08.md`
§4 (composite verdict + priced residue) + §5.
Pre-registered DIAL-INELIGIBLE. NO CLAIM.

## What this pin freezes

The composite verdict of the MV scoping (§4): the
stack — Zero's "monoticity polar vortex equilibrium"
(2026-11-08, his spelling) — is, at finite size,
**three pins and ONE honest composite exhibit: not
one object.** The composite exhibit is two seats read
together:

- the **ring-graph seat** (MV-1): the Finite Arrow
  package at the cycle — mass the keeper, entropy and
  deviation energy the monotones, the constant fields
  the equilibrium the run delivers;
- the **phase-ring seat** (MV-2): lifts on a phase
  ring under a relaxation step — the winding the
  keeper, the lift Dirichlet energy the monotone, the
  uniform twists at fixed winding the equilibrium the
  run delivers.

Per seat: one keeper, one monotone family, one
characterized equilibrium — three different
quantities/states, no quantity playing two roles
(the MV-0 charter). ACROSS seats: no identification
at all. Mass is not winding; entropy is not the lift
energy; the constant fields are not the uniform
twists. That separation is this pin's own fence
(`MVCompositeFence.crossSeatConflation`, armed).

**Equilibrium is deliberately not a quantity in this
record** (carried from MV-0 D4): it is the
characterized state each seat's run delivers, seated
per seat in `MVSeatEquilibrium` — not a thing that
runs, and not a thing that is kept.

## Honesty of the members at pin time

MV-1 and MV-2 stand **drafted, unverdicted** at the
hour this pin is drafted (see STATUS-MV3.md). This
record names both exhibits AS DESIGNED; the pin's
own build is queued behind MV-2's landing, and a
partial landing anywhere in the set grades this
record's corresponding entries down with it. The pin
does not launder its members' grades.

## Fences

- The continuum wall: the polar vortex lives in
  continuum fluid dynamics; this corpus has none.
  These exhibits stand on the near side of the wall
  and say so. NOT the atmosphere, not weather, not
  the polar vortex, not a fluid (K-MV-PROXY /
  K-MV-ATMOS stand armed in MV-0's registry).
- Roles separated within and across seats
  (K-MV-CONFLATE in MV-0's registry; the composite's
  cross-seat fence below).
- Dials 0/4; nothing in MV-0..MV-3 moves one
  (K-MV-DIAL standing, carried below).
- Working labels only — Zero names public coinages.
-/

namespace ThetLogos

/-- The composite exhibit's two seats. -/
inductive MVSeat where
  | graphSeat
  | phaseSeat
  deriving DecidableEq, Repr

/-- The two exhibits of the composite: MV-1 at the
ring-graph seat, MV-2 at the phase-ring seat. -/
inductive MVSeatExhibit where
  | ringGraphExhibit
  | phaseRingExhibit
  deriving DecidableEq, Repr

/-- Each exhibit's seat. -/
def mvExhibitSeat : MVSeatExhibit → MVSeat
  | .ringGraphExhibit => .graphSeat
  | .phaseRingExhibit => .phaseSeat

/-- The quantities the composite record tracks,
named per seat. Equilibrium is NOT among them — it
is a state, not a quantity (see `MVSeatEquilibrium`). -/
inductive MVSeatQuantity where
  | graphMass
  | graphEntropy
  | graphDeviationEnergy
  | phaseWinding
  | phaseLiftEnergy
  deriving DecidableEq, Repr

/-- The two roles a quantity can play. A quantity
plays exactly one (the role-separation charter). -/
inductive MVSeatRole where
  | keeper
  | monotone
  deriving DecidableEq, Repr

/-- Each quantity's seat. -/
def mvQuantitySeat : MVSeatQuantity → MVSeat
  | .graphMass => .graphSeat
  | .graphEntropy => .graphSeat
  | .graphDeviationEnergy => .graphSeat
  | .phaseWinding => .phaseSeat
  | .phaseLiftEnergy => .phaseSeat

/-- Each quantity's one role: mass and winding are
kept (conserved, never monotone); entropy, deviation
energy, and the lift Dirichlet energy run one way
(monotone/antitone, never conserved). -/
def mvQuantityRole : MVSeatQuantity → MVSeatRole
  | .graphMass => .keeper
  | .graphEntropy => .monotone
  | .graphDeviationEnergy => .monotone
  | .phaseWinding => .keeper
  | .phaseLiftEnergy => .monotone

/-- The characterized equilibria, as STATES: what
each seat's run delivers. Different constructors at
different seats — the constant fields are not the
uniform twists, and this record keeps them apart. -/
inductive MVSeatEquilibrium where
  | constantFields
  | uniformTwists
  deriving DecidableEq, Repr

/-- Each seat's equilibrium: the graph seat's flow
delivers the constant fields; the phase seat's
relaxation delivers the uniform twists at fixed
winding — at nonzero winding, a ring at rest still
carrying its twist. -/
def mvSeatEquilibrium : MVSeat → MVSeatEquilibrium
  | .graphSeat => .constantFields
  | .phaseSeat => .uniformTwists

/-- The composite's own fences. -/
inductive MVCompositeFence where
  | crossSeatConflation
  | dial
  deriving DecidableEq, Repr

/-- A fence's standing. -/
inductive MVFenceStatus where
  | armed
  | standing
  deriving DecidableEq, Repr

/-- The cross-seat conflation fence is ARMED: it
fires on any face that identifies the two seats'
keepers, monotones, or equilibria with one another.
The dial fence is STANDING: nothing in the composite
moves a dial, on any outcome. -/
def mvCompositeFenceStatus : MVCompositeFence → MVFenceStatus
  | .crossSeatConflation => .armed
  | .dial => .standing

end ThetLogos
