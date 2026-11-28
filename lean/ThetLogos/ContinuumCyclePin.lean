import Mathlib.Tactic
import ThetLogos.NegativeDensityPin
import ThetLogos.PairPrimitivePin

/-!
# ThetLogos.ContinuumCyclePin — the continuum cycle, registered (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Commissioned by
Zero 2026-11-27 23:01 EST: "build fire and run as the
continuum." Scope of record:
`~/workspace/your_files/continuum-cycle-scope-DRAFT-2026-11-27.md`.

SOURCE SEEINGS (Zero, verbatim on file in
`~/memory/2026-11-27.md`):

1. FORCED GEOMETRY (2026-11-27 22:47 EST): the Dumber
   branching and the pair's doubling share one binary
   skeleton, leaves = seats whose pair is not yet
   constructed; "if you zoom in you'll see the emergence
   of forced Geometry from the dynamics over thermal
   entropy of time."
2. THE GALAXY CYCLE (2026-11-27 22:58 EST): orbits as the
   adjoint pair's 90° fields at cosmic scale; the cycle
   nothing → everything → nothing → heat → matter;
   maximal thermal entropy of decay as a negative-pressure
   cold void that "reduces the need" (no outside hand);
   heat at a distance auto-snaps into the cold, "cresting
   that electrical spark and resulting magnetic fields and
   resulting matter."

## CHARTER — NO CLAIM

This line is aimed at the continuum reading (its direction
and target), and graded at the finite level only. Per
Zero's own register (2026-11-24): a completed finite
theorem is not a continuum theorem. Tier: T5 charter,
NO CLAIM; dials unmoved (0/4) unless a proved theorem
closes part of a pre-registered statement. QTFT/QTST
remain candidate names, not worn by this line. No gravity
object is constructed, fed, or identified.

## The official statements (pinned verbatim at this brick)

**GEOMETRY FORCED: the seat's geometry (its
identity-face/balance-locus structure) is determined by
its thermal-dynamical data (dynamics over thermal
entropy).**

**CYCLE CLOSES: snap + decay returns the seat to a
balanced state — the finite shadow of the cycle.**

Registered below as `cycleGeometryForced` and
`cycleCloses`, in statement form only. Nothing about
either is claimed in this brick: Brick 1+ takes the first
forcing/cycle lemmas on the smallest seats — or the kills.

## Registration decisions (frozen on the face at this brick)

- **Parent dialects REUSED, not reinvented.** The seat is
  a finite weighted seat in the NED Pin's dialect
  (`ThetLogos.NegativeDensityPin`): microstates `Ω` a
  `Fintype`, integer charges `q : Ω → ℤ`, configurations
  weight functions `p : Ω → ℝ`; the entropy and charge
  functionals are the NED line's own (`nedEntropy`,
  `nedCharge`, `nedZeroCharge`), untouched. The pair
  enters in the Pair Primitive Pin's dialect
  (`ThetLogos.PairPrimitivePin`): the seat carries an
  exchange `exch`, the pair's generation face at seat
  level (cf. `pairGen`), and a condensed configuration is
  one the exchange fixes — the identity face, cf.
  `pairIdentity` (`gen p = p`). Lane bookkeeping, stated
  openly: this lane is based on the NED lane tip and
  carries `PairPrimitivePin.lean` transplanted
  byte-identical from the pair lane tip `d484dbc`
  (sha256-verified against its committed blob); the
  module itself is the parents' work, unmodified.
- **The seat's two components.** A cycle seat
  distinguishes a **distant component** `distant : Finset
  Ω`; the pair's two faces at seat level are `distant`
  and its complement. "At a distance" is registered as
  disjoint support: distant heat is a configuration
  supported on `distant` alone.
- **FORCED ADJUSTMENT — maximality is registered over
  normalised configurations, stated here, not silent.**
  The scope names the balanced state "maximal entropy,
  zero net charge." Taken over ALL weight functions, that
  locus is empty by the NED line's own proved verdict
  (`NegativeDensityFinOne`, `NegativeDensityKill`: over
  all weight functions the entropy has no maximum on any
  seat — the fact K-NED fired on). Registering it that
  way would pin a vacuity. The smallest adjustment that
  keeps the balanced state the seeing names: maximality
  over the **normalised** (total weight 1) zero-charge
  configurations — the restriction the NED face itself
  names as the stated-change route, adopted here as this
  line's founding registration. The NED functionals are
  NOT re-aimed; only the comparison class of this line's
  balanced predicate is fixed, on the face.
- **`exch` is bare seat data at this brick.** That it
  exchanges the two components, and is an involution, is
  its registered reading (docstrings), not a proved or
  assumed property here — later bricks state such
  properties as hypotheses or lemmas, as the parents do
  (cf. NED Brick 0 registering `nedGibbsDist` without
  claiming its normaliser is nonzero).
- **Decay is registered as bare return.** `cycleCloses`
  asks for a return to a balanced configuration that
  STANDS (is fixed by the exchange). No decay operator
  is registered at this brick; adding one is a later
  brick's stated change, never a silent one.

## Kills pre-registered (quoted verbatim from the scope; armed by this registration, not fired by it)

- **K-FORCE-GEOM**: two distinct geometries on one finite
  seat carrying identical thermal-dynamical data — the
  forcing dies.
- **K-SNAP-ORDER**: a snap on a finite seat whose forced
  stage order differs from E → M → C, or which skips a
  stage — the cycle's order dies.
- **K-CYCLE-OPEN**: a finite seat whose snap-and-decay
  does not return to any balanced state — the cycle does
  not close at the finite level.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- The pin tests a *shadow* of the seeings, not the
  seeings (L2/L3 discipline): a finite forcing or cycle
  theorem neither establishes the continuum reading nor
  a continuum claim.

## Brick 0's charge

Definitions and the pinned statements ONLY: 0 strict by
design. Names frozen at this brick: `CycleSeat`,
`cycleChargeOn`, `cycleBalanced`, `cycleDistantHeat`,
`cycleChargeSplit`, `cycleRingMotion`, `cycleCondensed`,
`CycleSnap`, `cycleGeometryForced`, `cycleCloses`.
-/

namespace ThetLogos

/-- **The cycle seat data.** Over a finite seat of
microstates `Ω`: an integer charge assignment
`charge : Ω → ℤ` (the NED dialect), a distinguished
**distant component** `distant : Finset Ω` — the pair's
two faces at seat level are `distant` and its complement
— and an **exchange** `exch : Ω → Ω`, the pair's
generation face at seat level (cf. `pairGen`): the motion
that exchanges the two components. Registered as bare
data: that `exch` exchanges the components and is an
involution is its reading, stated here; proving or
assuming it is later bricks' work, never this def's
silent content. -/
structure CycleSeat (Ω : Type*) where
  /-- The seat's integer charge assignment (NED dialect). -/
  charge : Ω → ℤ
  /-- The distant component: one face of the pair at seat level. -/
  distant : Finset Ω
  /-- The exchange: the generation face at seat level. -/
  exch : Ω → Ω

/-- **The static charge carried on one component.** The
NED charge functional (`nedCharge`) restricted to a
component `A`: `∑ i ∈ A, p i * (charge i)`. The whole
seat's charge is the case `A = univ`; the two components'
charges are the cases `A = distant` and
`A = distantᶜ` — the quantities the snap's first stage
splits across the pair. -/
noncomputable def cycleChargeOn {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (A : Finset Ω) (p : Ω → ℝ) : ℝ :=
  ∑ i ∈ A, p i * (S.charge i : ℝ)

/-- **The balanced state — the void seat.** A
configuration is balanced when it is normalised (total
weight 1), carries **zero net charge** across the pair
(`nedZeroCharge`, the NED locus), and has **maximal
entropy** (`nedEntropy`) among the normalised zero-charge
configurations. Maximality is registered over the
normalised class — the forced adjustment stated on the
face: over all weight functions entropy has no maximum
(the NED line's proved verdict), so the all-weights
reading would register this locus empty by construction. -/
def cycleBalanced {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (p : Ω → ℝ) : Prop :=
  (∑ i, p i) = 1 ∧ nedZeroCharge S.charge p ∧
    ∀ r : Ω → ℝ, (∑ i, r i) = 1 → nedZeroCharge S.charge r →
      nedEntropy r ≤ nedEntropy p

/-- **Distant heat: the imbalance datum.** A
configuration held **at a distance** from the balanced
seat: supported on the distant component alone (it
vanishes off `distant` — disjoint support is the finite
form of "at a distance") and carrying nonzero static
charge — an imbalance, not a balanced configuration.
This is the heat that, in the seeing, auto-snaps into
the cold. -/
def cycleDistantHeat {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (p : Ω → ℝ) : Prop :=
  (∀ i : Ω, i ∉ S.distant → p i = 0) ∧
    ¬ nedZeroCharge S.charge p

/-- **Snap stage E — the charge split across the pair.**
The spark crests: the configuration's charge is split
across the seat's two components — the distant
component's charge is nonzero, and the two components'
charges cancel across the pair (their sum is zero). The
first of the snap's three stages, in the scope's fixed
order E → M → C. -/
def cycleChargeSplit {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) (p : Ω → ℝ) : Prop :=
  cycleChargeOn S S.distant p ≠ 0 ∧
    cycleChargeOn S S.distant p + cycleChargeOn S S.distantᶜ p = 0

/-- **Snap stage M — the ring motion, as a relation.**
The magnetic stage: the second configuration is the
first carried by the exchange — the pair's generation
face acting on configurations, `p' = p ∘ exch`. The ring
in motion (cf. the E/M/G filing: M = the ring in motion),
registered as the transport relation between the snap's
first two stages. -/
def cycleRingMotion {Ω : Type*} (S : CycleSeat Ω)
    (p p' : Ω → ℝ) : Prop :=
  p' = fun i => p (S.exch i)

/-- **Snap stage C — condensation, the identity face.**
The matter seat: `p'` is the condensation of `p` when it
**stands** — it is fixed by the exchange,
`p' ∘ exch = p'`, the identity face for configurations
(cf. `pairIdentity`: `gen p = p`) — and it carries the
motion stage's charge undiminished (condensed, not
annihilated): `nedCharge p' = nedCharge p`. The third of
the snap's stages, in the fixed order E → M → C. -/
def cycleCondensed {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) (p p' : Ω → ℝ) : Prop :=
  (fun i => p' (S.exch i)) = p' ∧
    nedCharge S.charge p' = nedCharge S.charge p

/-- **A snap on a cycle seat: the three stages, in fixed
order.** One bundle carrying the stage configurations
`stageE`, `stageM`, `stageC` with their stage properties
in the scope's fixed order: `split` (E: the charge split
across the pair), `motion` (M: `stageM` is `stageE`
carried by the exchange), `condenses` (C: `stageC` is
the condensation of `stageM`). The order is structural —
the fields are the stages, in order — and K-SNAP-ORDER
is the kill that tests whether any snap on a finite seat
is forced through them in this order, skipping none. -/
structure CycleSnap {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) where
  /-- Stage E configuration: the charge split. -/
  stageE : Ω → ℝ
  /-- Stage M configuration: the ring motion. -/
  stageM : Ω → ℝ
  /-- Stage C configuration: the condensation. -/
  stageC : Ω → ℝ
  /-- E: `stageE`'s charge is split across the pair. -/
  split : cycleChargeSplit S stageE
  /-- M: `stageM` is `stageE` carried by the exchange. -/
  motion : cycleRingMotion S stageE stageM
  /-- C: `stageC` is the condensation of `stageM`. -/
  condenses : cycleCondensed S stageM stageC

/-- **THE FIRST OFFICIAL STATEMENT, pinned as the line's
target — GEOMETRY FORCED.** The seat's geometry is
determined by its thermal-dynamical data: any two cycle
seats `S`, `S'` over the same `Ω` whose thermal-dynamical
data agree — the same static charge on every
configuration, and the same static charge on every
configuration carried by the motion (the dynamics read
through the thermal functionals) — have the same
geometry: the same standing configurations, i.e. the
same condensation (identity-face) locus. (The balance
locus is fixed by the charge data alone, through
`cycleBalanced`; the statement's teeth are in the
identity face, which the charge data do not wear on
their face.) Stated in statement form only; nothing
about it is claimed in this brick. Brick 1+'s charge is
the theorem — or K-FORCE-GEOM, each a landing at the same
volume. -/
def cycleGeometryForced {Ω : Type*} [Fintype Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ S' : CycleSeat Ω,
    (∀ p : Ω → ℝ,
      nedCharge S'.charge p = nedCharge S.charge p ∧
        nedCharge S'.charge (fun i => p (S'.exch i)) =
          nedCharge S.charge (fun i => p (S.exch i))) →
    ∀ p : Ω → ℝ,
      (fun i => p (S'.exch i)) = p ↔ (fun i => p (S.exch i)) = p

/-- **THE SECOND OFFICIAL STATEMENT, pinned as the line's
target — CYCLE CLOSES.** Snap + decay returns the seat
to a balanced state: for every snap on the seat there is
a configuration that is **balanced** (`cycleBalanced` —
the void seat: maximal entropy, zero net charge) and
**standing** (fixed by the exchange — the return lands
on the identity face). Decay is registered as bare
return at this brick, as the header states: no decay
operator is pinned here, and strengthening this
registration is a later brick's stated change. (The
return condition is registered at seat level — the snap
quantification is the statement's form; tying the return
to the snap's own endpoint is exactly the strengthening
a decay operator would make, and it is left to the
brick that registers one.) Stated in statement form
only; nothing about it is claimed in this brick.
Brick 1+'s charge is the theorem — or K-CYCLE-OPEN, each
a landing at the same volume. -/
def cycleCloses {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) : Prop :=
  ∀ _snap : CycleSnap S, ∃ p : Ω → ℝ,
    cycleBalanced S p ∧ (fun i => p (S.exch i)) = p

end ThetLogos
