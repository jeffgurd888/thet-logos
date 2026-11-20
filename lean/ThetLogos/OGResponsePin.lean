import Mathlib.Tactic
import ThetLogos.OGPin
import ThetLogos.BoundarySeat

namespace ThetLogos

/-!
# ThetLogos.OGResponsePin — OG-RL-0, the extension pin (0 strict, by design)

**Commission:** Zero, 2026-11-17 09:21 EST ("aim the bench"), on the
scoping `og-response-law-scope-2026-11-17.md`. The scoping's verdict:
over `OGDatum` as pinned, NO test-body response law is stateable
(the declared unity form has no body sector, and a response law is a
law about a body); over a datum EXTENDED by declared additions,
exactly one derived-law shape is stateable — the RL-P1 form (C-4).
This pin freezes that extension and its target forms. The content
bricks OG-RL-1..3 prove against these forms or report the failure.

## The four design rulings (Zero's, 2026-11-17 09:41–09:47 EST — frozen)

The pin's frozen forms ARE these rulings; they were made one at a
time, in this order:

1. **EXTENSION** (09:44 EST): "Extend the datum — add the body
   sector." A NEW datum extending `OGDatum` with a body sector.
   The pinned `OGDatum` in `OGPin.lean` is NOT edited —
   K-OG-RL-AMEND is armed over any quiet edit of it.
2. **SOURCE** (09:45 EST, corrected by Zero himself 09:46 EST):
   the source is **ρ, a mass-density field**. (Zero's first tap
   chose teCharge; he corrected it a minute later to mass
   density. The standing ruling is ρ.)
3. **CHANNEL** (09:47 EST): **GROUNDED** — the body sits at a
   `BoundarySeat` site; the potential is UA-2's landed
   `groundedPotential` (total-mass sensitive). The potential does
   NOT route through the closed Poisson channel —
   K-OG-RL-SHADOW: that channel is total-mass blind by landed
   theorem (`PoissonTotalMassBlindness`, CT-1).
4. **KINETIC KERNEL** (09:47 EST): the seat's own `w`. No imported
   kinetic term, no new constant (D2-5).

## Face declarations (read before anything below)

- **This module is a PIN.** Definitions and frozen statement forms
  only: **no theorems, no axioms, no proofs.** 0 strict, BY DESIGN.
- **PRE-REGISTERED DIAL-INELIGIBLE.** NO CLAIM. Dial 2 = 0 before
  this pin, 0 after it, and 0 under every outcome of OG-RL-1..3.
  A landing on this line is exhibit-grade mathematics about a
  declared datum; Dial 2 moves only on a later P-D2 audit pass,
  which no brick on this line performs or promises. A full landing
  would grade at most PASS-N, in variational form only.
- **The extension is Register-A declared design**, in the same
  bucket as the Gate B declaration it extends ("gravity's
  primitive is unity", Zero, 2026-11-08 18:02 EST). It is NOT a
  Lean `axiom`, and nothing here can be cited as a hypothesis by
  any proof. A declaration is design, not a result.
- **The law, if it lands, is a law of the EXTENDED datum, never
  of OG-as-pinned** (K-OG-RL-SCOPE). The amended object carries
  its own name and fences. OG-as-pinned has no test body and
  therefore no response law; that scoped kill stands untouched
  by anything on this line.
- **Predeclared scope (D2-0):** Newtonian-regime fragment, finite
  seat, ONE body in a FIXED background, NO back-reaction. This
  scope is stated here so it cannot be upgraded after the fact.

## Pin-level completion of the scope's elided hypotheses (on the face)

The scoping's pseudocode writes `groundedPotential w b ρ` with the
hypotheses suppressed. The landed form (UA-2) requires symmetry
(`hw`), nonnegativity (`hw0`) — both carried by `OGDatum` — and
**complete positivity** (`hpos : ∀ i j, i ≠ j → 0 < w i j`), which
`OGDatum` does NOT carry. The extended datum therefore carries
`w_pos` as a field. This is a completion of the ruled channel's
landed requirements, not a change of shape: the potential is the
landed grounded inversion of the seat's own `w`, or there is no
potential. Recorded here so no reader has to discover it in the
proof terms.

## The frozen objects

- **`OGResponseDatum`** — the extended datum: an `OGDatum` plus
  (A) the source field `ρ` (mass density, background side),
  (B) the grounded site `b`, and the positivity field `w_pos`.
- **`OGBody`** — the body sector: a mass `m > 0`. A body path is
  `x : Fin (n+1) → V`, positions on the seat over discrete steps.
- **`seatKinetic`** — the kinetic kernel, a definition from `w`
  alone: `seatKinetic w i j := w i j` (Ruling 4; D2-1's soft spot,
  frozen here in the pin, not chosen per-result — D2-0).
- **`ogPotential`** — the grounded potential of the datum's own
  source: `groundedPotential D.w … D.b D.ρ` (Ruling 3).
- **`ogAction`** — the frozen path action:
  `Σ_steps m·seatKinetic − Σ_sites m·φ`. The mass multiplies BOTH
  sums as a single scalar factor; that is what makes its
  cancellation in the stationarity condition a THEOREM that could
  fail (OG-RL-2), not a definition (K-OG-RL-UNIV). The action has
  NO free constant (D2-5).
- **`ogStationary`** — THE RESPONSE LAW's predicate, derived not
  stipulated: `x` is stationary when every single-site variation
  of an interior path point fails to lower the action. Endpoints
  are fixed (the variational principle's own shape).
- **The second channel (countermodel apparatus)** —
  `ogChargePotential` (the grounded potential of a second field
  `σ`), `ogChargedAction` (the action plus a charge coupling
  `− Σ q·ψ` — note the charge term carries NO mass factor, which
  is exactly what lets it break the scaling), and
  `ogChargedStationary`. This apparatus exists so that
  universality's non-vacuity is a theorem-shape (D2-6, CT-8
  answered with content), not a construction: if the countermodel
  fails to break universality, K-OG-RL-SECOND fires and OG-RL-2
  does not ship as evidence of anything.

## The frozen forms (OG-RL-1..3 targets; names frozen here)

- **EL form — `OGResponseELForm`** (OG-RL-1): stationarity of a
  path is EXACTLY the explicit variational inequality of
  `ogSiteBalance` at every interior site — the Euler–Lagrange
  form of the law, an iff, derived in both directions.
- **Universality form — `OGResponseUniversalityForm`** (OG-RL-2):
  the stationary path set is independent of the body's mass —
  any two bodies (an `OGBody` carries nothing but its mass, so
  any two bodies differ ONLY in mass) have the same stationary
  paths. A theorem, never a hypothesis or a definition
  (K-OG-RL-UNIV).
- **Countermodel form — `OGResponseCountermodelForm`** (OG-RL-2):
  at some datum, second field, step count, there are one body,
  two distinct charges, and one path stationary under the first
  charge and not under the second — universality provably FAILS
  once a second channel couples, so its holding for mass alone
  is content (D2-6).
- **Shadow form — `OGResponseShadowForm`** (OG-RL-3): over the
  extended datum ITSELF (not bare functions): under a nonnegative
  source with some positive mass off the ground, stationary
  paths EXIST for every body and every step count — the law has
  instances over the datum (the datum-level assembly; the named
  seat's potential computation and attraction content ride on
  the EL form in OG-RL-3). K-OG-RL-VAC arms over vacuity in
  either direction at a named seat.

## The kill registry (K-OG-RL-*, pre-registered in the scoping §4)

- **K-OG-RL-AMEND** — any brick edits `OGPin`'s `OGDatum`, or
  presents the extended datum as OG-as-pinned: the line stops.
- **K-OG-RL-SHADOW** — the potential routed through the CLOSED
  Poisson channel: total-mass blind by landed theorem. The
  grounded channel or no channel.
- **K-OG-RL-UNIV** — universality entering any brick as a
  hypothesis, a field condition, or a definition.
- **K-OG-RL-SECOND** — OG-RL-2's countermodel FAILS to break
  universality: the universality theorem was vacuous (CT-8).
- **K-OG-RL-VAC** — stationarity vacuous at a named seat in
  either direction (every path stationary, or none) where
  OG-RL-1 claims content.
- **K-OG-RL-SIGN** — the attraction direction fixed by a sign
  choice in the source map, the kernel, or the action, rather
  than derived from `laplacianOp`'s landed conventions
  (`laplacianOp w F i = Σ j, w i j * (F i − F j)`,
  `BridgeLaplacian`) and the grounded inversion.
- **K-OG-RL-STRIP** — at audit, the stripped action + EL law
  cannot be named, prose excluded, as the finite Newtonian
  shadow (discrete Poisson + variational Euler–Lagrange):
  D2-2 falls.
- **K-OG-RL-SCOPE** — any text presenting an OG-RL landing as a
  response law OF OG-as-pinned, a gravity object, Dial
  evidence, or progress past the predeclared fragment scope.

The standing K-OG registry (OGPin face) applies in full:
K-OG-SUM (fired), K-OG-SHADOW, K-OG-TOLMAN, K-OG-SQUEEZE,
K-OG-PROXY, K-OG-FIAT, K-OG-VAC, K-OG-DIAL.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **The extended datum — PINNED FORM (Register A, declared
design; Rulings 1–3).**

An `OGDatum` — carried whole, unedited (K-OG-RL-AMEND) —
extended by three declared additions: the source field `ρ`
(a mass-density datum, background side; Ruling 2), the grounded
site `b` (the Gate-A channel's Dirichlet pin; Ruling 3), and the
complete-positivity field `w_pos` (the landed grounded
inversion's own requirement; see the header's completion note).
An inhabitant is a *choice* of seat data; the structure asserts
nothing about any physical system. NO CLAIM; dial-ineligible;
Dial 2 = 0. -/
structure OGResponseDatum (V : Type*) [Fintype V] [DecidableEq V]
    [Nonempty V] extends OGDatum V where
  /-- (A) The source field: mass density on the seat. -/
  ρ : V → ℝ
  /-- (B) The grounded site: the potential is pinned to `0` here. -/
  b : V
  /-- Complete positivity of the seat's own weights — the landed
  grounded inversion (`BoundarySeat.exists_groundedPotential`)
  requires it. Off-diagonal only; the diagonal is `OGDatum`'s. -/
  w_pos : ∀ i j, i ≠ j → 0 < w i j

/-- **The body sector — PINNED FORM (Ruling 1).** A test body is
its mass, positive. (C) of the scoping: the body sector the
pinned unity form deliberately does not have, added here by
declared extension — beside `OGDatum`, never inside it. A body
path is `x : Fin (n+1) → V` over discrete steps. The body
carries NO non-mass parameter in the uncharged law; that is what
gives the universality form (OG-RL-2) its CT-8 question, and the
charged apparatus below its answer. -/
structure OGBody (V : Type*) where
  /-- The body's mass. -/
  m : ℝ
  /-- The mass is positive. Positivity is load-bearing: the
  universality theorem is the cancellation of this factor, and
  at `m ≤ 0` the stationarity condition flips or degenerates. -/
  hm : 0 < m

/-- **The kinetic kernel — PINNED (Ruling 4).** A definition
from the seat's own weights `w` alone, no new constant (D2-5):
the kernel of a step is the seat's own weight of that step.
Frozen in this pin (D2-0/D2-1): it is not chosen per-result,
and no brick may retune it after seeing the EL output. -/
def seatKinetic (w : V → V → ℝ) (i j : V) : ℝ :=
  w i j

/-- **The datum's potential — PINNED (Ruling 3).** The landed
grounded inversion of the datum's own source field on the
datum's own weights, pinned at the datum's ground:
`groundedPotential w hw hw0 hpos b ρ` (UA-2, `BoundarySeat`).
Total-mass sensitive by landed theorem
(`groundedPotential_add_const_ne`) — the exact negation of the
closed seat's blindness. NOT routed through the closed Poisson
channel (K-OG-RL-SHADOW). -/
noncomputable def ogPotential (D : OGResponseDatum V) : V → ℝ :=
  groundedPotential D.w D.w_symm D.w_nonneg D.w_pos D.b D.ρ

/-- **The second channel's potential — PINNED (countermodel
apparatus).** The grounded potential of a second field `σ` on
the same seat, same ground. Used only by the charged action
below: the countermodel's second potential. It is the same
landed inversion — no new channel is invented for the
countermodel. -/
noncomputable def ogChargePotential (D : OGResponseDatum V)
    (σ : V → ℝ) : V → ℝ :=
  groundedPotential D.w D.w_symm D.w_nonneg D.w_pos D.b σ

/-- **The path action — FROZEN (scoping C-4; D2-0, D2-5).**

`ogAction D B n x = Σ_{k : Fin n} m·seatKinetic w (x k) (x (k+1))
− Σ_{k : Fin (n+1)} m·φ (x k)`, where `φ = ogPotential D`.

The mass `m` is a single scalar factor multiplying BOTH sums:
its cancellation in the stationarity condition is the
universality THEOREM of OG-RL-2, which could fail — and does
fail once the charged term below is added (the countermodel).
There is no free constant anywhere in this action: φ's scale is
fixed by the grounded inversion of ρ (D2-5). The sign of the
potential term is part of this frozen form (kinetic − potential,
the action shape whose rent UA-3 paid); no brick may re-choose
it per-result (K-OG-RL-SIGN arms over any further sign fixing —
the attraction direction must be DERIVED from `laplacianOp`'s
conventions and this form, never adjusted). -/
noncomputable def ogAction (D : OGResponseDatum V) (B : OGBody V)
    (n : ℕ) (x : Fin (n + 1) → V) : ℝ :=
  (∑ k : Fin n, B.m * seatKinetic D.w (x k.castSucc) (x k.succ)) -
    (∑ k : Fin (n + 1), B.m * ogPotential D (x k))

/-- **Stationarity — the response law's predicate, PINNED.**

`x` is stationary when NO single-site variation of an interior
path point lowers the action: for every interior `k`
(`0 < k.val < n` — endpoints are fixed) and every site `y`,
`ogAction (x with k ↦ y) ≥ ogAction x`. The response (the
stationary path set) is an OUTPUT of this predicate, derived
from the action — never an input, a placement, or a renaming
(the C-3 disease, refused by the standing precedent). Whether
this predicate has instances, and whether it bites, is
theorem-content for OG-RL-1/3 (K-OG-RL-VAC). -/
def ogStationary (D : OGResponseDatum V) (B : OGBody V) (n : ℕ)
    (x : Fin (n + 1) → V) : Prop :=
  ∀ (k : Fin (n + 1)), 0 < k.val → k.val < n → ∀ y : V,
    ogAction D B n (Function.update x k y) ≥ ogAction D B n x

/-- **The site balance — PINNED (the EL form's local quantity).**
At an interior site `k` of a path `x`, the part of the action
that a variation at `k` can move, evaluated at a candidate site
`y`: the two kinetic steps touching `k`, minus the potential at
`y`, all under the body's mass factor. The EL form (below)
states that stationarity is exactly the pointwise minimality
of this balance at the path's own sites — `y ↦ balance y` is
minimized at `y = x k`: a variation moves the action by
`balance y − balance (x k)`, and stationarity (no variation
lowers the action) is exactly that difference being
nonnegative for every `y`. -/
noncomputable def ogSiteBalance (D : OGResponseDatum V)
    (B : OGBody V) (n : ℕ) (x : Fin (n + 1) → V) (k : Fin (n + 1))
    (hk : 0 < k.val ∧ k.val < n) (y : V) : ℝ :=
  B.m * (seatKinetic D.w (x ⟨k.val - 1, by omega⟩) y +
      seatKinetic D.w y (x ⟨k.val + 1, by omega⟩)) -
    B.m * ogPotential D y

/-- **FROZEN FORM — the EL form (OG-RL-1's target).** Stationarity
of `x` is EXACTLY the site-balance minimality at every interior
site: for every interior `k` and every site `y`, the balance at
the path's own `x k` does not exceed the balance at `y`. An iff,
in variational form — on a general graph the law is
path-optimality, not an acceleration vector (the acceleration
FORM exists only on coordinate seats; D2-4's residual risk,
predeclared). OG-RL-1 proves a theorem of this type or reports
the failure.

REPAIR NOTE (disclosed, lane grade): as first banked (commit
843ccb0) this form carried the inequality flipped — balance
maximality — a drafting error in this pin, caught by OG-RL-1a's
first build (`og_el_form` unprovable in both directions). The
scope froze the action (`K − P`) and stationarity (no variation
lowers the action); the EL direction is forced by those two —
`A(update) − A(x) = balance y − balance (x k) ≥ 0` — and is
minimality. No content had been proved against the flipped
form; the action, stationarity, kernel, source, channel, and
all four rulings are unchanged. -/
def OGResponseELForm (D : OGResponseDatum V) (B : OGBody V)
    (n : ℕ) (x : Fin (n + 1) → V) : Prop :=
  ogStationary D B n x ↔
    ∀ (k : Fin (n + 1)) (hk : 0 < k.val ∧ k.val < n) (y : V),
      ogSiteBalance D B n x k hk (x k) ≤
        ogSiteBalance D B n x k hk y

/-- **FROZEN FORM — universality (OG-RL-2's target).** The
stationary path set does not depend on the body's mass: for any
two bodies — which, an `OGBody` carrying nothing but mass,
differ ONLY in mass — stationarity of a path under one is
stationarity under the other, both directions. This form is a
THEOREM-target: it may not enter any brick as a hypothesis, a
field condition, or a definition (K-OG-RL-UNIV). -/
def OGResponseUniversalityForm (D : OGResponseDatum V) (n : ℕ)
    (x : Fin (n + 1) → V) : Prop :=
  ∀ B₁ B₂ : OGBody V, ogStationary D B₁ n x ↔ ogStationary D B₂ n x

/-- **The charged action — PINNED (countermodel apparatus).** The
frozen action plus a second-channel coupling: a charge `q`
coupled to the second potential `ψ = ogChargePotential D σ`,
entering as `− Σ q·ψ (x k)` — with NO mass factor. That absence
is the point: the charged action is not a positive scalar
multiple of a body-independent action, so its stationarity can
depend on the body's parameters — the failure mode that makes
the universality theorem non-vacuous (D2-6). -/
noncomputable def ogChargedAction (D : OGResponseDatum V)
    (B : OGBody V) (q : ℝ) (σ : V → ℝ) (n : ℕ)
    (x : Fin (n + 1) → V) : ℝ :=
  ogAction D B n x -
    (∑ k : Fin (n + 1), q * ogChargePotential D σ (x k))

/-- **Charged stationarity — PINNED (countermodel apparatus).**
Stationarity of a path under the charged action: no single-site
interior variation lowers `ogChargedAction`. -/
def ogChargedStationary (D : OGResponseDatum V) (B : OGBody V)
    (q : ℝ) (σ : V → ℝ) (n : ℕ) (x : Fin (n + 1) → V) : Prop :=
  ∀ (k : Fin (n + 1)), 0 < k.val → k.val < n → ∀ y : V,
    ogChargedAction D B q σ n (Function.update x k y) ≥
      ogChargedAction D B q σ n x

/-- **FROZEN FORM — the countermodel (OG-RL-2's target).** There
exist a second field, a step count, ONE body, two DISTINCT
charges, and a path that is charged-stationary under the first
charge and NOT under the second: with everything else held
fixed — same datum, same body, same mass, same path — the
response changes when the second channel's coupling changes.
That is what answers CT-8 with content: the body sector CAN
express composition, so mass-independence is a theorem with a
failure mode, not a vacuity. If no such witness exists,
K-OG-RL-SECOND fires. -/
def OGResponseCountermodelForm (D : OGResponseDatum V)
    (σ : V → ℝ) (n : ℕ) : Prop :=
  ∃ (B : OGBody V) (q₁ q₂ : ℝ) (x : Fin (n + 1) → V),
    q₁ ≠ q₂ ∧ ogChargedStationary D B q₁ σ n x ∧
      ¬ ogChargedStationary D B q₂ σ n x

/-- **FROZEN FORM — the shadow form (OG-RL-3's target).** Over
the extended datum ITSELF: under a nonnegative source with some
positive mass off the ground, for every body and every step
count, a stationary path EXISTS — the law has instances over
the datum, at datum level, not only over bare functions (the
datum-level assembly of the scoping's Brick 3). The named
seat's potential computation and the attraction content ride
on the EL form; this form is the existence half, and
K-OG-RL-VAC arms over its failure at a named seat. -/
def OGResponseShadowForm (D : OGResponseDatum V) : Prop :=
  (∀ i, 0 ≤ D.ρ i) → (∃ i, i ≠ D.b ∧ 0 < D.ρ i) →
    ∀ (B : OGBody V) (n : ℕ), ∃ x : Fin (n + 1) → V,
      ogStationary D B n x

end ThetLogos
