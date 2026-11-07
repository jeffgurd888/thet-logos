import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ThetLogos.SolidBody

/-!
# ThetLogos.SolidBodyActionPin — UA-3 PIN (interface only, 0 strict)

**UA-3 — the SolidBody action-rent brick.** Commissioned by Jeff
2026-11-06 23:33 EST ("fire both" = UA-2 + UA-3). Spec:
`gravity-untried-angles-scoping-2026-11-06.md` §UA-3 — priced M,
~12–22 strict, pre-registered DIAL-INELIGIBLE. The scoping's rent
form governs: *stationarity of the action implies the trajectory
satisfies the Euler field equation the module currently assumes as
T4 — or the exact statement the action actually supports, graded on
the face.*

## Why this brick exists

`ThetLogos.SolidBody` takes Euler's rigid-body equations as a **T4
hypothesis**: every conservation theorem there assumes "ω obeys the
Euler field" (`∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i`,
with `Differentiable` coordinates) and proves conservation from it.
Nothing in that module derives the field from anything. This brick
asks whether the seat can pay *rent*: a path-action, built from the
body's own data alone, whose **stationarity derives the Euler
trajectories** — independent motivation, in a gravity-free house,
for the path-action primitive (RL-P1 Gate B, response-law scoping
2026-11-05 §7). The primitive declaration itself stays Jeff's hand
regardless of this brick's outcome. This brick touches no dial.

## The action (frozen)

The seat's variables are the angular velocities themselves
(`ω : ℝ → Fin 3 → ℝ`, continuous time — the module's own trajectory
form; the module carries no frame variables). The action is the
plain kinetic action of the path, in the module's own landed
vocabulary:

  `sbAction b T ω = ∫ t in 0..T, rotEnergy b (ω t)`

— the time-integral of `rotEnergy`, the rotational kinetic energy,
a definition from the moments alone. **No definition in this pin
mentions `eulerRHS`.**

## The variation class (frozen) — and why it is this one

A free rigid body's configuration is its frame; varying the frame
by an infinitesimal rotation field `ξ : ℝ → Fin 3 → ℝ` induces on
the body angular velocity the **adjoint variation**

  `δω = ξ' + ω × ξ`   (`sbFrameVar`),

the classical Euler–Poincaré variation. Stationarity
(`sbStationary`) is the vanishing of the first variation of
`sbAction` under every such frame variation with `ξ` vanishing at
both endpoints of `[0, T]`. This variation class is part of the
seat's own geometry (the frame is what a rigid body *is*); it is
stated here from cross products and derivatives alone, with no
mention of the Euler field. Variations of ω in arbitrary
independent directions are *not* the seat's variations — a point
recorded honestly: on ω-paths with unconstrained variations, no
action of kinetic type has Euler trajectories as its stationary
paths (see the design record below).

## The rent statement (frozen target)

`sb_stationary_iff_euler` (content module): for a `C¹` trajectory
`ω` (the module's own hypothesis shape: differentiable coordinates),

  `sbStationary b ω ↔ ∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i`

— stationarity **is** the module's T4 hypothesis, derived, in both
directions. Note the stationarity predicate quantifies over *every*
window `[a, b]`: an action principle is a property of the
trajectory, not of one chosen window (with a single fixed window,
stationarity could only see that window, and the `∀ t` form would
be false outside it — the all-windows form is the honest
predicate, and it is the one frozen). The engine is one exact identity (machine-checked in
sympy this run, to be proved in Lean): with `L = angMom`,

  `Σᵢ Lᵢ·(ξ'ᵢ + (ω × ξ)ᵢ) = (Σᵢ Lᵢξᵢ)' + Σᵢ ξᵢ·(−Iᵢ·(ω'ᵢ − eulerRHSᵢ))`

so the first variation is a boundary term (killed by
`ξ(0) = ξ(T) = 0`) plus `∫ ξ · (−I(ω' − eulerRHS))`; the forward
direction is then the fundamental lemma (a continuous field whose
integral against every endpoint-vanishing `ξ` is zero vanishes —
proved by the standard bump argument), and `Iᵢ > 0` divides out.
The reverse direction is the identity read backwards. Corollary:
every stationary trajectory inherits the module's landed
conservation theorems with the T4 hypothesis *derived*, not assumed.

## Design record (at full rank — two designs died before this one)

1. **Discrete Douglas-type action on ω-paths** (first in-lane pin
   commit): symbolic analysis showed its stationarity law is a
   quartic recursion, not the Euler field in any form; the whole
   symmetric pair-coupling family fails the constant-path test
   (a discrete Euler law must annihilate the stationarity defect
   on constant paths; the family's defect is a nonzero non-Euler
   expression). Additionally, no cubic potential has the
   `eulerRHS`-weighted field as its gradient (proved by linear
   algebra over the cubic monomial basis) — the Euler field is
   gyroscopic, not a gradient. Abandoned before proof work.
2. **Energy–Casimir / Lagrange-multiplier action**
   `∫(T(ω') − λ·C(ω))`: its Euler–Lagrange system is the decoupled
   oscillator `ω''ᵢ = −2λIᵢωᵢ`, verified symbolically and
   numerically to neither imply nor be implied by the Euler field
   (the multiplier frozen from the path makes it worse, not
   better). Abandoned.
3. **This pin** — the classical Euler–Poincaré principle at the
   seat's own variables, with the frame variation class made
   explicit as data. The derivation could have failed: the bulk
   coefficient is `−Iᵢ(ω'ᵢ − eulerRHSᵢ)` *exactly*, with no free
   parameter anywhere in the action or the variation class.

## Scope label, on its face

Fixed moments; `C¹` trajectories on a finite horizon `[0, T]`,
`T > 0`; the variation class is the frame (adjoint) class above —
that restriction is the seat's geometry, stated, not hidden. No
statement about physical bodies (the T4 input of `SolidBody` is
untouched), and no gravity content of any kind.

## Kills, pre-registered

* **K-UA3-FIAT** — if the only statable action whose stationarity
  yields the Euler field is the Euler field re-encoded term-by-term
  (no kinetic-energy form defined from the body's data alone), the
  brick lands as that finding: rent NOT EARNED. Checkable defence:
  the action is `∫ rotEnergy`; `eulerRHS` occurs in no definition
  of this line; the variation class is defined from the cross
  product alone.
* **K-UA3-SCOPE** — any use of a landed UA-3 as gravity evidence,
  or as discharging RL-P1's target (a) (ODP-RLP1-FRAME — different
  seat/realization), fires this kill.

## Frozen names (this pin)

`sbAction`, `sbFrameVar`, `sbFirstVar`, `sbStationary`. The content
module (`SolidBodyAction`) adds theorem names under the `sb`
prefix; it may not rename or re-define these.

**NO CLAIM; dials 0/4; Dial 2 = 0.** No gravity vocabulary anywhere
in this line.
-/

namespace ThetLogos

/-- The cross product on `Fin 3 → ℝ`, in coordinates. Used to state
the frame variation class; defined from coordinates alone. -/
def sbCross (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

/-- The kinetic path action of a trajectory `ω` over the horizon
`[0, T]`: the time-integral of the module's rotational kinetic
energy `rotEnergy` along the path. Built from the body's moments
alone; the Euler field is not mentioned. -/
noncomputable def sbAction (b : SolidBody) (T : ℝ) (ω : ℝ → Fin 3 → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, rotEnergy b (ω t)

/-- The frame (adjoint / Euler–Poincaré) variation of the angular
velocity path `ω` induced by the infinitesimal rotation field `ξ`:
`δω = ξ' + ω × ξ`, read pointwise. This is the variation class of
the seat: the variations a rigid body's angular velocity actually
admits when its frame is varied. -/
noncomputable def sbFrameVar (ω ξ : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun i => deriv (fun s => ξ s i) t + sbCross (ω t) (ξ t) i

/-- The first-variation integrand of the kinetic action at time
`t` under the frame variation induced by `ξ`: the pairing of the
angular momentum with the frame variation,
`Σᵢ (Iᵢ·ωᵢ t)·(δω)ᵢ t`. The first variation of `sbAction` along
the variation is the integral of this density. -/
noncomputable def sbFirstVar (b : SolidBody) (ω ξ : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∑ i, angMom b (ω t) i * sbFrameVar ω ξ t i

/-- Stationarity of the kinetic action at the trajectory `ω`:
on **every** window `[a, b]` (`a < b`), the first variation
vanishes for every frame variation field `ξ` with differentiable
coordinates vanishing at both endpoints. (Every window: an action
principle is a property of the trajectory; a single fixed window
would see only itself.) -/
def sbStationary (b : SolidBody) (ω : ℝ → Fin 3 → ℝ) : Prop :=
  ∀ a b' : ℝ, a < b' → ∀ ξ : ℝ → Fin 3 → ℝ,
    (∀ i, Differentiable ℝ (fun s => ξ s i)) →
    ξ a = 0 → ξ b' = 0 →
    ∫ t in a..b', sbFirstVar b ω ξ t = 0

/- REPAIR NOTE (parent-authorized, 2026-11-07): pin v4 as committed
(67a9213) never elaborated — in `sbStationary` the bound endpoint
`b : ℝ` captured the body parameter `b : SolidBody`, so `sbFirstVar b`
received a real number (variable capture). The repair is a pure
alpha-rename of that bound endpoint (`b` → `b'`, with its two uses);
the proposition denoted is the identical one the def's signature and
docstring always stated. No other binder, statement, or claim in this
pin is changed. -/

end ThetLogos
