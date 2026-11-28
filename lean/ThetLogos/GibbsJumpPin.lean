import Mathlib.Tactic

/-!
# ThetLogos.GibbsJumpPin — the Gibbs jump forecast, registered (Brick 0)

Working label only — naming is Zero's hand. Brick 0 of the
Gibbs Jump Pin; scope of record:
`~/workspace/your_files/gibbs-jump-pin-scope-DRAFT-2026-11-25.md`.
Fired under Zero's "run everything" of 2026-11-27.

Zero's seeing sequence, 2026-11-25 (verbatim fragments, in
order): "what if infinity ♾️ is limited to the adjointed
pairs quantum vertex"; "but it can't reach a single point
it must be a ring of balance or the eye of a hurricane 🌀
or tornado"; "it becomes a cloud of point origin of
balanced thermal entropy"; "just like a single point is a
proactive position of probability"; "I think that's why we
see the sub atomic jumping around"; and his question: "can
we forecast the jump from previous jump positions and
thermal entropy manipulation".

TIER: the finite statistics below are T1-or-kill; the
physical reading is T5, NO CLAIM about real particles under
every outcome. Dial-ineligible; Dial 2 stays 0.

## The honest verdict on the question (carried on the face)

- Forecast the individual jump from previous positions:
  NO — obstructed at theorem grade (Bell; loophole-free
  tests). Previous positions do not carry the next jump.
  That obstruction is this pin's fence, not its target.
- Forecast the statistics, and manipulate them thermally:
  YES — established stochastic thermodynamics (Kramers /
  Arrhenius rates, ratchets, entropy landscapes). You
  re-weight the cloud; you do not pick the point.

This pin is the finite, provable core of the YES half: a
finite seat of positions with Gibbs-weighted jumps, the
exact forecast matrix, and the manipulation stated as
theorems in later bricks. Statistics only: no statement in
this line predicts an individual jump, at this seat or any
other. No continuum limit, no particle claim.

## Registration decisions (frozen on the face at this brick)

- **The seat.** Three positions on a ring — the ring of
  balance from the seeing, at its smallest honest size:
  positions `Fin 3`, where each position's neighbours on
  the ring are the other two.
- **The landscape and temperature.** An energy landscape
  `E : Fin 3 → ℝ` and an inverse temperature `β : ℝ`
  (registered for all real `β`; the thermal reading is
  `β ≥ 0`, and Brick 1's theorems will say which side of
  that line they need, on their faces).
- **The jump weights — the exact form, frozen here.**
  Direct Gibbs form, Metropolis-free: from position `i`,
  the weight of jumping to `j` is `exp (-β * E j)` when
  `j ≠ i`, and `0` at `j = i` (a jump moves). The forecast
  matrix is the row-normalisation of the weights.
- **The Gibbs distribution, registered as a named object**
  (`gibbsDist`): the landscape's own Gibbs weights,
  normalised over the seat — Brick 1's charge includes
  proving it is the forecast's stationary distribution.
- **The forecast from a history** (`gibbsForecastFrom`):
  the forecast after a finite history of positions is the
  forecast matrix at the history's LAST position; from the
  empty history it is the Gibbs distribution itself (the
  registered prior). This definition is where the pin's
  honesty fence lives: the forecast is a function of the
  present position alone BY CONSTRUCTION here, and Brick 2
  states and proves that as the fence (K-JUMP-MEMORY) —
  the seat certifies that history-based forecasting buys
  nothing here, it does not merely fail to use history.

## The claims, pinned as statements (Brick 1 and 2's charges)

- `gibbsJumpForecastClaim` — the forecast is a forecast:
  its rows sum to `1`, and the Gibbs distribution is
  stationary for it. Brick 1's charge.
- `gibbsJumpMemoryFence` — the forecast from any two
  histories ending at the same present position is the
  same forecast. **K-JUMP-MEMORY, pre-registered:** at this
  seat the forecast provably does NOT depend on previous
  jump positions beyond the current one — the finite
  Markov property stated as the pin's honesty fence.
  Brick 2's charge, together with the manipulation
  theorems (the forecast's exact response to `β` and to
  the landscape).

## Brick 0's charge

Definitions and statement pins ONLY: 0 strict by design.
Names frozen at this brick: `gibbsJumpWeight`,
`gibbsJumpNorm`, `gibbsForecast`, `gibbsDist`,
`gibbsForecastFrom`, `gibbsJumpForecastClaim`,
`gibbsJumpMemoryFence`.
-/

namespace ThetLogos

/-- **The Gibbs jump weights.** From position `i`, the
weight of the jump to `j`: `exp (-β * E j)` — the target's
Gibbs factor — when `j ≠ i`, and `0` at `j = i` (a jump
moves). Direct Gibbs form, Metropolis-free, frozen at
this brick: every later brick of this line uses these
weights or says on its face that it has changed them. -/
noncomputable def gibbsJumpWeight (E : Fin 3 → ℝ) (β : ℝ) (i j : Fin 3) : ℝ :=
  if j = i then 0 else Real.exp (-β * E j)

/-- **The jump normaliser.** The total weight of the jumps
available from position `i` — the row sum the forecast
divides by. (Positive whenever the seat has another
position, since Gibbs factors are positive; that is a
later brick's lemma, not this def's assumption.) -/
noncomputable def gibbsJumpNorm (E : Fin 3 → ℝ) (β : ℝ) (i : Fin 3) : ℝ :=
  ∑ j, gibbsJumpWeight E β i j

/-- **The forecast matrix, as a named object.** The exact
forecast of the next jump: from `i`, the probability of
landing at `j` is the jump weight `i → j` over the total
weight from `i`. This matrix — not any single jump — is
what the line forecasts, manipulates, and proves about. -/
noncomputable def gibbsForecast (E : Fin 3 → ℝ) (β : ℝ) (i j : Fin 3) : ℝ :=
  gibbsJumpWeight E β i j / gibbsJumpNorm E β i

/-- **The Gibbs distribution of the landscape.** The
seat's thermal equilibrium weights: `exp (-β * E j)`
normalised over all positions. Registered as its own
object because Brick 1's stationarity theorem is stated
about it: the forecast's long-run distribution is this
one — the cloud of the seeing, as a finite distribution. -/
noncomputable def gibbsDist (E : Fin 3 → ℝ) (β : ℝ) (j : Fin 3) : ℝ :=
  Real.exp (-β * E j) / ∑ k, Real.exp (-β * E k)

/-- **The forecast from a history.** After a finite
history of positions, the forecast of the next jump is
the forecast matrix at the history's last position; from
the empty history, it is the Gibbs distribution itself
(the registered prior — before any jump, the cloud is
all there is). The dependence is on the last position
ALONE: that is registered here as a definition, and
Brick 2 proves it as the line's honesty fence
(K-JUMP-MEMORY) rather than letting it pass as a
convention. -/
noncomputable def gibbsForecastFrom (E : Fin 3 → ℝ) (β : ℝ)
    (h : List (Fin 3)) (j : Fin 3) : ℝ :=
  match h.getLast? with
  | some i => gibbsForecast E β i j
  | none => gibbsDist E β j

/-- **The forecast claim, pinned as a statement.** The
forecast matrix is a forecast: every row sums to `1`,
and the Gibbs distribution is stationary for it — one
step of the forecast, averaged over the Gibbs
distribution, returns the Gibbs distribution. Brick 1's
charge is this statement, proved at the registered seat,
entry by entry. Nothing about it is claimed here. -/
def gibbsJumpForecastClaim (E : Fin 3 → ℝ) (β : ℝ) : Prop :=
  (∀ i, ∑ j, gibbsForecast E β i j = 1) ∧
    (∀ j, ∑ i, gibbsDist E β i * gibbsForecast E β i j = gibbsDist E β j)

/-- **K-JUMP-MEMORY, pinned as a statement.** The forecast
depends on the history only through its present position:
any two histories ending at the same last position give
the same forecast, for every target `j`. The finite
Markov property, stated as this pin's honesty fence: the
seat itself certifies that previous jump positions buy
the forecast nothing beyond the current one. Brick 2's
charge, beside the manipulation theorems. Nothing about
it is claimed here. -/
def gibbsJumpMemoryFence (E : Fin 3 → ℝ) (β : ℝ) : Prop :=
  ∀ h₁ h₂ : List (Fin 3), ∀ j : Fin 3,
    h₁.getLast? = h₂.getLast? →
      gibbsForecastFrom E β h₁ j = gibbsForecastFrom E β h₂ j

end ThetLogos
