import Mathlib.Tactic
import ThetLogos.ThreeRoutesPin

/-!
# ThetLogos.ThreeRoutesBrick1 — the owed field, discharged (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 1 of the
Three Routes line, first job per the resume point on
`ThetLogos.ThreeRoutesPin`'s face and Zero's order
2026-11-28 02:51 EST ("build and run all"): **discharge
the OWED field** — derive `RouteSphereSeat.jumpRel` from
`gibbsJumpReach` (the Gibbs seat's own forecast
positivity) instead of leaving it as bare data.

## The derivation, stated openly

A configuration's **position content** is its weight
distribution over the ring positions. One Gibbs jump, at
the configuration level, is this: a **nonzero amount of
the configuration's weight crosses from one position `i`
to another position `j` along a forecast-positive pair**
— `0 < gibbsForecast E β i j`, the jump seat's own banked
law, read exactly as `gibbsJumpReach` reads it. That is
`derivedJumpRel` below. Read its body: `arrowStep`, its
complement, and every route notion occur NOWHERE in it —
the independence the circularity audit demands, checkable
by reading. K-ROUTE-COSTUME stays armed against this
brick: if the derivation were step's complement in
disguise, the kill fires; it is not, and the body is the
evidence.

`RouteSphereSeat.ofGibbs` is the canonical seat whose
`jumpRel` field IS the derived relation. Brick 0's
structure is untouched (the field stays a field — seats
may still carry other jump data); what this brick adds
is the derived seat the audit asked for, and the
verdicts of Brick 2 are stated about `ofGibbs` seats.

## What the derivation immediately shows (proved below)

- The forecast's positivity is exactly `j ≠ i`:
  `gibbsJumpReach_iff`. Gibbs factors are positive at
  every `β` and the normaliser is positive on `Fin 3`,
  so position-level reachability is **temperature-blind**
  — the headwind Brick 0 named on its face, now a proved
  lemma. Its consequence for `thermalOrdersJumps` is
  Brick 2's charge (K-ROUTE-THERMAL is the exact test).
- A derived jump **preserves total weight**
  (`derivedJumpRel_weight`, `routeJump_weight`): jumps
  move weight; they do not create or destroy it.
  Condensation — a step — preserves only charge. That
  asymmetry is what Brick 2's verdicts turn on.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- Per Zero's register (2026-11-24): a completed finite
  theorem is not a continuum theorem. T5 charter,
  NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-- **The jump normaliser is positive on `Fin 3`.** From
any position there is another position, its Gibbs factor
is positive, and every weight is nonnegative — so the
row sum the forecast divides by is positive. (Brick 0
registered this as a later brick's lemma; here it is.) -/
theorem gibbsJumpNorm_pos (E : Fin 3 → ℝ) (β : ℝ) (i : Fin 3) :
    0 < gibbsJumpNorm E β i := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  unfold gibbsJumpNorm
  calc (0 : ℝ) < gibbsJumpWeight E β i j := by
        unfold gibbsJumpWeight
        rw [if_neg hj]
        exact Real.exp_pos _
    _ ≤ ∑ k, gibbsJumpWeight E β i k := by
        apply Finset.single_le_sum (f := fun k => gibbsJumpWeight E β i k)
        · intro k _
          unfold gibbsJumpWeight
          split_ifs
          · exact le_refl 0
          · exact le_of_lt (Real.exp_pos _)
        · exact Finset.mem_univ j

/-- **Position-level jump reachability is exactly
"elsewhere".** `gibbsJumpReach R i j ↔ j ≠ i`: the
forecast gives the jump `i → j` positive weight exactly
when `j ≠ i` — the diagonal weight is `0` by the jump
law's own registration (a jump moves), and every
off-diagonal Gibbs factor is positive at every `β`.
This is the temperature-blindness Brick 0's face named,
proved: bare reachability carries no thermal content,
and Brick 2's thermal test is run with this lemma in
hand. -/
theorem gibbsJumpReach_iff (R : RouteSphereSeat) (i j : Fin 3) :
    gibbsJumpReach R i j ↔ j ≠ i := by
  unfold gibbsJumpReach gibbsForecast
  constructor
  · intro h hji
    subst hji
    unfold gibbsJumpWeight at h
    rw [if_pos rfl, zero_div] at h
    exact lt_irrefl 0 h
  · intro hji
    apply div_pos
    · unfold gibbsJumpWeight
      rw [if_neg hji]
      exact Real.exp_pos _
    · exact gibbsJumpNorm_pos _ _ _

/-- **The derived one-jump relation on configurations.**
`q` is one derived jump from `p` when, for some
positions `i`, `j` and some amount `t > 0`, the pair
`i → j` is forecast-positive (`0 < gibbsForecast E β
i j` — the jump seat's own law, the position-level
content of `gibbsJumpReach`) and `q` is `p` with `t`
units of weight crossed from `i` to `j`: `q j = p j +
t`, `q i = p i - t`, and `q k = p k` elsewhere. The
configuration-level reading of one Gibbs jump, derived
from the forecast alone. `arrowStep` and its complement
occur nowhere in this body — K-ROUTE-COSTUME is armed
against any reading of it as a costume, and the body is
the standing refutation. -/
def derivedJumpRel (E : Fin 3 → ℝ) (β : ℝ)
    (p q : Fin 3 → ℝ) : Prop :=
  ∃ i j : Fin 3, ∃ t : ℝ,
    0 < gibbsForecast E β i j ∧ 0 < t ∧
      q = fun k => p k + (if k = j then t else if k = i then -t else 0)

/-- **The canonical derived seat.** The sphere seat
whose OWED `jumpRel` field is discharged by the
derivation: `jumpRel := derivedJumpRel landscape beta`.
Brick 0's `RouteSphereSeat` structure is untouched —
this constructor is the discharge the audit demanded,
and the seats Brick 2's verdicts are stated about. -/
def RouteSphereSeat.ofGibbs (cycle : CycleSeat (Fin 3))
    (core : Finset (Fin 3)) (landscape : Fin 3 → ℝ)
    (beta : ℝ) : RouteSphereSeat :=
  { cycle := cycle, core := core, landscape := landscape,
    beta := beta, jumpRel := derivedJumpRel landscape beta }

/-- The derived seat's jump field IS the derived
relation, by construction. -/
theorem RouteSphereSeat.ofGibbs_jumpRel
    (cycle : CycleSeat (Fin 3)) (core : Finset (Fin 3))
    (landscape : Fin 3 → ℝ) (beta : ℝ) :
    (RouteSphereSeat.ofGibbs cycle core landscape beta).jumpRel
      = derivedJumpRel landscape beta :=
  rfl

/-- **A derived jump preserves total weight.** The
crossing adds `t` at `j` and removes `t` at `i` (and
`i ≠ j`, since the forecast is positive only
off-diagonal), so the seat's total weight is unchanged:
jumps move weight; they do not create it. -/
theorem derivedJumpRel_weight {E : Fin 3 → ℝ} {β : ℝ}
    {p q : Fin 3 → ℝ} (h : derivedJumpRel E β p q) :
    (∑ k, q k) = ∑ k, p k := by
  obtain ⟨i, j, t, hfc, -, rfl⟩ := h
  have hji : j ≠ i := by
    intro h
    subst h
    unfold gibbsForecast gibbsJumpWeight at hfc
    rw [if_pos rfl, zero_div] at hfc
    exact lt_irrefl 0 hfc
  have hg : (∑ k : Fin 3,
      (if k = j then t else if k = i then -t else 0)) = 0 := by
    have e1 : (∑ k : Fin 3,
        (if k = j then t else if k = i then -t else 0))
        = (∑ k : Fin 3, (if k = j then t else 0))
          + ∑ k : Fin 3, (if k = i then -t else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k = j
      · subst hkj
        simp [hji]
      · by_cases hki : k = i
        · subst hki
          simp [hkj]
        · simp [hkj, hki]
    rw [e1]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact add_neg_cancel t
  rw [Finset.sum_add_distrib, hg, add_zero]

/-- **Jump reachability on a derived seat preserves
total weight.** Every trajectory of derived jumps keeps
`∑ k, p k` fixed, by induction on its length, from
`derivedJumpRel_weight`. This is the invariant Brick 2
sets against the step route: condensation — a step —
preserves the seat's charge, not its weight, so the
step route is NOT contained in the jump route on
derived seats. -/
theorem routeJump_weight {c : CycleSeat (Fin 3)}
    {core : Finset (Fin 3)} {E : Fin 3 → ℝ} {β : ℝ}
    {p q : Fin 3 → ℝ}
    (h : routeJump (RouteSphereSeat.ofGibbs c core E β) p q) :
    (∑ k, q k) = ∑ k, p k := by
  obtain ⟨n, traj, h0, hn, hsteps⟩ := h
  have key : ∀ k : ℕ, k ≤ n → (∑ x, traj k x) = ∑ x, p x := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [h0]
    | succ k ih =>
      intro hk
      have hstep := hsteps k (Nat.lt_of_succ_le hk)
      rw [RouteSphereSeat.ofGibbs_jumpRel] at hstep
      exact (derivedJumpRel_weight hstep).trans (ih (Nat.le_of_succ_le hk))
  rw [← hn]
  exact key n (le_refl n)

end ThetLogos
