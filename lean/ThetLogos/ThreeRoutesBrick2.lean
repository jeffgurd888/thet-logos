import Mathlib.Tactic
import ThetLogos.ThreeRoutesPin
import ThetLogos.ThreeRoutesBrick1

/-!
# ThetLogos.ThreeRoutesBrick2 — the route verdicts on the smallest seat (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 2 of
the Three Routes line: the verdicts Brick 0 pinned and
Brick 1 prepared, taken on the smallest seat — or the
kills, at the same volume.

## The test seat

`frozenSeat`: the DERIVED sphere seat (Brick 1's
`RouteSphereSeat.ofGibbs`) over `frozenCycle` — charge
`![1, -1, 2]`, distant `{2}`, and the FROZEN exchange
`exch = id`. The frozen exchange is the honest test
bed for the order claims: with no ring motion, the
step route is exactly charge-preserving condensation,
so both routes can be characterised outright — the
jump route by Brick 1's invariant (total weight), the
step route by charge. What the two characterisations
say about each other is the verdict, and it is not
the pinned order.

## The verdicts

- **Standing ⊆ step: PROVED, for every seat**
  (`standing_subset_step`). A standing-only history is
  an `ArrowPath` whose steps are condensations, and
  condensation is an `arrowStep` disjunct — the first
  inclusion of `routeOrder` is a theorem.
- **Jump strictness: PROVED on the frozen seat**
  (`frozen_strictness`). `![1, 1, -2]` is jump-reachable
  from `![0, 0, 0]` (two derived jumps, exhibited) and
  not step-reachable (steps preserve `nedCharge`; the
  target's charge is `-4 ≠ 0`). The jump route goes
  somewhere no dynamical path goes. **K-ROUTE-COLLAPSE
  does not fire** — the routes do not coincide.
- **Route order: REFUTED on the frozen seat**
  (`frozen_not_routeOrder`). The second inclusion
  dies: `![0, 0, 0]` is step-reachable from
  `![1, 1, 0]` (one condensation — same charge `0`)
  but not jump-reachable (derived jumps preserve total
  weight; `0 ≠ 2`, by Brick 1's `routeJump_weight`).
  So on derived seats the three routes are NOT ordered
  as pinned: the comparison is not empty (strictness
  holds) and it is not an order (the second inclusion
  fails) — the routes cross. ROUTE ORDER, as a
  statement about the derived jump law, is dead at the
  finite level; its first inclusion survives as the
  theorem above.
- **K-ROUTE-THERMAL: FIRES, in its derived form.**
  Brick 0's face prescribes the test verbatim: "if the
  derived jump law's reachability turns out independent
  of the thermal datum, the kill fires." It is
  (`jumpRel_independent`): for derived seats, `routeJump`
  depends ONLY on the landscape and the temperature —
  change the charge, the exchange, the core, or the
  distant component (where the shadow form of
  `thermalOrdersJumps` holds the heat) and the
  jump-reachable set does not move
  (`routeJump_distant_independent`). Brick 1's
  `gibbsJumpReach_iff` already showed position-level
  reachability is exactly `j ≠ i` at every `β`. The
  seeing's thermal content therefore does NOT live in
  reachability at the finite level; it retreats to the
  forecast VALUES (the statistics), exactly where
  Brick 0's face said it lives. Disclosed at full rank:
  `thermalOrdersJumps` as literally stated ranges over
  ALL sphere seats, whose owed field is unconstrained
  bare data, so its letter can be satisfied by changing
  the field itself — a costume satisfaction, worth
  nothing; the kill fires against the derived law,
  which is the only reading Brick 0's audit permits.
- **K-ROUTE-FREE: untested at this brick.** Its step
  arm is the Entropy-Arrow conjecture, tested on that
  line's own ground; its jump arm (entropy along
  derived jumps) is a later brick's question. Named
  here so the silence is registered, not passed over.

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

/-- **Standing ⊆ step, for every sphere seat.** A
standing-only history is an `ArrowPath` all of whose
steps are condensations; condensation is the second
disjunct of `arrowStep`, so the same path is a
dynamical history. The first inclusion of `routeOrder`,
discharged as a theorem — the transport is the
identity on paths. -/
theorem standing_subset_step (R : RouteSphereSeat)
    (p q : Fin 3 → ℝ) :
    routeStanding R p q → routeStep R p q := by
  intro h
  obtain ⟨path, -⟩ := h
  exact ⟨path⟩

/-- **The frozen cycle seat.** Charge `![1, -1, 2]`,
distant component `{2}`, and the frozen exchange
`exch = id`: no ring motion, so the seat's dynamics
are condensation alone and both routes admit outright
characterisations. -/
def frozenCycle : CycleSeat (Fin 3) :=
  { charge := ![1, -1, 2], distant := {2}, exch := id }

/-- **The frozen test seat.** The derived sphere seat
over `frozenCycle` (Brick 1's `ofGibbs`): core
`{0, 1}`, flat landscape, inverse temperature `1`. -/
def frozenSeat : RouteSphereSeat :=
  RouteSphereSeat.ofGibbs frozenCycle {0, 1} ![0, 0, 0] 1

/-- **Charge is invariant along frozen histories.**
Every step of the frozen seat preserves `nedCharge`:
ring motion is the identity (the exchange is frozen),
and condensation preserves charge by its definition.
Induction on the path's steps. -/
theorem frozen_charge_along {p q : Fin 3 → ℝ}
    (path : ArrowPath frozenCycle p q) :
    ∀ k : ℕ, k ≤ path.len →
      nedCharge frozenCycle.charge (path.traj k)
        = nedCharge frozenCycle.charge p := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [path.start]
  | succ k ih =>
    intro hk
    have ih' := ih (Nat.le_of_succ_le hk)
    rcases path.steps k (Nat.lt_of_succ_le hk) with hring | hcond
    · have hring' : path.traj (k + 1)
          = fun i => path.traj k (frozenCycle.exch i) := hring
      have hfun : (fun i => path.traj k (frozenCycle.exch i))
          = path.traj k := rfl
      rw [hring', hfun]
      exact ih'
    · obtain ⟨-, hcharge⟩ := hcond
      exact hcharge.trans ih'

/-- **The jump exhibit on the frozen seat.**
`![1, 1, -2]` is jump-reachable from `![0, 0, 0]` by
two derived jumps: weight `1` crosses `2 → 0`, then
weight `1` crosses `2 → 1`. Both pairs are
forecast-positive (off-diagonal, by Brick 1's
`gibbsJumpReach_iff` content: the forecast is a
positive Gibbs factor over a positive normaliser). -/
theorem frozen_jump_exhibit :
    routeJump frozenSeat ![0, 0, 0] ![1, 1, -2] := by
  have hfc20 : 0 < gibbsForecast ![0, 0, 0] 1 2 0 := by
    show 0 < gibbsJumpWeight ![0, 0, 0] 1 2 0
      / gibbsJumpNorm ![0, 0, 0] 1 2
    apply div_pos
    · unfold gibbsJumpWeight
      rw [if_neg (by decide : (0 : Fin 3) ≠ 2)]
      exact Real.exp_pos _
    · exact gibbsJumpNorm_pos _ _ _
  have hfc21 : 0 < gibbsForecast ![0, 0, 0] 1 2 1 := by
    show 0 < gibbsJumpWeight ![0, 0, 0] 1 2 1
      / gibbsJumpNorm ![0, 0, 0] 1 2
    apply div_pos
    · unfold gibbsJumpWeight
      rw [if_neg (by decide : (1 : Fin 3) ≠ 2)]
      exact Real.exp_pos _
    · exact gibbsJumpNorm_pos _ _ _
  refine ⟨2, fun k => if k = 0 then ![0, 0, 0]
    else if k = 1 then ![1, 0, -1] else ![1, 1, -2],
    rfl, by simp, ?_⟩
  intro k hk
  interval_cases k
  · show derivedJumpRel ![0, 0, 0] 1 ![0, 0, 0] ![1, 0, -1]
    refine ⟨2, 0, 1, hfc20, by norm_num, ?_⟩
    funext m
    fin_cases m <;> simp <;> norm_num
  · show derivedJumpRel ![0, 0, 0] 1 ![1, 0, -1] ![1, 1, -2]
    refine ⟨2, 1, 1, hfc21, by norm_num, ?_⟩
    funext m
    fin_cases m <;> simp <;> norm_num

/-- **Jump strictness on the frozen seat.** The
exhibit's target is jump-reachable and not
step-reachable: every frozen history preserves
`nedCharge` (`frozen_charge_along`), the start's
charge is `0`, and the target's charge is
`1 - 1 + (-2) * 2 = -4`. The diagram's purple line
goes somewhere no path goes — K-ROUTE-COLLAPSE does
not fire. -/
theorem frozen_strictness : jumpStrictness frozenSeat := by
  refine ⟨![0, 0, 0], ![1, 1, -2], frozen_jump_exhibit, ?_⟩
  intro h
  obtain ⟨path⟩ := h
  have hch := frozen_charge_along path path.len (le_refl _)
  rw [path.finish] at hch
  simp [nedCharge, frozenCycle, Fin.sum_univ_three] at hch

/-- **Route order is REFUTED on the frozen seat.** The
second inclusion fails: `![0, 0, 0]` is step-reachable
from `![1, 1, 0]` — one condensation, both of charge
`0` — but not jump-reachable, because derived jumps
preserve total weight (Brick 1's `routeJump_weight`)
and `0 ≠ 1 + 1 + 0`. The pinned ROUTE ORDER dies at
the finite level on derived seats; its first inclusion
stands as `standing_subset_step`. -/
theorem frozen_not_routeOrder : ¬ routeOrder frozenSeat := by
  intro hord
  obtain ⟨-, h2⟩ := hord
  have hstep : routeStep frozenSeat ![1, 1, 0] ![0, 0, 0] := by
    show Nonempty (ArrowPath frozenCycle ![1, 1, 0] ![0, 0, 0])
    refine ⟨⟨1, fun k => if k = 0 then ![1, 1, 0] else ![0, 0, 0],
      rfl, by simp, ?_⟩⟩
    intro k hk
    interval_cases k
    show arrowStep frozenCycle ![1, 1, 0] ![0, 0, 0]
    right
    constructor
    · funext i
      fin_cases i <;> simp [frozenCycle]
    · norm_num [nedCharge, frozenCycle, Fin.sum_univ_three]
  have hjump := h2 ![1, 1, 0] ![0, 0, 0] hstep
  have hw := routeJump_weight hjump
  simp [Fin.sum_univ_three] at hw
  norm_num at hw

/-- **Derived jump reachability depends only on the
landscape and the temperature.** For `ofGibbs` seats,
`routeJump` is the same relation whatever charge,
exchange, core, or distant component the seat carries:
the relation is built from the seat's `jumpRel` field
alone, and Brick 1 fixed that field to
`derivedJumpRel landscape beta`. -/
theorem jumpRel_independent (c₁ c₂ : CycleSeat (Fin 3))
    (core₁ core₂ : Finset (Fin 3)) (E : Fin 3 → ℝ) (β : ℝ)
    (p q : Fin 3 → ℝ) :
    routeJump (RouteSphereSeat.ofGibbs c₁ core₁ E β) p q ↔
      routeJump (RouteSphereSeat.ofGibbs c₂ core₂ E β) p q := by
  constructor
  · intro h
    obtain ⟨n, traj, h0, hn, hs⟩ := h
    refine ⟨n, traj, h0, hn, ?_⟩
    intro k hk
    have hstep := hs k hk
    rwa [RouteSphereSeat.ofGibbs_jumpRel] at hstep ⊢
  · intro h
    obtain ⟨n, traj, h0, hn, hs⟩ := h
    refine ⟨n, traj, h0, hn, ?_⟩
    intro k hk
    have hstep := hs k hk
    rwa [RouteSphereSeat.ofGibbs_jumpRel] at hstep ⊢

/-- **K-ROUTE-THERMAL's firing form.** Change ONLY the
distant component — where the thermal datum of
`thermalOrdersJumps`' shadow form is held — and the
derived seat's jump-reachable set does not move. With
`jumpRel_independent`, the derived jump law's
reachability is provably independent of the thermal
datum: the kill Brick 0 armed fires, and the seeing's
thermal content retreats to the forecast values. -/
theorem routeJump_distant_independent (c : CycleSeat (Fin 3))
    (core : Finset (Fin 3)) (E : Fin 3 → ℝ) (β : ℝ)
    (d : Finset (Fin 3)) (p q : Fin 3 → ℝ) :
    routeJump (RouteSphereSeat.ofGibbs c core E β) p q ↔
      routeJump (RouteSphereSeat.ofGibbs
        { charge := c.charge, distant := d, exch := c.exch }
        core E β) p q :=
  jumpRel_independent c _ core core E β p q

end ThetLogos
