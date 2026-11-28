import Mathlib.Tactic
import ThetLogos.GeometryForcesPin

/-!
# ThetLogos.GeometryForcesBrick1 — geometry does not force: both kills fire (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 1 of
the Geometry Forces line: the two pinned statements
tested on the smallest seats.

## What the NED line already decided (reported first, as scoped)

The NED line's banked extrema close the unrelativised
question before this line starts: over ALL weight
functions on a seat, `nedEntropy` is unbounded above
and attains no maximum (`nedExhibit_no_max_entropy`,
`nedExhibit_entropy_unbounded`, banked at lane grade
in the NED line, Bricks 2a/2b) — K-NED fired there in
proved form, and the NED extremal identification is
dead at the finite level. That is why Brick 0's
`cycleBalanced` maximises only over the NORMALISED
ZERO-CHARGE class. What remains for this line is
exactly the relativised question: does the maximum
over that class sit exactly on the geometric locus,
and are the tunneling channels the geometry's? Both
answers are no.

## The kills — both fire, at full rank

- **K-GEOM-ENTROPY FIRES** (`geom_entropy_kill`), via
  arm 2 of `geomForcesEntropy`. On `geomSeatId`
  (Fin 3, charge `![1, -1, 0]`, identity exchange —
  so the locus is EVERYTHING), the configuration
  `![1/2, 1/2, 0]` is normalised, zero-charge, and
  standing, so arm 2 would make it `cycleBalanced`.
  But `![1/3, 1/3, 1/3]` is in the same class with
  entropy `log 3 > log 2`, the entropy of
  `![1/2, 1/2, 0]`: not maximal, not balanced. The
  maximum over the class does not sit exactly on the
  locus — here the locus is too big (identity
  exchange makes everything stand, balanced or not).
  Arm 1 and arm 3 are untested; the statement dies
  on arm 2 regardless, and this brick says so.
- **K-GEOM-TUNNEL FIRES** (`geom_tunnel_kill`), and
  with it **K-GEOM-COSTUME** in the same exhibit. The
  seats `tunnelSeatA` (charge `![1, 0, 0]`) and
  `tunnelSeatB` (charge `![0, 0, 1]`) have the SAME
  geometry (`geom_tunnel_eq`: same exchange, same
  distant component — `geomOf` does not read the
  charge). For the pair `P = ![1, 0, 0]`,
  `Q = ![1, 5, 1]`: on seat B a tunneling channel
  joins them (`tunnel_joined_B`: a ring motion to
  `![0, 0, 1]`, then a condensation to `Q`; and no
  standing-only history joins them, because standing
  steps preserve B's charge and B reads `0` on `P`,
  `1` on `Q`). On seat A a standing-only history
  joins them directly (one condensation; A reads
  charge `1` on both), so they are NOT tunneling-
  joined there. Same geometry, opposite tunneling:
  the channel structure is decided by the CHARGE,
  which the geometry does not carry. GEOMETRY FORCES
  TUNNELING is dead at the finite level, and the
  geometry, worn as the channel's explanation, is a
  costume for charge data — K-GEOM-COSTUME's firing
  form, named as such.

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

/-- **The entropy-kill seat.** Fin 3, charge
`![1, -1, 0]`, identity exchange: every configuration
stands, so the locus is everything — the widest
possible locus against which to test whether the
entropy maximum sits exactly on it. -/
def geomSeatId : CycleSeat (Fin 3) :=
  { charge := ![1, -1, 0], distant := ∅, exch := id }

/-- **K-GEOM-ENTROPY FIRES.** `geomForcesEntropy` is
false on `geomSeatId`, by its second arm:
`![1/2, 1/2, 0]` is normalised, zero-charge, and
standing (the exchange is the identity), so the arm
would make it balanced — but `![1/3, 1/3, 1/3]`, in
the same normalised zero-charge class, has strictly
larger entropy (`log 3 > log 2`). Arms 1 and 3 are
untested; the statement dies on arm 2. -/
theorem geom_entropy_kill :
    ¬ geomForcesEntropy geomSeatId := by
  intro h
  have hbal := h.2.1 ![1 / 2, 1 / 2, 0]
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [nedZeroCharge, nedCharge, geomSeatId,
      Fin.sum_univ_three])
    (by
      show (fun i => ![1 / 2, 1 / 2, 0] (geomSeatId.exch i))
        = ![1 / 2, 1 / 2, 0]
      funext i
      fin_cases i <;> simp [geomSeatId])
  have hle := hbal.2.2 ![1 / 3, 1 / 3, 1 / 3]
    (by norm_num [Fin.sum_univ_three])
    (by norm_num [nedZeroCharge, nedCharge, geomSeatId,
      Fin.sum_univ_three])
  have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  have hlog3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.log_inv]
  have e3 : nedEntropy ![1 / 3, 1 / 3, 1 / 3] = Real.log 3 := by
    have e : nedEntropy ![1 / 3, 1 / 3, 1 / 3]
        = -(1 / 3 * Real.log (1 / 3) + 1 / 3 * Real.log (1 / 3)
          + 1 / 3 * Real.log (1 / 3)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_three]
    rw [e, hlog3]
    ring
  have e2 : nedEntropy ![1 / 2, 1 / 2, 0] = Real.log 2 := by
    have e : nedEntropy ![1 / 2, 1 / 2, 0]
        = -(1 / 2 * Real.log (1 / 2)
          + 1 / 2 * Real.log (1 / 2)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_three]
    rw [e, hlog2]
    ring
  rw [e3, e2] at hle
  have hlt : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  exact (not_le_of_gt hlt) hle

/-- **Tunneling seat A.** Fin 3, charge `![1, 0, 0]`
(the charge reads position 0), distant `{2}`,
exchange swapping 0 and 2. -/
def tunnelSeatA : CycleSeat (Fin 3) :=
  { charge := ![1, 0, 0], distant := {2}, exch := ![2, 1, 0] }

/-- **Tunneling seat B.** Fin 3, charge `![0, 0, 1]`
(the charge reads position 2), distant `{2}`, the
SAME exchange as seat A. The two seats differ only
in the charge — which `geomOf` does not read. -/
def tunnelSeatB : CycleSeat (Fin 3) :=
  { charge := ![0, 0, 1], distant := {2}, exch := ![2, 1, 0] }

/-- **Same geometry.** `geomOf` reads the exchange
(orbits, locus) and the distant component only; the
two tunneling seats agree on both, so their
geometries are equal — the charge difference is
invisible to `geomOf`. -/
theorem geom_tunnel_eq :
    geomOf tunnelSeatA = geomOf tunnelSeatB := rfl

/-- **Standing steps preserve B's charge.** Along
any standing-only history on `tunnelSeatB`, the net
charge is constant — each step is a condensation,
and condensation preserves `nedCharge` by its
definition. -/
theorem tunnel_charge_along {p q : Fin 3 → ℝ}
    (h : geomStandingHistory tunnelSeatB p q) :
    nedCharge tunnelSeatB.charge q
      = nedCharge tunnelSeatB.charge p := by
  obtain ⟨path, hsteps⟩ := h
  have key : ∀ k, k ≤ path.len →
      nedCharge tunnelSeatB.charge (path.traj k)
        = nedCharge tunnelSeatB.charge p := by
    intro k hk
    induction k with
    | zero => rw [path.start]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hcond := hsteps k (Nat.lt_of_succ_le hk)
      rw [hcond.2, ih']
  have hfin := key path.len le_rfl
  rwa [path.finish] at hfin

/-- **The channel on seat B.** `![1, 0, 0]` and
`![1, 5, 1]` are tunneling-joined on `tunnelSeatB`:
a two-step history (ring motion to `![0, 0, 1]`,
then condensation to `![1, 5, 1]`, which stands and
carries B-charge `1`) reaches the second from the
first, while no standing-only history does — standing
steps preserve B's charge, and B reads `0` on
`![1, 0, 0]` but `1` on `![1, 5, 1]`. -/
theorem tunnel_joined_B :
    geomTunnelJoined tunnelSeatB ![1, 0, 0] ![1, 5, 1] := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨2, fun n => if n = 0 then ![1, 0, 0]
        else if n = 1 then ![0, 0, 1] else ![1, 5, 1],
      rfl, rfl, ?_⟩⟩
    intro k hk
    interval_cases k
    · show arrowStep tunnelSeatB ![1, 0, 0] ![0, 0, 1]
      left
      funext i
      fin_cases i <;> simp [tunnelSeatB]
    · show arrowStep tunnelSeatB ![0, 0, 1] ![1, 5, 1]
      right
      constructor
      · funext i
        fin_cases i <;> simp [tunnelSeatB]
      · norm_num [nedCharge, tunnelSeatB, Fin.sum_univ_three]
  · intro hstand
    have hch := tunnel_charge_along hstand
    norm_num [nedCharge, tunnelSeatB, Fin.sum_univ_three] at hch

/-- **No channel on seat A.** The same pair is NOT
tunneling-joined on `tunnelSeatA`: a one-step
standing-only history joins them directly
(`![1, 5, 1]` stands under the exchange, and A reads
charge `1` on both configurations). -/
theorem tunnel_not_joined_A :
    ¬ geomTunnelJoined tunnelSeatA ![1, 0, 0] ![1, 5, 1] := by
  intro h
  apply h.2
  have hcond : cycleCondensed tunnelSeatA ![1, 0, 0] ![1, 5, 1] := by
    constructor
    · funext i
      fin_cases i <;> simp [tunnelSeatA]
    · norm_num [nedCharge, tunnelSeatA, Fin.sum_univ_three]
  refine ⟨⟨1, fun n => if n = 0 then ![1, 0, 0] else ![1, 5, 1],
    rfl, rfl, ?_⟩, ?_⟩
  · intro k hk
    interval_cases k
    show arrowStep tunnelSeatA ![1, 0, 0] ![1, 5, 1]
    exact Or.inr hcond
  · intro k hk
    interval_cases k
    show cycleCondensed tunnelSeatA ![1, 0, 0] ![1, 5, 1]
    exact hcond

/-- **K-GEOM-TUNNEL FIRES — and K-GEOM-COSTUME in
the same exhibit.** `geomForcesTunneling` is false
on `tunnelSeatB`: `tunnelSeatA` has the same
geometry, yet the pair `![1, 0, 0]`, `![1, 5, 1]` is
tunneling-joined on B and not on A. The tunneling
channels are decided by the charge, which the
geometry does not carry — geometry worn as the
channels' explanation is a costume for charge data. -/
theorem geom_tunnel_kill :
    ¬ geomForcesTunneling tunnelSeatB := by
  intro h
  have hiff := h tunnelSeatA geom_tunnel_eq ![1, 0, 0] ![1, 5, 1]
  exact tunnel_not_joined_A (hiff.mp tunnel_joined_B)

end ThetLogos
