import Mathlib.Tactic
import ThetLogos.RecursiveTurmoilPin

/-!
# ThetLogos.RecursiveTurmoilBrick1 — the census: one claim proved for all seats, one kill fires (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 1
of the Recursive Turmoil line: the registered claims
of the pin, tested.

## Verdicts

- **`turmoilNoFixedShore` PROVED — for every seat**
  (`no_fixed_shore_all`), stronger than the scoped
  Fin 3 census. Suppose a turn fixes `p`: a step to a
  standing `r`, then a step back to `p`. The second
  step decides it. If it is ring motion, `p` is `r`
  carried by the exchange — and `r` stands, so the
  carry is `r` itself: `p = r`, standing. If it is
  condensation, its first clause is exactly that `p`
  stands. Either way `p ∈ geomLocus S`. **K-TURMOIL-FIXED
  does not fire** — on any seat, not just the census
  seat: the loop has no still centre outside standing.
- **`turmoilNoExit` PROVED — for every seat**
  (`no_exit_all`), in its registered absorption
  form: concatenating a turn-chain from `p` to `q`
  with one from `q` onward gives a turn-chain from
  `p`, so the loop from anywhere it reaches stays
  inside its own reach. (Registered knowing the form
  is close to construction — the pin said so; the
  strong no-exit-to-a-limit form remains the
  FRONTIER face, unstatable in-tree.)
- **K-TURMOIL-UNBOUND FIRES** (`turmoil_unbound_kill`)
  on the census seat `turmoilSeat` (Fin 3, charge
  `![0, 0, 1]`, distant `{2}`, exchange swapping 0
  and 2). One turn already escapes the geometry:
  `![1, 0, 0]` turns to `![0, 7, 0]` through the
  standing midpoint `![0, 5, 0]` (both steps are
  condensations — each endpoint stands, and the
  seat's charge, which reads only position 2, is `0`
  throughout). So `![0, 7, 0]` lies in the
  turmoil-orbit of `![1, 0, 0]`. But the
  geometry-orbit of `![1, 0, 0]` has exactly two
  points — the exchange is an involution, so its
  ring iterates alternate between `![1, 0, 0]` and
  `![0, 0, 1]` (`iterate_dichotomy`,
  `geom_orbit_fin`) — and `![0, 7, 0]` is neither
  (its position-1 weight is `7`). The turmoil-orbit
  is strictly larger than the geometry-orbit:
  `turmoilBound` is FALSE on this seat. The faces
  come apart; the binding, as registered, was two
  separate stories — the dynamics, passing through
  standing configurations, walks off the geometry's
  orbit and does not come back.
- **K-TURMOIL-COSTUME does not fire**, tested by the
  same exhibit: the turn is not the identity on
  orbits and the geometry beat does not trivialise
  it — the loop genuinely reaches somewhere the
  geometry alone does not. The turmoil is real; that
  is precisely why it comes unbound.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- The FRONTIER face stands: no exit to a continuum
  limit is claimed or statable here (Dial 3 = 0).
- Per Zero's register (2026-11-24): a completed finite
  theorem is not a continuum theorem. T5 charter,
  NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-- **No fixed shore, for every seat.** A turn that
fixes `p` passes through a standing midpoint `r`;
the return step is either ring motion — which then
gives `p = r` carried by the exchange, and `r`
stands, so `p = r` stands — or condensation, whose
first clause is that `p` stands. K-TURMOIL-FIXED
does not fire, on any seat. -/
theorem no_fixed_shore_all {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (S : CycleSeat Ω) :
    turmoilNoFixedShore S := by
  intro p hp
  obtain ⟨r, _hstep1, hrstand, hstep2⟩ := hp
  have hrstand' : (fun i => r (S.exch i)) = r := hrstand
  show (fun i => p (S.exch i)) = p
  rcases hstep2 with hring | hcond
  · have hpr : p = r := hring.trans hrstand'
    rw [hpr]
    exact hrstand'
  · exact hcond.1

/-- **No exit (absorption), for every seat.** A
turn-chain from `p` to `q` concatenated with a
turn-chain from `q` to `r` is a turn-chain from `p`
to `r` (the chains are spliced at `q`, the shared
shore), so the loop from anywhere it reaches stays
inside its own reach. -/
theorem no_exit_all {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (S : CycleSeat Ω) :
    turmoilNoExit S := by
  intro p q hq r hr
  obtain ⟨n₁, traj₁, h10, h1n, h1steps⟩ := hq
  obtain ⟨n₂, traj₂, h20, h2n, h2steps⟩ := hr
  refine ⟨n₁ + n₂,
    fun k => if k ≤ n₁ then traj₁ k else traj₂ (k - n₁), ?_, ?_, ?_⟩
  · show (if 0 ≤ n₁ then traj₁ 0 else traj₂ (0 - n₁)) = p
    rw [if_pos (Nat.zero_le n₁)]
    exact h10
  · show (if n₁ + n₂ ≤ n₁ then traj₁ (n₁ + n₂)
      else traj₂ (n₁ + n₂ - n₁)) = r
    by_cases hn₂ : n₂ = 0
    · subst hn₂
      simp only [Nat.add_zero]
      rw [if_pos le_rfl, h1n]
      exact h20.symm.trans h2n
    · rw [if_neg (by omega), Nat.add_sub_cancel_left]
      exact h2n
  · intro k hk
    by_cases hk1 : k < n₁
    · have e1 : (fun k => if k ≤ n₁ then traj₁ k
          else traj₂ (k - n₁)) k = traj₁ k :=
        if_pos (Nat.le_of_lt hk1)
      have e2 : (fun k => if k ≤ n₁ then traj₁ k
          else traj₂ (k - n₁)) (k + 1) = traj₁ (k + 1) :=
        if_pos (by omega)
      rw [e1, e2]
      exact h1steps k hk1
    · by_cases hkn : k = n₁
      · rw [hkn]
        have e1 : (fun k => if k ≤ n₁ then traj₁ k
            else traj₂ (k - n₁)) n₁ = traj₁ n₁ :=
          if_pos le_rfl
        have e2 : (fun k => if k ≤ n₁ then traj₁ k
            else traj₂ (k - n₁)) (n₁ + 1) = traj₂ 1 := by
          show (if n₁ + 1 ≤ n₁ then traj₁ (n₁ + 1)
            else traj₂ (n₁ + 1 - n₁)) = traj₂ 1
          rw [if_neg (by omega)]
          congr 1
          omega
        rw [e1, e2, h1n, ← h20]
        exact h2steps 0 (by omega)
      · have hgt : n₁ < k := by omega
        have e1 : (fun k => if k ≤ n₁ then traj₁ k
            else traj₂ (k - n₁)) k = traj₂ (k - n₁) := by
          show (if k ≤ n₁ then traj₁ k else traj₂ (k - n₁))
            = traj₂ (k - n₁)
          rw [if_neg (by omega)]
        have e2 : (fun k => if k ≤ n₁ then traj₁ k
            else traj₂ (k - n₁)) (k + 1)
            = traj₂ (k - n₁ + 1) := by
          show (if k + 1 ≤ n₁ then traj₁ (k + 1)
            else traj₂ (k + 1 - n₁)) = traj₂ (k - n₁ + 1)
          rw [if_neg (by omega)]
          congr 1
          omega
        rw [e1, e2]
        exact h2steps (k - n₁) (by omega)

/-- **The census seat.** Fin 3, charge `![0, 0, 1]`
(the charge reads position 2 alone), distant `{2}`,
exchange swapping 0 and 2 and fixing 1 — the
geometry line's tunneling seat B, so the census runs
on ground already surveyed. -/
def turmoilSeat : CycleSeat (Fin 3) :=
  { charge := ![0, 0, 1], distant := {2}, exch := ![2, 1, 0] }

/-- **One turn, exhibited.** `![1, 0, 0]` turns to
`![0, 7, 0]` on `turmoilSeat`, through the standing
midpoint `![0, 5, 0]`: both steps are condensations
(midpoint and endpoint stand; the charge reads only
position 2 and is `0` at all three configurations). -/
theorem turmoil_turn_exhibit :
    turmoilTurn turmoilSeat ![1, 0, 0] ![0, 7, 0] := by
  have hstand5 : (fun i => (![0, 5, 0] : Fin 3 → ℝ)
        (turmoilSeat.exch i))
      = ![0, 5, 0] := by
    funext i
    fin_cases i <;> simp [turmoilSeat]
  have hmem : ![0, 5, 0] ∈ geomLocus turmoilSeat := hstand5
  refine ⟨![0, 5, 0], ?_, hmem, ?_⟩
  · right
    exact ⟨hstand5, by norm_num [nedCharge, turmoilSeat,
      Fin.sum_univ_three]⟩
  · right
    constructor
    · funext i
      fin_cases i <;> simp [turmoilSeat]
    · norm_num [nedCharge, turmoilSeat, Fin.sum_univ_three]

/-- **The turn's endpoint is in the turmoil-orbit.**
`![0, 7, 0]` is reached from `![1, 0, 0]` by a chain
of one turn. -/
theorem turmoil_orbit_exhibit :
    ![0, 7, 0] ∈ turmoilOrbit turmoilSeat ![1, 0, 0] := by
  refine ⟨1, fun n => if n = 0 then ![1, 0, 0] else ![0, 7, 0],
    rfl, rfl, ?_⟩
  intro k hk
  interval_cases k
  show turmoilTurn turmoilSeat ![1, 0, 0] ![0, 7, 0]
  exact turmoil_turn_exhibit

/-- **The exchange's iterates dichotomise.** The
census seat's exchange is an involution, so every
iterate is either the identity or the exchange
itself. -/
theorem iterate_dichotomy : ∀ n : ℕ,
    turmoilSeat.exch^[n] = id ∨
      turmoilSeat.exch^[n] = turmoilSeat.exch := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Function.iterate_succ]
    rcases ih with h | h
    · rw [h]
      exact Or.inr rfl
    · rw [h]
      left
      funext i
      fin_cases i <;> simp [turmoilSeat, Function.comp_apply]

/-- **The geometry-orbit of `![1, 0, 0]` has exactly
two points.** By the dichotomy, every ring iterate of
`![1, 0, 0]` is itself or `![0, 0, 1]`. -/
theorem geom_orbit_fin {q : Fin 3 → ℝ}
    (hq : q ∈ turmoilGeomOrbit turmoilSeat ![1, 0, 0]) :
    q = ![1, 0, 0] ∨ q = ![0, 0, 1] := by
  obtain ⟨n, hn⟩ := hq
  rcases iterate_dichotomy n with h | h
  · left
    exact hn.trans (by funext i; simp [h])
  · right
    have hEq : (fun i => (![1, 0, 0] : Fin 3 → ℝ)
          (turmoilSeat.exch^[n] i))
        = ![0, 0, 1] := by
      funext i
      simp only [h]
      fin_cases i <;> simp [turmoilSeat]
    exact hn.trans hEq

/-- **K-TURMOIL-UNBOUND FIRES.** `turmoilBound` is
false on `turmoilSeat`: `![0, 7, 0]` lies in the
turmoil-orbit of `![1, 0, 0]` (one exhibited turn)
but not in its geometry-orbit (exactly two points,
`![1, 0, 0]` and `![0, 0, 1]`, neither with
position-1 weight `7`). The dynamics' iterates and
the geometry's orbits are two stories, not one loop. -/
theorem turmoil_unbound_kill :
    ¬ turmoilBound turmoilSeat := by
  intro h
  have hmem : ![0, 7, 0] ∈ turmoilOrbit turmoilSeat ![1, 0, 0] :=
    turmoil_orbit_exhibit
  rw [h ![1, 0, 0]] at hmem
  rcases geom_orbit_fin hmem with h1 | h1
  · have h7 := congrFun h1 1
    simp at h7
  · have h7 := congrFun h1 1
    simp at h7

end ThetLogos
