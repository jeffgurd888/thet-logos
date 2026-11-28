import Mathlib.Tactic
import ThetLogos.EntropyArrowPin

/-!
# ThetLogos.EntropyArrowBrick1 — the arrow tested on Fin 2; both kills fire (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 1 of
the Entropy Arrow line: the pinned conjecture's two
arms, tested on the smallest seat where they can be
tested at all.

## What is proved

- **Ring motion preserves entropy** (`ring_entropy`).
  For any seat whose exchange is bijective, carrying a
  configuration by the exchange permutes its weights,
  and `nedEntropy` — a symmetric function of the
  weights — is unchanged. (No involution hypothesis
  is needed; bijectivity is the whole content.)
- **The balanced point of the Fin 2 seat**
  (`balanced_half`): on `arrowSeatFinTwo` (charge
  `![1, -1]`, exchange swapping the two points),
  `![1/2, 1/2]` is `cycleBalanced` — the unique point
  of the normalised zero-charge class, as in the
  cycle line's Brick 1.

## The kills — both fire, at full rank

- **K-ARROW FIRES** (`arrow_lower_exhibit`,
  `arrow_kill`). A one-step condensation history runs
  from `![1/2, 1/2]` to `![2, 2]`: `![2, 2]` stands
  under the swap (it is constant) and carries the
  same charge `0`. Its entropy is `-4 * log 2`,
  strictly below `log 2`, the entropy of
  `![1/2, 1/2]`. A realizable dynamical history
  strictly lowers entropy, so `arrowNoBackwardReturn`
  is FALSE on this seat: NO BACKWARD RETURN is dead
  at the finite level. The condensation step, as
  pinned, constrains only charge and standing — it
  does not see weight growth, and weight growth is
  exactly where entropy falls.
- **K-ARROW-FORWARD FIRES** (`arrow_forward_kill`).
  `arrowForwardExists` is also FALSE on this seat.
  The obstruction is a charge invariant, not an
  entropy one: on `arrowSeatFinTwo` ring motion
  NEGATES the net charge (`charge_comp_swap`) and
  condensation preserves it, so every history from
  `![1, 0]` keeps the charge in `{1, -1}`
  (`arrow_charge_pm`) — while the balanced point
  `![1/2, 1/2]` has charge `0`. No history from
  `![1, 0]` reaches the balanced point at all, let
  alone by an entropy-increasing path, although
  `![1, 0]`'s entropy `0` is strictly below the
  balanced point's `log 2`. FORWARD EXISTS is dead
  at the finite level.

Both arms of the pinned conjecture fail on the
smallest seat, for two different named reasons:
condensation is entropy-blind downward, and the
charge invariant walls the balanced point off from
whole charge classes. A revived arrow needs a step
law that sees weights (for the first) and a charge
theory that lets histories change class (for the
second) — new registrations, new scopes, Zero's
word. This line does not re-aim the statements
silently.

**K-ARROW-TRIVIAL does not fire**: `arrowStep` is
untouched by this brick and `nedEntropy` enters no
step definition; the kills land on the derived steps
as pinned.

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

/-- **The Fin 2 arrow seat.** Charge `![1, -1]`,
distant component `{0}`, exchange swapping the two
points — the cycle line's smallest seat, reused so
both lines are tested on the same ground. -/
def arrowSeatFinTwo : CycleSeat (Fin 2) :=
  { charge := ![1, -1], distant := {0}, exch := ![1, 0] }

/-- **Ring motion preserves entropy.** Carrying a
configuration by a bijective exchange permutes its
weights; `nedEntropy`, a symmetric function of the
weights, is unchanged. -/
theorem ring_entropy {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : CycleSeat Ω) (p : Ω → ℝ) (hb : Function.Bijective S.exch) :
    nedEntropy (fun i => p (S.exch i)) = nedEntropy p := by
  simp only [nedEntropy, gibbsEntropy]
  congr 1
  exact Equiv.sum_comp (Equiv.ofBijective S.exch hb)
    (fun j => p j * Real.log (p j))

/-- **The balanced point of the Fin 2 seat.**
`![1/2, 1/2]` is `cycleBalanced` on
`arrowSeatFinTwo`: normalised, zero-charge, and the
unique — hence maximal-entropy — point of the
normalised zero-charge class. -/
theorem balanced_half :
    cycleBalanced arrowSeatFinTwo ![1 / 2, 1 / 2] := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_two]
  · norm_num [nedZeroCharge, nedCharge, arrowSeatFinTwo,
      Fin.sum_univ_two]
  · intro r hsum hzc
    have hsum' : r 0 + r 1 = 1 := by
      simpa [Fin.sum_univ_two] using hsum
    have hzc' : r 0 - r 1 = 0 := by
      have h := hzc
      simp [nedZeroCharge, nedCharge, arrowSeatFinTwo,
        Fin.sum_univ_two] at h
      linarith
    have hr0 : r 0 = 1 / 2 := by linarith
    have hr1 : r 1 = 1 / 2 := by linarith
    have hent : nedEntropy r
        = -(r 0 * Real.log (r 0) + r 1 * Real.log (r 1)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    have hentp : nedEntropy ![1 / 2, 1 / 2]
        = -(1 / 2 * Real.log (1 / 2)
          + 1 / 2 * Real.log (1 / 2)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    rw [hent, hentp, hr0, hr1]

/-- **K-ARROW's ground: the lowering path.** A
one-step condensation path from `![1/2, 1/2]` to
`![2, 2]` on `arrowSeatFinTwo`: `![2, 2]` stands
under the swap (it is constant) and carries the same
charge `0`. -/
noncomputable def arrow_lower_path :
    ArrowPath arrowSeatFinTwo ![1 / 2, 1 / 2] ![2, 2] := by
  refine ⟨1, fun n => if n = 0 then ![1 / 2, 1 / 2] else ![2, 2],
    rfl, rfl, ?_⟩
  intro k hk
  interval_cases k
  show arrowStep arrowSeatFinTwo ![1 / 2, 1 / 2] ![2, 2]
  right
  constructor
  · funext i
    fin_cases i <;> simp [arrowSeatFinTwo]
  · norm_num [nedCharge, arrowSeatFinTwo, Fin.sum_univ_two]

/-- **K-ARROW's ground: the entropy drop.** The
entropy of `![2, 2]` is `-4 * log 2`, strictly below
the entropy `log 2` of `![1/2, 1/2]`. -/
theorem arrow_lower_entropy :
    nedEntropy ![2, 2] < nedEntropy ![1 / 2, 1 / 2] := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  have e1 : nedEntropy ![2, 2] = -4 * Real.log 2 := by
    have e : nedEntropy ![2, 2]
        = -(2 * Real.log 2 + 2 * Real.log 2) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    rw [e]
    ring
  have e2 : nedEntropy ![1 / 2, 1 / 2] = Real.log 2 := by
    have e : nedEntropy ![1 / 2, 1 / 2]
        = -(1 / 2 * Real.log (1 / 2)
          + 1 / 2 * Real.log (1 / 2)) := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    rw [e, hlog]
    ring
  rw [e1, e2]
  linarith

/-- **K-ARROW FIRES.** `arrowNoBackwardReturn` is
false on `arrowSeatFinTwo`: the exhibited history
runs from `![1/2, 1/2]` to a configuration of
strictly lower entropy. NO BACKWARD RETURN is dead
at the finite level. -/
theorem arrow_kill :
    ¬ arrowNoBackwardReturn arrowSeatFinTwo := by
  intro h
  have hle := h ![1 / 2, 1 / 2] ![2, 2] ⟨arrow_lower_path⟩
  exact (not_lt_of_ge hle) arrow_lower_entropy

/-- **Ring motion negates the charge** on
`arrowSeatFinTwo`: the exchange swaps the two
positions, and the charge `![1, -1]` is antisymmetric
under the swap. -/
theorem charge_comp_swap (p : Fin 2 → ℝ) :
    nedCharge arrowSeatFinTwo.charge
        (fun i => p (arrowSeatFinTwo.exch i))
      = -nedCharge arrowSeatFinTwo.charge p := by
  simp [nedCharge, arrowSeatFinTwo, Fin.sum_univ_two]

/-- **The charge invariant.** Every arrow history on
`arrowSeatFinTwo` starting at charge `1` or `-1`
ends at charge `1` or `-1`: ring motion negates the
charge, condensation preserves it, and no step does
anything else to it. -/
theorem arrow_charge_pm {p p' : Fin 2 → ℝ}
    (path : ArrowPath arrowSeatFinTwo p p')
    (h : nedCharge arrowSeatFinTwo.charge p = 1 ∨
      nedCharge arrowSeatFinTwo.charge p = -1) :
    nedCharge arrowSeatFinTwo.charge p' = 1 ∨
      nedCharge arrowSeatFinTwo.charge p' = -1 := by
  have key : ∀ k, k ≤ path.len →
      nedCharge arrowSeatFinTwo.charge (path.traj k) = 1 ∨
        nedCharge arrowSeatFinTwo.charge (path.traj k) = -1 := by
    intro k hk
    induction k with
    | zero => rw [path.start]; exact h
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hstep := path.steps k (Nat.lt_of_succ_le hk)
      rcases hstep with hring | hcond
      · rw [hring]
        rcases ih' with h1 | h1
        · rw [charge_comp_swap, h1]
          exact Or.inr (by norm_num)
        · rw [charge_comp_swap, h1]
          exact Or.inl (by norm_num)
      · rw [hcond.2]
        exact ih'
  have hfin := key path.len le_rfl
  rwa [path.finish] at hfin

/-- **K-ARROW-FORWARD FIRES.** `arrowForwardExists`
is false on `arrowSeatFinTwo`: `![1, 0]` has entropy
`0`, strictly below the balanced point's `log 2`,
but every history from `![1, 0]` keeps the charge in
`{1, -1}` while the balanced point's charge is `0` —
no path reaches it, increasing or otherwise.
FORWARD EXISTS is dead at the finite level, killed
by a charge obstruction. -/
theorem arrow_forward_kill :
    ¬ arrowForwardExists arrowSeatFinTwo := by
  intro h
  obtain ⟨path, -⟩ := h ![1, 0] ![1 / 2, 1 / 2] balanced_half (by
    have hent0 : nedEntropy ![1, 0] = 0 := by
      simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
    have hentb : nedEntropy ![1 / 2, 1 / 2] = Real.log 2 := by
      have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
      have e : nedEntropy ![1 / 2, 1 / 2]
          = -(1 / 2 * Real.log (1 / 2)
            + 1 / 2 * Real.log (1 / 2)) := by
        simp [nedEntropy, gibbsEntropy, Fin.sum_univ_two]
      rw [e, hlog]
      ring
    rw [hent0, hentb]
    exact Real.log_pos (by norm_num))
  have hpm := arrow_charge_pm path
    (Or.inl (by norm_num [nedCharge, arrowSeatFinTwo,
      Fin.sum_univ_two]))
  have hcb : nedCharge arrowSeatFinTwo.charge ![1 / 2, 1 / 2]
      = 0 := balanced_half.2.1
  rw [hcb] at hpm
  rcases hpm with h1 | h1 <;> norm_num at h1

end ThetLogos
