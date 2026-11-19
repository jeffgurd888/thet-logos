import Mathlib.Tactic
import ThetLogos.PhaseRingSteps

/-!
# MV-2 SPLIT BRICK — PhaseRingRelaxStep (brick 2 of 5)

Split of the MV-2 draft module `ThetLogos.PhaseRingRelax`
(29 declarations) under the BRICK CAP law (Zero,
2026-11-11 21:37 EST; ~10 new declarations per build
invocation, banked per brick). Statements and proofs
are carried VERBATIM from the repaired draft
(mv2 @ 2456faf); the split moves text across module
seams only — no statement moved, no proof rewritten.
All declarations keep namespace
`ThetLogos.PhaseRingRelax`, so every full name is
unchanged. The design document lives in the header
of brick 1 (`ThetLogos.PhaseRingSteps`) and in
STATUS-MV2.md.

Contents of this brick: the relaxation step `relaxStep` and its step law, winding keeper, iteration keeper, and slip law (1 def + 5 theorems). Builds on brick 1.

Dial-ineligible; NO CLAIM; dials 0/4.
-/


namespace ThetLogos
namespace PhaseRingRelax

open PhaseWinding

variable {n : ℕ}

/-! ## The relaxation step -/

/-- The **relaxation step** on lifts: every bond step
relaxes toward the mean step by the fraction `ε` of
its deviation; the lift is rebuilt from its relaxed
steps, anchored at the old `Θ 0`, the wrap bond taking
the relaxed last step, the winding carried unchanged —
and the closing holds because the relaxed steps still
sum to `2π * w` (`sum_relaxGStep`): a no-slip step by
construction, with the conservation proved again on
the face at `relaxStep_winding`. -/
noncomputable def relaxStep (L : Lift n) (ε : ℝ) : Lift n where
  Θ := fun k => L.Θ 0 + ∑ j ∈ Finset.range k.val, relaxGStep L ε j
  wrap := relaxGStep L ε n
  w := L.w
  closing := by
    show (L.Θ 0 + ∑ j ∈ Finset.range ((Fin.last n).val), relaxGStep L ε j)
        - (L.Θ 0 + ∑ j ∈ Finset.range ((0 : Fin (n + 1)).val),
            relaxGStep L ε j)
        + relaxGStep L ε n
      = 2 * Real.pi * ((L.w : ℤ) : ℝ)
    rw [Fin.val_last]
    simp only [Fin.val_zero, Finset.range_zero, Finset.sum_empty,
      add_zero]
    have hsum : ∑ j ∈ Finset.range n, relaxGStep L ε j
        + relaxGStep L ε n = 2 * Real.pi * (L.w : ℝ) := by
      rw [← Finset.sum_range_succ]
      exact sum_relaxGStep L ε
    linarith [hsum]

/-- The phases of the relaxed lift, read back: partial
sums of the relaxed steps from the anchor. -/
theorem relaxStep_Θ (L : Lift n) (ε : ℝ) (k : Fin (n + 1)) :
    (relaxStep L ε).Θ k
      = L.Θ 0 + ∑ j ∈ Finset.range k.val, relaxGStep L ε j :=
  rfl

/-- **The step law:** every bond of the relaxed lift —
the seam included — steps by the old step relaxed
toward the mean. -/
theorem relaxStep_step (L : Lift n) (ε : ℝ) (k : Fin (n + 1)) :
    (relaxStep L ε).step k
      = L.step k - ε * (L.step k - stepMean L) := by
  by_cases hk : k = Fin.last n
  · subst hk
    rw [Lift.step_last, Lift.step_last]
    have hg : L.gstep n = L.wrap := if_pos rfl
    show L.gstep n - ε * (L.gstep n - stepMean L)
        = L.wrap - ε * (L.wrap - stepMean L)
    rw [hg]
  · have hrg : relaxGStep L ε k.val
        = L.step k - ε * (L.step k - stepMean L) := by
      show L.gstep k.val - ε * (L.gstep k.val - stepMean L)
          = L.step k - ε * (L.step k - stepMean L)
      rw [← step_eq_gstep L k]
    rw [Lift.step_of_ne_last _ hk, relaxStep_Θ, relaxStep_Θ,
      coe_cyc_of_ne_last hk, Finset.sum_range_succ]
    linarith [hrg]

/-- **The keeper:** the relaxation does not move the
winding — at any step size, by construction and now by
proof. -/
theorem relaxStep_winding (L : Lift n) (ε : ℝ) :
    (relaxStep L ε).winding = L.winding :=
  rfl

/-- The keeper under iteration: any number of
relaxation steps leaves the winding where it was. -/
theorem relaxStep_iterate_winding (L : Lift n) (ε : ℝ) (m : ℕ) :
    ((fun L' : Lift n => relaxStep L' ε)^[m] L).winding
      = L.winding := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', relaxStep_winding, ih]

/-- **Changed exactly by slips:** a slip of size `s`
applied after any relaxation lands the winding at
exactly `w + s` — the landed slip law
(`Lift.winding_slipShift`) composed with the keeper.
The order is the true one: a slip changes the
step-sum, so a relaxation after a slip relaxes toward
the NEW mean; no reverse-order law is claimed. -/
theorem slipShift_relaxStep_winding (L : Lift n) (ε : ℝ)
    (α : Fin (n + 1) → ℝ) (αw : ℝ) (s : ℤ)
    (hs : αw - α 0 = 2 * Real.pi * (s : ℝ)) :
    ((relaxStep L ε).slipShift α αw s hs).winding
      = L.winding + s := by
  rw [Lift.winding_slipShift, relaxStep_winding]


end PhaseRingRelax
end ThetLogos
