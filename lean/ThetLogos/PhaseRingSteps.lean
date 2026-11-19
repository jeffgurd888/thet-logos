import Mathlib.Tactic
import ThetLogos.PhaseWinding
import ThetLogos.WindingRing

/-!
# ThetLogos.PhaseRingRelax — phase-ring relaxation: a keeper, a monotone, twisted equilibria (MV-2, DRAFT)

STATUS: **DRAFT — UNVERDICTED** (lane thet-logos-og0, branch
mv2, drafted 2026-11-11). No build has arbitrated this file.
Design record: `STATUS-MV2.md` in the lane root (the design
fork — step-relaxation taken, site-phase gradient step
rejected with its reason — is priced there in the open).
Charter: `monotonicity-vortex-equilibrium-scope-2026-11-08.md`
§3(b) + §4 (MV-2: band M–L, est. 12–22 strict) + §5.
Pre-registered DIAL-INELIGIBLE. Dial 2 = 0 on every outcome.
NO CLAIM.

## What this brick is

The phase-ring half of the MV stack's finite analogue
(§3 verdict (b)): on `PhaseWinding` lifts — real site
phases on a ring of `n + 1` sites, a closing `wrap`, the
winding `w : ℤ` carried as data — this brick builds the
three roles, kept apart on the face (MV-0 charter):

- **The keeper: the winding.** A discrete relaxation step
  on the lift's bond steps conserves `w` exactly
  (`relaxStep_winding`, and under iteration), and the
  winding changes ONLY through the seam, by exactly the
  slip: a slip of size `s` after any relaxation has
  winding `w + s` (`slipShift_relaxStep_winding`, the
  landed `PhaseWinding` slip law T3 composed with the
  invariance; the same law at the integer-tick seat is
  `WindingRing.winding_slip`, cited, not re-proved).
- **The monotone: the lift Dirichlet energy**
  `liftEnergy L = ∑ k, (L.step k)^2` over ALL bonds, the
  seam bond included. Under the relaxation step with
  step-size `ε ∈ [0, 1]` it obeys the exact identity
  `E' = (1−ε)² (E − B) + B`, where `B = (n+1) · m²` is
  the fixed-winding floor and `m = 2π w / (n+1)` the
  mean bond step — hence `E' ≤ E`
  (`liftEnergy_relaxStep`, `liftEnergy_relaxStep_le`).
  The bound `ε ≤ 1` is the stability bound, on the
  face — the FA-3 shape named in the scoping.
- **The equilibria: the uniform twists.** At fixed
  winding the energy floor `B` is attained exactly by
  the lifts whose every bond steps by the mean
  (`liftEnergy_eq_iff`), and those are exactly the
  relaxation's fixed points (`relaxStep_fixed_iff`).
  They exist at EVERY winding: `uniformLift w` — at
  `w ≠ 0` a ring at equilibrium still carries its
  winding. Rest without unwinding. The landed Fourier
  lift is one of them (`fourierLift_isUniformTwist`).

## The step, and the fork it came from

`relaxStep L ε` replaces every bond step `s` by
`s − ε (s − m)`: steps relax toward their own mean,
and the mean is the winding's (the summed closing
equation `Lift.sum_step`: `∑ k, L.step k = 2π w`), so
the step-sum — hence the closing, hence `w` — is
untouched by construction and proved conserved on the
face. The new lift is rebuilt from its relaxed steps,
anchored at `L.Θ 0`, the wrap bond taking the relaxed
last step.

The naive alternative — an Euler step of the
cycle-graph Laplacian on the site phases, wrap
absorbing the seam — was REJECTED at design (priced in
STATUS-MV2.md): its Lyapunov function is the chain
energy with the seam excluded, and its rest states are
the seam-concentrated lifts (`Θ` constant,
`wrap = 2π w`), not the uniform twists this exhibit
exists to characterize. It is not built here and not
silently substituted.

## Fences

- NOT the polar vortex, not weather, not the
  atmosphere, not a fluid (K-MV-PROXY / K-MV-ATMOS
  armed over any such telling). A finite ring of
  phases with a keeper, a monotone, and twisted
  equilibria.
- Roles separated (K-MV-CONFLATE armed): the winding
  is conserved and never monotone; the energy is
  antitone under the step and never conserved;
  equilibrium is the characterized state, not a
  quantity. No dial moves (K-MV-DIAL standing).
- Route B (principal-argument winding) remains
  unbuilt, as in `PhaseWinding`. The winding here is
  the lift's, as there.
-/

namespace ThetLogos
namespace PhaseRingRelax

open PhaseWinding

variable {n : ℕ}

/-! ## SPLIT NOTE (2026-11-11, brick-cap law)

This module is BRICK 1 of the MV-2 split. The draft
module `ThetLogos.PhaseRingRelax` (29 declarations)
was split at drafting time into five sequential
modules along its section seams, per the BRICK CAP
law (Zero, 2026-11-11 21:37 EST): `PhaseRingSteps`
(9, this brick) → `PhaseRingRelaxStep` (6) →
`PhaseRingEnergy` (4) → `PhaseRingUniform` (7) →
`PhaseRingRelaxEnergy` (3). Statements and proofs
are carried verbatim from the repaired draft
(mv2 @ 2456faf); all declarations keep namespace
`ThetLogos.PhaseRingRelax`, so every full name is
unchanged. Banked per brick: build → olean verified
on disk → commit → next brick. The monolith file is
removed on the split branch (mv2split); its text
survives entire across the five bricks (name set and
body verified identical at split time). -/

/-! ## The mean step and the energy -/

/-- The **mean bond step** of a lift: the summed closing
equation (`Lift.sum_step`) forces the steps to average
`2π * w / (n + 1)`. This is the winding, read as a
per-bond share — the relaxation's target. -/
noncomputable def stepMean (L : Lift n) : ℝ :=
  2 * Real.pi * (L.w : ℝ) / ((n : ℝ) + 1)

/-- The relaxed bond steps, ℕ-indexed (the `gstep`
indexing: index `n` is the wrap bond). Each step moves
toward the mean by the fraction `ε` of its deviation. -/
noncomputable def relaxGStep (L : Lift n) (ε : ℝ) (j : ℕ) : ℝ :=
  L.gstep j - ε * (L.gstep j - stepMean L)

/-- The **lift Dirichlet energy**: the sum of squared
bond steps over ALL bonds of the lift, the seam bond
included. The exhibit's monotone. -/
def liftEnergy (L : Lift n) : ℝ :=
  ∑ k, (L.step k) ^ 2

/-- The **equilibrium predicate**: every bond of the
lift steps by exactly the mean — the uniformly twisted
configuration at the lift's own winding. -/
def IsUniformTwist (L : Lift n) : Prop :=
  ∀ k, L.step k = stepMean L

/-! ## Step bookkeeping helpers -/

/-- The `Fin`-indexed steps are the `gstep`s read along
the ring (the local step of `Lift.sum_step`'s proof,
exported for this brick's use). -/
theorem step_eq_gstep (L : Lift n) (k : Fin (n + 1)) :
    L.step k = L.gstep (k : ℕ) := by
  by_cases hk : k = Fin.last n
  · subst hk
    show L.step (Fin.last n)
        = (if ((Fin.last n : Fin (n + 1)) : ℕ) = n then L.wrap
            else L.phaseSeq ((Fin.last n).val + 1) - L.phaseSeq (Fin.last n).val)
    rw [Lift.step_last, Fin.val_last]
    exact (if_pos rfl).symm
  · have hval : (k : ℕ) ≠ n := by
      intro h
      apply hk
      exact Fin.ext (by rw [Fin.val_last]; exact h)
    have h1 : L.phaseSeq (k.val + 1) = L.Θ (cyc k) := by
      rw [Lift.phaseSeq_apply L (k.val + 1) (by omega)]
      congr 1
      exact Fin.ext (by rw [coe_cyc_of_ne_last hk])
    have h2 : L.phaseSeq k.val = L.Θ k := by
      rw [Lift.phaseSeq_apply L k.val k.isLt]
    show L.step k
        = (if (k : ℕ) = n then L.wrap
            else L.phaseSeq (k.val + 1) - L.phaseSeq k.val)
    rw [Lift.step_of_ne_last L hk, if_neg hval, h1, h2]

/-- The `gstep`s around the ring sum to `2π * w`: the
summed closing equation in ℕ-indexed form. -/
theorem sum_gstep (L : Lift n) :
    ∑ j ∈ Finset.range (n + 1), L.gstep j
      = 2 * Real.pi * (L.w : ℝ) := by
  calc ∑ j ∈ Finset.range (n + 1), L.gstep j
      = ∑ k : Fin (n + 1), L.gstep (k : ℕ) :=
        (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ k, L.step k :=
        Finset.sum_congr rfl fun k _ => (step_eq_gstep L k).symm
    _ = 2 * Real.pi * (L.w : ℝ) := L.sum_step

/-- The mean step, multiplied back up: `(n + 1)` mean
steps are exactly the total `2π * w`. -/
theorem stepMean_mul_card (L : Lift n) :
    ((n : ℝ) + 1) * stepMean L = 2 * Real.pi * (L.w : ℝ) := by
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  show ((n : ℝ) + 1)
      * (2 * Real.pi * (L.w : ℝ) / ((n : ℝ) + 1))
      = 2 * Real.pi * (L.w : ℝ)
  field_simp

/-- The steps sum to `(n + 1)` mean steps: the summed
closing equation in mean form. -/
theorem sum_step_eq (L : Lift n) :
    ∑ k, L.step k = ((n : ℝ) + 1) * stepMean L := by
  calc ∑ k, L.step k = 2 * Real.pi * (L.w : ℝ) := L.sum_step
    _ = ((n : ℝ) + 1) * stepMean L := (stepMean_mul_card L).symm

/-- **The keeper at step level:** the relaxed steps
still sum to `2π * w` — relaxing every step toward the
mean does not move the total, because the deviations
from the mean sum to zero. This is what makes the
relaxation a no-slip step. -/
theorem sum_relaxGStep (L : Lift n) (ε : ℝ) :
    ∑ j ∈ Finset.range (n + 1), relaxGStep L ε j
      = 2 * Real.pi * (L.w : ℝ) := by
  have hS : ∑ j ∈ Finset.range (n + 1), (L.gstep j - stepMean L)
      = ∑ j ∈ Finset.range (n + 1), L.gstep j
        - ((n : ℝ) + 1) * stepMean L := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    ring_nf
  calc ∑ j ∈ Finset.range (n + 1), relaxGStep L ε j
      = ∑ j ∈ Finset.range (n + 1), L.gstep j
          - ε * ∑ j ∈ Finset.range (n + 1), (L.gstep j - stepMean L) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => rfl
    _ = 2 * Real.pi * (L.w : ℝ) := by
        rw [hS, sum_gstep, stepMean_mul_card]
        ring


end PhaseRingRelax
end ThetLogos
