import Mathlib.Tactic
import ThetLogos.FluxTwist

/-!
# ThetLogos.PhaseWinding — phase winding on a finite ring, counted by an integer (T1 target, cabinet)

STATUS: STANDS WHOLE (T1), landed 2026-10-22 (parent-verified:
in-tree build green, axiom check standard-only). Commissioned by
Jeff 2026-10-22 ("Commission the winding brick (lift-first, A)").
Charter:
`writings/phase-winding-brick-charter-draft-2026-10-21.md`.
Anchor: `ThetLogos.FluxTwist` (imported, not modified).

## What this brick is

The finite, honest atom underneath vortex talk: **phase winding
around a ring of `n + 1` sites, counted by an integer.** NO CLAIM,
cabinet tier: not a Yang–Mills rung, no credit toward Δ.

## Encoding (charter route A, lift-first)

A configuration *is* a lift `Lift n`:

- `Θ : Fin (n + 1) → ℝ`, the real phase at each site (the physical
  phase at site `k` is `FluxTwist.phaseOf (Θ k) = exp (i Θ k)`);
- `wrap : ℝ`, the closing increment: the phase step along the last
  bond, from the last site back around to site `0`;
- `w : ℤ`, the winding number;
- the closing equation `Θ (last) − Θ 0 + wrap = 2π * w`: traversing
  the ring from site `0` — along the chain bonds, then the wrap
  bond — returns to `Θ 0 + 2π * w`, the same physical phase, lifted
  by `2π * w`.

The winding number is part of the lift's data — that is route A's
known cost, stated on the charter and repeated here: `w` is a
property of the *lift*, and the bridge to "winding is a property of
the phase configuration itself" is route B (principal argument),
which is OUT OF SCOPE for this brick and is not built here. The data
is not free, though: `Lift.winding_unique` proves that `(Θ, wrap)`
determine `w`, so one lift cannot carry two winding numbers.

## What is proved

- **T1 — Compound = sum.** Pointwise addition of lifts adds
  windings (`Lift.winding_add`; the arbitrary-lift form is
  `Lift.winding_add_of_eq`).
- **T2 — Gauge invariance.** Shifting by a single-valued site
  function `α` changes every bond step by `α (cyc k) − α k` — the
  wrap bond included, since `cyc (last) = 0` — and leaves the
  summed steps, and hence `w`, unchanged (`Lift.step_gaugeShift`,
  `Lift.sum_step_gaugeShift`, `Lift.winding_gaugeShift`). Global
  phase rotation is the constant-`α` corollary
  (`Lift.step_gaugeShift_const`).
- **T3 — Phase slip = the only door.** A shift whose wrap value
  `αw` disagrees with the site value `α 0` by `αw − α 0 = 2π * s`
  changes `w` by exactly `s` (`Lift.winding_slipShift`; the master
  form `Lift.winding_shift_eq` covers *any* lift obtained from `L`
  by such a shift). Stated as algebra — NOT as a continuity or
  phase-transition claim.
- **T4 — FluxTwist bridge.** At flux `θ = 0` the Fourier phase
  configuration `k ↦ 2π * m * k / (n + 1)` is a lift (`fourierLift`)
  whose every bond steps by `2π * m / (n + 1)` and whose winding is
  exactly the mode index `m` (`fourierLift_winding`,
  `fourierLift_step`); its site phases are the arguments of
  FluxTwist's `fourierVec m`, which equals `twistedFourierVec 0 m`
  (`fourierLift_phase`, `fourierVec_eq_twistedFourierVec_zero`),
  the eigenvector of `twistedShift_mulVec_twistedFourierVec`. At
  general `θ` the total around the ring is `θ + 2π * m`
  (`fourierPhase_total`) — not `2π` times an integer — and any lift
  carrying the general-`θ` phases satisfies `θ = 2π * (w − m)`
  (`eq_two_pi_mul_sub_of_fourier_lift`): the flux sits as a
  fractional offset of the winding, on the face.

## Fences

- NOT an Abrikosov vortex: no manifold, no order-parameter field,
  no core. This brick proves the winding atom a vortex carries; it
  is never captioned as a vortex.
- No knots (a phase on a ring has no crossing data), no strings, no
  tension, no thermal/acoustic content, no simultaneity-triad
  claim.
- Route B (principal-argument winding from a unit-modulus
  configuration) is NOT built.
- Conventions: sites `Fin (n + 1)`; `Real.pi` explicit, no local
  π binding (per the FluxTwist dossier's engineering note).
-/

namespace ThetLogos
namespace PhaseWinding

variable {n : ℕ}

/-- Telescoping sum over a range: the increments of a real sequence
along a chain sum to the endpoint difference. -/
theorem range_telescope (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (f (j + 1) - f j) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- A **lift** (charter route A): real site phases `Θ`, a wrap
increment `wrap` closing the ring, and the winding number `w : ℤ`,
bound by the closing equation: traversing the ring from site `0`
returns to `Θ 0 + 2π * w`. -/
structure Lift (n : ℕ) where
  Θ : Fin (n + 1) → ℝ
  wrap : ℝ
  w : ℤ
  closing : Θ (Fin.last n) - Θ 0 + wrap = 2 * Real.pi * (w : ℝ)

namespace Lift

/-- The winding number of a lift. -/
def winding (L : Lift n) : ℤ := L.w

/-- The winding number is determined by the phase data: two winding
numbers for the same `(Θ, wrap)` agree — the closing equation pins
`w`, since `2π ≠ 0`. -/
theorem winding_unique {Θ : Fin (n + 1) → ℝ} {wrap : ℝ} {w₁ w₂ : ℤ}
    (h₁ : Θ (Fin.last n) - Θ 0 + wrap = 2 * Real.pi * (w₁ : ℝ))
    (h₂ : Θ (Fin.last n) - Θ 0 + wrap = 2 * Real.pi * (w₂ : ℝ)) :
    w₁ = w₂ := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have key : (2 * Real.pi) * (w₁ : ℝ) = (2 * Real.pi) * (w₂ : ℝ) := by
    rw [← h₁, ← h₂]
  have hcast : (w₁ : ℝ) = (w₂ : ℝ) := mul_left_cancel₀ hpi key
  exact_mod_cast hcast

/-- Two lifts with the same phases and the same wrap have the same
winding. -/
theorem winding_eq_of_eq {L M : Lift n} (hΘ : M.Θ = L.Θ) (hwrap : M.wrap = L.wrap) :
    M.winding = L.winding := by
  have hM : L.Θ (Fin.last n) - L.Θ 0 + L.wrap = 2 * Real.pi * (M.w : ℝ) := by
    rw [← hΘ, ← hwrap]
    exact M.closing
  exact winding_unique hM L.closing

/-! ## T1: compound = sum -/

/-- Pointwise addition of lifts: phases add, wrap increments add,
windings add. The closing check is the two closing equations added —
algebra, as chartered. -/
def add (L M : Lift n) : Lift n where
  Θ := L.Θ + M.Θ
  wrap := L.wrap + M.wrap
  w := L.w + M.w
  closing := by
    simp only [Pi.add_apply, Int.cast_add]
    linarith [L.closing, M.closing]

/-- **T1 (compound = sum):** winding adds under pointwise addition
of lifts: `w(Θ + Φ) = w(Θ) + w(Φ)` in ℤ — nothing tangles, nothing
hides. -/
theorem winding_add (L M : Lift n) :
    (L.add M).winding = L.winding + M.winding := rfl

/-- T1, arbitrary-lift form: any lift whose phases and wrap are the
pointwise sums of two lifts' has the sum winding. -/
theorem winding_add_of_eq (L M L' : Lift n)
    (hΘ : L'.Θ = L.Θ + M.Θ) (hwrap : L'.wrap = L.wrap + M.wrap) :
    L'.winding = L.winding + M.winding := by
  have hsum : (L.Θ + M.Θ) (Fin.last n) - (L.Θ + M.Θ) 0 + (L.wrap + M.wrap)
      = 2 * Real.pi * ((L.w + M.w : ℤ) : ℝ) := by
    simp only [Pi.add_apply, Int.cast_add]
    linarith [L.closing, M.closing]
  have hL' : (L.Θ + M.Θ) (Fin.last n) - (L.Θ + M.Θ) 0 + (L.wrap + M.wrap)
      = 2 * Real.pi * (L'.w : ℝ) := by
    rw [← hΘ, ← hwrap]
    exact L'.closing
  show L'.w = L.w + M.w
  exact (winding_unique hsum hL').symm

/-! ## Bond steps and the summed closing equation -/

/-- The phase step along bond `k`: from site `k` to its cyclic
successor `cyc k` — except on the wrap bond `k = last`, where the
step is the lift's closing increment `wrap`. -/
def step (L : Lift n) (k : Fin (n + 1)) : ℝ :=
  if k = Fin.last n then L.wrap else L.Θ (cyc k) - L.Θ k

theorem step_last (L : Lift n) : L.step (Fin.last n) = L.wrap := if_pos rfl

theorem step_of_ne_last (L : Lift n) {k : Fin (n + 1)} (hk : k ≠ Fin.last n) :
    L.step k = L.Θ (cyc k) - L.Θ k := if_neg hk

/-- The site phases read off as a ℕ-sequence (zero off the ring):
the auxiliary for the summed closing equation. -/
def phaseSeq (L : Lift n) : ℕ → ℝ :=
  fun j => if h : j < n + 1 then L.Θ ⟨j, h⟩ else 0

theorem phaseSeq_apply (L : Lift n) (j : ℕ) (h : j < n + 1) :
    L.phaseSeq j = L.Θ ⟨j, h⟩ := dif_pos h

theorem phaseSeq_zero (L : Lift n) : L.phaseSeq 0 = L.Θ 0 := by
  rw [phaseSeq_apply L 0 (Nat.succ_pos n)]
  congr 1

theorem phaseSeq_last (L : Lift n) : L.phaseSeq n = L.Θ (Fin.last n) := by
  rw [phaseSeq_apply L n (Nat.lt_succ_self n)]
  congr 1

/-- The bond steps read off along the ℕ-indexing of the ring:
index `n` is the wrap bond. Auxiliary for `sum_step`. -/
def gstep (L : Lift n) (j : ℕ) : ℝ :=
  if j = n then L.wrap else L.phaseSeq (j + 1) - L.phaseSeq j

/-- The summed bond steps around the ring are exactly `2π * w`:
the closing equation in summed form — chain increments telescope
to `Θ (last) − Θ 0`, and the wrap bond contributes `wrap`. -/
theorem sum_step (L : Lift n) : ∑ k, L.step k = 2 * Real.pi * (L.w : ℝ) := by
  have hstep : ∀ k : Fin (n + 1), L.step k = L.gstep (k : ℕ) := by
    intro k
    by_cases hk : k = Fin.last n
    · subst hk
      show L.step (Fin.last n)
          = (if ((Fin.last n : Fin (n + 1)) : ℕ) = n then L.wrap
              else L.phaseSeq ((Fin.last n).val + 1) - L.phaseSeq (Fin.last n).val)
      rw [step_last, Fin.val_last]
      exact (if_pos rfl).symm
    · have hval : (k : ℕ) ≠ n := by
        intro h
        apply hk
        exact Fin.ext (by rw [Fin.val_last]; exact h)
      have hlt : (k : ℕ) < n :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hval
      have h1 : L.phaseSeq (k.val + 1) = L.Θ (cyc k) := by
        rw [phaseSeq_apply L (k.val + 1) (by omega)]
        congr 1
        exact Fin.ext (by rw [coe_cyc_of_ne_last hk])
      have h2 : L.phaseSeq k.val = L.Θ k := by
        rw [phaseSeq_apply L k.val k.isLt]
      show L.step k
          = (if (k : ℕ) = n then L.wrap
              else L.phaseSeq (k.val + 1) - L.phaseSeq k.val)
      rw [step_of_ne_last L hk, if_neg hval, h1, h2]
  calc ∑ k, L.step k
      = ∑ k : Fin (n + 1), L.gstep (k : ℕ) :=
        Finset.sum_congr rfl fun k _ => hstep k
    _ = ∑ j ∈ Finset.range (n + 1), L.gstep j :=
        Fin.sum_univ_eq_sum_range _ _
    _ = (∑ j ∈ Finset.range n, (L.phaseSeq (j + 1) - L.phaseSeq j))
          + L.wrap := by
        rw [Finset.sum_range_succ]
        congr 1
        · exact Finset.sum_congr rfl fun j hj =>
            if_neg (by have hj' := Finset.mem_range.mp hj; omega)
        · exact if_pos rfl
    _ = (L.phaseSeq n - L.phaseSeq 0) + L.wrap := by rw [range_telescope]
    _ = (L.Θ (Fin.last n) - L.Θ 0) + L.wrap := by
        rw [phaseSeq_last, phaseSeq_zero]
    _ = 2 * Real.pi * (L.w : ℝ) := L.closing

/-! ## T2: gauge invariance -/

/-- The gauge shift of a lift by a single-valued site function
`α : Fin (n + 1) → ℝ`: phases shift by `α`; the wrap increment
absorbs the seam difference `α 0 − α (last)`. That `α` is a genuine
function on the ring *is* the single-valuedness of charter T2. -/
def gaugeShift (L : Lift n) (α : Fin (n + 1) → ℝ) : Lift n where
  Θ := L.Θ + α
  wrap := L.wrap + α 0 - α (Fin.last n)
  w := L.w
  closing := by
    simp only [Pi.add_apply]
    linarith [L.closing]

/-- **T2 (gauge invariance):** a single-valued shift does not move
the winding. -/
theorem winding_gaugeShift (L : Lift n) (α : Fin (n + 1) → ℝ) :
    (L.gaugeShift α).winding = L.winding := rfl

/-- T2 at the bonds: every step of the gauge-shifted lift is the
old step plus `α (cyc k) − α k` — the wrap bond included, since
`cyc (last) = 0`, so its adjustment `α 0 − α (last)` has the same
form. -/
theorem step_gaugeShift (L : Lift n) (α : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    (L.gaugeShift α).step k = L.step k + (α (cyc k) - α k) := by
  by_cases hk : k = Fin.last n
  · subst hk
    rw [step_last, step_last, cyc_last]
    show L.wrap + α 0 - α (Fin.last n) = L.wrap + (α 0 - α (Fin.last n))
    ring
  · rw [step_of_ne_last (L.gaugeShift α) hk, step_of_ne_last L hk]
    show (L.Θ + α) (cyc k) - (L.Θ + α) k
        = L.Θ (cyc k) - L.Θ k + (α (cyc k) - α k)
    simp only [Pi.add_apply]
    ring

/-- T2, summed form: the total step around the ring is unchanged by
a gauge shift — the `α (cyc k) − α k` contributions cancel around
the ring, each site value appearing once with each sign because
`cyc` is a permutation. -/
theorem sum_step_gaugeShift (L : Lift n) (α : Fin (n + 1) → ℝ) :
    ∑ k, (L.gaugeShift α).step k = ∑ k, L.step k := by
  calc ∑ k, (L.gaugeShift α).step k
      = ∑ k, (L.step k + (α (cyc k) - α k)) :=
        Finset.sum_congr rfl fun k _ => step_gaugeShift L α k
    _ = (∑ k, L.step k) + ∑ k, (α (cyc k) - α k) := Finset.sum_add_distrib
    _ = ∑ k, L.step k := by
        rw [Finset.sum_sub_distrib, Equiv.sum_comp cyc α]
        simp

/-- Global phase rotation (constant gauge shift) does not even
move the individual bond steps. -/
theorem step_gaugeShift_const (L : Lift n) (c : ℝ) (k : Fin (n + 1)) :
    (L.gaugeShift (fun _ => c)).step k = L.step k := by
  rw [step_gaugeShift]
  simp

/-! ## T3: phase slip = the only door -/

/-- The slip shift: a site shift by `α` whose wrap value `αw` is
allowed to disagree with the site value `α 0` at the seam. The
mismatch `αw − α 0 = 2π * s` is the phase slip. -/
def slipShift (L : Lift n) (α : Fin (n + 1) → ℝ) (αw : ℝ) (s : ℤ)
    (hs : αw - α 0 = 2 * Real.pi * (s : ℝ)) : Lift n where
  Θ := L.Θ + α
  wrap := L.wrap + αw - α (Fin.last n)
  w := L.w + s
  closing := by
    simp only [Pi.add_apply]
    push_cast
    linarith [L.closing, hs]

/-- **T3 (phase slip = the only door):** a shift with wrap
mismatch `2π * s` moves the winding by exactly `s`. -/
theorem winding_slipShift (L : Lift n) (α : Fin (n + 1) → ℝ) (αw : ℝ) (s : ℤ)
    (hs : αw - α 0 = 2 * Real.pi * (s : ℝ)) :
    (L.slipShift α αw s hs).winding = L.winding + s := rfl

/-- T3 at the ordinary bonds: away from the seam, a slip shift
changes steps exactly as a gauge shift does. -/
theorem step_slipShift_of_ne_last (L : Lift n) (α : Fin (n + 1) → ℝ)
    (αw : ℝ) (s : ℤ) (hs : αw - α 0 = 2 * Real.pi * (s : ℝ))
    {k : Fin (n + 1)} (hk : k ≠ Fin.last n) :
    (L.slipShift α αw s hs).step k = L.step k + (α (cyc k) - α k) := by
  rw [step_of_ne_last (L.slipShift α αw s hs) hk, step_of_ne_last L hk]
  show (L.Θ + α) (cyc k) - (L.Θ + α) k
      = L.Θ (cyc k) - L.Θ k + (α (cyc k) - α k)
  simp only [Pi.add_apply]
  ring

/-- T3 at the seam: the wrap step absorbs the full wrap value
`αw` — this is the one bond where a slip can enter. -/
theorem step_slipShift_last (L : Lift n) (α : Fin (n + 1) → ℝ)
    (αw : ℝ) (s : ℤ) (hs : αw - α 0 = 2 * Real.pi * (s : ℝ)) :
    (L.slipShift α αw s hs).step (Fin.last n)
      = L.step (Fin.last n) + (αw - α (Fin.last n)) := by
  rw [step_last, step_last]
  show L.wrap + αw - α (Fin.last n) = L.wrap + (αw - α (Fin.last n))
  ring

/-- **T3, master form — the "only" in "only door":** *any* lift
obtained from `L` by a site shift `α` plus a wrap adjustment whose
seam mismatch is `αw − α 0 = 2π * s` has winding exactly
`L.w + s`. Within shift-deformations, `w` moves only through the
seam mismatch, and by exactly the slip amount — algebra, not a
continuity claim. -/
theorem winding_shift_eq (L L' : Lift n) (α : Fin (n + 1) → ℝ) (αw : ℝ) (s : ℤ)
    (hΘ : L'.Θ = L.Θ + α) (hwrap : L'.wrap = L.wrap + αw - α (Fin.last n))
    (hs : αw - α 0 = 2 * Real.pi * (s : ℝ)) :
    L'.winding = L.winding + s := by
  have h' := L'.closing
  rw [hΘ, hwrap] at h'
  simp only [Pi.add_apply] at h'
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have key : (2 * Real.pi) * (L'.w : ℝ) = (2 * Real.pi) * ((L.w + s : ℤ) : ℝ) := by
    push_cast
    linarith [L.closing, hs, h']
  have hcast : (L'.w : ℝ) = ((L.w + s : ℤ) : ℝ) := mul_left_cancel₀ hpi key
  show L'.w = L.w + s
  exact_mod_cast hcast

/-- Any single-valued shift of any lift preserves its winding:
T2's content at the level of arbitrary lifts (the master form with
seam mismatch zero, forcing `s = 0`). -/
theorem winding_eq_of_gauge (L L' : Lift n) (α : Fin (n + 1) → ℝ)
    (hΘ : L'.Θ = L.Θ + α) (hwrap : L'.wrap = L.wrap + α 0 - α (Fin.last n)) :
    L'.winding = L.winding := by
  have hs : α 0 - α 0 = 2 * Real.pi * ((0 : ℤ) : ℝ) := by simp
  have h := winding_shift_eq L L' α (α 0) 0 hΘ hwrap hs
  simpa using h

end Lift

/-! ## T4: the FluxTwist bridge -/

/-- The general-flux Fourier phase function on the ring: site `k`
carries phase `(θ + 2π * m) * k / (n + 1)` — the arguments of
FluxTwist's `twistedFourierVec θ m`. -/
noncomputable def fourierPhase (θ : ℝ) (m : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun k => (θ + 2 * Real.pi * (m.val : ℝ)) * (k.val : ℝ) / ((n : ℝ) + 1)

/-- At general flux `θ`, traversing the ring under the Fourier
phases accumulates exactly `θ + 2π * m` (chain difference plus the
uniform closing step): `2π` times an integer only when `θ` is a
multiple of `2π` — stated, not hidden. -/
theorem fourierPhase_total (θ : ℝ) (m : Fin (n + 1)) :
    fourierPhase θ m (Fin.last n) - fourierPhase θ m 0
      + (θ + 2 * Real.pi * (m.val : ℝ)) / ((n : ℝ) + 1)
      = θ + 2 * Real.pi * (m.val : ℝ) := by
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  show (θ + 2 * Real.pi * (m.val : ℝ)) * ((Fin.last n).val : ℝ) / ((n : ℝ) + 1)
      - (θ + 2 * Real.pi * (m.val : ℝ)) * ((0 : Fin (n + 1)).val : ℝ)
        / ((n : ℝ) + 1)
      + (θ + 2 * Real.pi * (m.val : ℝ)) / ((n : ℝ) + 1)
      = θ + 2 * Real.pi * (m.val : ℝ)
  rw [Fin.val_last]
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, sub_zero]
  field_simp

/-- Any lift carrying the general-flux Fourier phases (with the
uniform closing step) has its flux pinned to its winding:
`θ = 2π * (w − m)`. At `θ = 0` this forces `w = m`; at `θ ≠ 0` the
flux is a fractional offset of the winding — the non-integrality
is on the face. -/
theorem eq_two_pi_mul_sub_of_fourier_lift {θ : ℝ} {m : Fin (n + 1)} (L : Lift n)
    (hΘ : L.Θ = fourierPhase θ m)
    (hwrap : L.wrap = (θ + 2 * Real.pi * (m.val : ℝ)) / ((n : ℝ) + 1)) :
    θ = 2 * Real.pi * ((L.w : ℝ) - (m.val : ℝ)) := by
  have h := L.closing
  rw [hΘ, hwrap, fourierPhase_total θ m] at h
  have h2 : 2 * Real.pi * ((L.w : ℝ) - (m.val : ℝ))
      = 2 * Real.pi * (L.w : ℝ) - 2 * Real.pi * (m.val : ℝ) := by ring
  rw [h2, ← h]
  ring

/-- **T4 (FluxTwist bridge):** the `θ = 0` Fourier phase
configuration as a lift: site phases `2π * m * k / (n + 1)`, the
uniform closing step, winding exactly the mode index `m`. -/
noncomputable def fourierLift (m : Fin (n + 1)) : Lift n where
  Θ := fun k => 2 * Real.pi * (m.val : ℝ) * (k.val : ℝ) / ((n : ℝ) + 1)
  wrap := 2 * Real.pi * (m.val : ℝ) / ((n : ℝ) + 1)
  w := (m.val : ℤ)
  closing := by
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    show (2 * Real.pi * (m.val : ℝ) * ((Fin.last n).val : ℝ) / ((n : ℝ) + 1))
        - (2 * Real.pi * (m.val : ℝ) * ((0 : Fin (n + 1)).val : ℝ)
          / ((n : ℝ) + 1))
        + (2 * Real.pi * (m.val : ℝ) / ((n : ℝ) + 1))
        = 2 * Real.pi * (((m.val : ℤ)) : ℝ)
    rw [Fin.val_last]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, sub_zero]
    push_cast
    field_simp

/-- T4: the winding of the `θ = 0` Fourier lift is exactly the
mode index `m` — the mode index in the standing FluxTwist module
*is* the winding number of its phase configuration. -/
theorem fourierLift_winding (m : Fin (n + 1)) :
    (fourierLift m).winding = (m.val : ℤ) := rfl

/-- T4: every bond of the Fourier lift steps by the same
`2π * m / (n + 1)` — the wrap bond included. -/
theorem fourierLift_step (m : Fin (n + 1)) (k : Fin (n + 1)) :
    (fourierLift m).step k = 2 * Real.pi * (m.val : ℝ) / ((n : ℝ) + 1) := by
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  by_cases hk : k = Fin.last n
  · subst hk
    exact Lift.step_last (fourierLift m)
  · rw [Lift.step_of_ne_last _ hk]
    show 2 * Real.pi * (m.val : ℝ) * ((cyc k).val : ℝ) / ((n : ℝ) + 1)
        - 2 * Real.pi * (m.val : ℝ) * (k.val : ℝ) / ((n : ℝ) + 1)
        = 2 * Real.pi * (m.val : ℝ) / ((n : ℝ) + 1)
    rw [coe_cyc_of_ne_last hk]
    push_cast
    field_simp
    ring

/-- T4: the site phases of the Fourier lift are exactly the
arguments of FluxTwist's `fourierVec m`. -/
theorem fourierLift_phase (m : Fin (n + 1)) (k : Fin (n + 1)) :
    fourierVec m k = phaseOf ((fourierLift m).Θ k) := rfl

/-- FluxTwist's plain Fourier vector is its twisted Fourier
vector at flux zero. -/
theorem fourierVec_eq_twistedFourierVec_zero (m : Fin (n + 1)) :
    fourierVec m = twistedFourierVec 0 m := by
  funext k
  show phaseOf (2 * Real.pi * (m.val : ℝ) * (k.val : ℝ) / ((n : ℝ) + 1))
      = phaseOf ((0 + 2 * Real.pi * (m.val : ℝ)) * (k.val : ℝ) / ((n : ℝ) + 1))
  congr 1
  ring

/-- T4, eigenphase form: the eigenphase angle of
`twistedFourierVec 0 m` under `twistedShift` — FluxTwist's
`twistedShift_mulVec_twistedFourierVec` at `θ = 0` — is the
uniform bond step of the Fourier lift: the ring hears winding
`m`. -/
theorem fourier_eigenphase_angle (m : Fin (n + 1)) (k : Fin (n + 1)) :
    (0 + 2 * Real.pi * (m.val : ℝ)) / ((n : ℝ) + 1)
      = (fourierLift m).step k := by
  rw [fourierLift_step, zero_add]

end PhaseWinding
end ThetLogos
