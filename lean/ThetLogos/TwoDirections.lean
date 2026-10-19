import Mathlib.Tactic
import ThetLogos.ThermalKernel

open Matrix Finset

namespace ThetLogos

/-!
# ThetLogos.TwoDirections — the two directions of a heat kernel's spectrum (Tiers T1/T2)

Origin (Jeff, 2026-10-19): "gravity and matter one way light and
heat the other?" — a proposed pairing of the world into two
directions. Gauntlet verdict the same day:

- **NO-GO as a physical partition.** Gravity bends light; heat
  conducts through matter; the two columns interconvert (a star is
  the two directions in continuous exchange). No theorem of this
  corpus will state a physical separation of gravity/matter from
  light/heat, and none does.
- **FIT as the spectral dichotomy of a finite heat kernel.** What
  the pairing's skeleton actually is, mathematically, stands
  proved below: under the diagonal heat kernel of `ThermalKernel`,
  a nonnegative generator's spectrum splits into exactly two
  directions —

  - **the gathered column**: modes with `lam i = 0`, whose
    schedules are identically `1` — conserved at every time,
    never dispersed;
  - **the dispersing column**: modes with `0 < lam i`, whose
    schedules decay exponentially, with the slowest dispersal set
    by the smallest positive rate — the gap.

  The trace of the kernel is the exact sum of the two columns:
  a time-independent count of gathered modes plus the sum of the
  dispersing schedules (`heatKernel_trace_dichotomy`), and a mode
  is gathered **iff** its schedule never disperses
  (`exp_neg_mul_forall_eq_one_iff`).

## Fences (what this module does NOT claim)

- Finite level, **diagonal-generator case only**, building on
  `ThermalKernel`. The general Hermitian-generator reduction is
  the same named remainder shared by `ResonanceSpectrum`,
  `SpectralClock`, and `ThermalKernel`; it is not attempted here.
- This packages the spectral dichotomy only. It contains no
  gravity, no light, no continuum limit, and no physical claim;
  the words "gathered" and "dispersing" name the two parts of a
  finite spectrum, nothing more.
- `t` is the modular/thermal parameter, as in `ThermalKernel`.

Tier map:
- T2: nothing new — the kernel is `ThermalKernel.heatKernel`.
- T1 (proved): everything below.
-/

-- ============================================================================
-- §1. The gathered column: zero modes are conserved
-- ============================================================================

section TwoDirections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Zero-mode conservation** (Tier T1 — proved): a mode with
    rate zero never decays — its schedule stands at `1` at every
    time. The gathered column is exactly conserved. -/
theorem heatKernel_diag_eq_one_of_eq_zero (lam : ι → ℝ) (t : ℝ) {i : ι}
    (hi : lam i = 0) : heatKernel lam t i i = 1 := by
  rw [heatKernel_apply_diag, hi]
  simp

/-- **A gathered mode is gathered at the level of schedules**
    (Tier T1 — proved): if `lam i = 0` then the mode's exponential
    schedule is identically `1` in `t`. -/
theorem exp_neg_mul_eq_one_of_eq_zero (lam : ι → ℝ) {i : ι} (hi : lam i = 0)
    (t : ℝ) : Real.exp (-t * lam i) = 1 := by
  rw [hi]
  simp

-- ============================================================================
-- §2. The dispersing column: positive modes decay, at the gap's rate
-- ============================================================================

/-- **Positive modes disperse, weakly** (Tier T1 — proved): a mode
    with positive rate has schedule at most `1` at every
    nonnegative time. -/
theorem heatKernel_diag_le_one_of_pos (lam : ι → ℝ) {i : ι}
    (hi : 0 < lam i) {t : ℝ} (ht : 0 ≤ t) : heatKernel lam t i i ≤ 1 := by
  rw [heatKernel_apply_diag, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hi.le

/-- **Positive modes disperse, strictly** (Tier T1 — proved): a
    mode with positive rate has schedule strictly below `1` at
    every positive time — dispersal is real, not an inequality
    artifact. -/
theorem heatKernel_diag_lt_one_of_pos (lam : ι → ℝ) {i : ι}
    (hi : 0 < lam i) {t : ℝ} (ht : 0 < t) : heatKernel lam t i i < 1 := by
  rw [heatKernel_apply_diag, Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hi

/-- **The gap-rate bound** (Tier T1 — proved): no mode disperses
    slower than the exponential at any lower rate bound `g`. With
    `g` the smallest positive rate, every dispersing schedule is
    at most `exp(−t·g)` — the gap sets the slowest dispersal. -/
theorem heatKernel_diag_le_exp_neg_mul_of_le (lam : ι → ℝ) {i : ι}
    {g : ℝ} (hg : g ≤ lam i) {t : ℝ} (ht : 0 ≤ t) :
    heatKernel lam t i i ≤ Real.exp (-t * g) := by
  rw [heatKernel_apply_diag]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr ht))

-- ============================================================================
-- §3. The trace dichotomy: the two columns exhaust the trace
-- ============================================================================

/-- **The trace dichotomy** (Tier T1 — proved): the trace of the
    heat kernel of a nonnegative generator is exactly the gathered
    column plus the dispersing column — the count of zero modes
    (a literal cardinality, independent of `t`) plus the sum of
    the positive modes' schedules. -/
theorem heatKernel_trace_dichotomy (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) :
    Matrix.trace (heatKernel lam t)
      = ((Finset.univ.filter (fun i => lam i = 0)).card : ℝ)
        + ∑ i ∈ Finset.univ.filter (fun i => 0 < lam i),
            Real.exp (-t * lam i) := by
  have hfil : Finset.univ.filter (fun i => ¬ lam i = 0)
      = Finset.univ.filter (fun i => 0 < lam i) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      rcases (hlam i).eq_or_lt with h0 | hpos
      · exact absurd h0.symm h
      · exact hpos
    · intro hpos h0
      rw [h0] at hpos
      exact lt_irrefl 0 hpos
  have hzero : ∑ i ∈ Finset.univ.filter (fun i => lam i = 0),
        Real.exp (-t * lam i)
      = ((Finset.univ.filter (fun i => lam i = 0)).card : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun i hi => by
      rw [Finset.mem_filter] at hi
      rw [hi.2]
      simp)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [heatKernel_trace,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => lam i = 0)
      (fun i => Real.exp (-t * lam i)), hfil, hzero]

/-- **The gathered contribution is a constant** (Tier T1 — proved):
    removing the zero-mode count from the trace leaves exactly
    the dispersing column — the gathered part of the trace is a
    literal, `t`-independent cardinality. -/
theorem heatKernel_trace_sub_card (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) :
    Matrix.trace (heatKernel lam t)
        - ((Finset.univ.filter (fun i => lam i = 0)).card : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < lam i),
          Real.exp (-t * lam i) := by
  rw [heatKernel_trace_dichotomy lam hlam t, add_sub_cancel_left]

-- ============================================================================
-- §4. The iff headline: gathered ⇔ never disperses
-- ============================================================================

/-- **Gathered ⇔ never disperses** (Tier T1 — proved): for a
    nonnegative rate, a mode's schedule is identically `1` at all
    times if and only if the mode's rate is zero. The two columns
    of the dichotomy are characterized mode by mode: conservation
    and zero rate are the same fact. -/
theorem exp_neg_mul_forall_eq_one_iff (lam : ι → ℝ) {i : ι}
    (hi0 : 0 ≤ lam i) :
    (∀ t : ℝ, Real.exp (-t * lam i) = 1) ↔ lam i = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [Real.exp_eq_one_iff] at h1
    linarith
  · intro h t
    exact exp_neg_mul_eq_one_of_eq_zero lam h t

end TwoDirections

end ThetLogos
