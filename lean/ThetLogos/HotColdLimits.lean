/-
# HotColdLimits — the two limiting channels, at the diagonal seat

**Commissioned by Zero, 2026-11-13 ("full open and
build" → "open the gates"), from his hot–cold geometric
principle (2026-11-13 16:55) and the operators framing
(17:38: "two operators of heat hot and cold"); scope:
~/workspace/your_files/hot-cold-limits-pin-scope-2026-11-13.md.
NO CLAIM. Dial-ineligible.**

THE CLAIM BEING CARDED (finite, seat-bound): the two
limiting channels of the finite Gibbs state are
ASYMMETRIC operators, not twin states:
- HOT channel (β → 0): the state washes to uniform —
  structure dissolves.
- COLD channel (β large): the state concentrates on
  the spectral floor — excited weight dies like
  e^(−βΔ) (the GAPFLOOR-1 shape).

This module is the theorem companion to COLD-0
(`ColdHeatDualityPin`), which filed the design lines
and the target forms; here the diagonal-seat content
is proved, against the corpus's own weight idiom
(`coldWeight` / `coldPartition`) and `gibbsForm`
(`PartnerThermal`).

FENCES (the scope's, carded): the channels are
LIMITING CHANNELS (maps on states), not substances;
neither is an absence — cold is a floor, not a void.
Kills armed: K-HOTCOLD-CONT (any continuum-limit
reading = FRONTIER, unpriced), K-HOTCOLD-PHYS (no
physical heat engine is claimed). The GAPFLOOR-1
citation: the general Hermitian-seat floor bound is
`GibbsGapFloor`'s (landed 2026-11-12, lane grade); that
module is not in this branch's ancestry, so its shape
is cited here by name and PROVED at this diagonal
seat, not imported — the GapLine precedent.

STATUS: STATUS-HOTCOLD.md.
-/

import Mathlib
import ThetLogos.PartnerThermal
import ThetLogos.ColdHeatDualityPin

namespace ThetLogos

variable {N : ℕ} [NeZero N]

/-! ## §1 — the two limiting states -/

/-- **The hot state**: the uniform diagonal state —
every mode carries weight `1/N`. Independent of the
generator: this is what any Gibbs state washes to at
the hot end. -/
noncomputable def hotState : Matrix (Fin N) (Fin N) ℂ :=
  (N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- **The cold state** at a chosen mode `i₀`: the point
mass on that mode — the diagonal state with all weight
on `i₀`. (At the cold end the Gibbs state concentrates
on the ground modes; with a ground index chosen, this
is the limit shape.) -/
def coldState (E : Fin N → ℝ) (i₀ : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => if i = i₀ then (1 : ℂ) else 0)

/-! ## §2 — the hot end: β = 0 washes to uniform -/

/-- **H-1 (the scope's theorem 1):** at `β = 0` the
Gibbs form of the diagonal generator is the hot state
— uniformity at the hot end, diagonal seat. (The
computation uses nothing about the generator: at
`β = 0` the Gibbs exponential is `1` and its trace is
the mode count. The seat is stated as scoped.) -/
theorem gibbsForm_diagonal_zero (E : Fin N → ℝ) :
    gibbsForm (Matrix.diagonal fun i => (E i : ℂ)) 0
      = hotState := by
  simp [gibbsForm, hotState, Matrix.trace_one]

/-! ## §3 — the cold end: weights concentrate on the floor -/

/-- The partition sum is positive (the corpus's
`GibbsSpan.gibbsSum_pos`, restated for `coldPartition`,
which is that sum). -/
theorem coldPartition_pos (β : ℝ) (E : Fin N → ℝ) :
    0 < coldPartition β E :=
  GibbsSpan.gibbsSum_pos β E

/-- The weight unfolding: `coldWeight` is the Boltzmann
factor over the partition sum. -/
theorem coldWeight_eq (β : ℝ) (E : Fin N → ℝ) (j : Fin N) :
    coldWeight β E j
      = Real.exp (-(β * E j)) / coldPartition β E := by
  have hZ : 0 < coldPartition β E := coldPartition_pos β E
  simp only [coldWeight, GibbsSpan.gibbsWeightsE]
  rw [show (-(β * E j + Real.log (coldPartition β E)))
        = (-(β * E j)) - Real.log (coldPartition β E) by ring,
    Real.exp_sub, Real.exp_log hZ]

/-- **H-2 (the scope's theorem 2):** the ground mode's
weight is monotone in `β` — as it gets colder the
floor only gains. (Via the reciprocal form: the weight
is `1 / ∑ᵢ e^{−β(Eᵢ − E_{i₀})}`, a reciprocal of a sum
of terms each antitone in `β`.) -/
theorem coldWeight_ground_mono {E : Fin N → ℝ} {i₀ : Fin N}
    (hi₀ : ∀ i, E i₀ ≤ E i) {β₁ β₂ : ℝ} (hβ : β₁ ≤ β₂) :
    coldWeight β₁ E i₀ ≤ coldWeight β₂ E i₀ := by
  -- The comparison sum `S β = ∑ i, exp (−β (E i − E i₀))`.
  set S : ℝ → ℝ := fun β => ∑ i, Real.exp (-(β * (E i - E i₀)))
    with hS
  have hSpos : ∀ β, 0 < S β :=
    fun β => Finset.sum_pos (fun i _ => Real.exp_pos _)
      Finset.univ_nonempty
  have hSantitone : S β₂ ≤ S β₁ := by
    apply Finset.sum_le_sum
    intro i _
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right hβ
    exact sub_nonneg.mpr (hi₀ i)
  -- Each cold weight is the reciprocal of its `S`.
  have hform : ∀ β, coldWeight β E i₀ = (S β)⁻¹ := by
    intro β
    rw [coldWeight_eq]
    have hZfact : coldPartition β E
        = Real.exp (-(β * E i₀)) * S β := by
      rw [hS, coldPartition, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hZfact]
    have he : Real.exp (-(β * E i₀)) ≠ 0 := Real.exp_ne_zero _
    have hS' : S β ≠ 0 := (hSpos β).ne'
    field_simp
  rw [hform β₁, hform β₂]
  exact (inv_le_inv₀ (hSpos β₁) (hSpos β₂)).mpr hSantitone

/-- **H-3a (the scope's theorem 3, per-mode):** every
mode's weight is at most the gap-floor factor of its
own height above the ground mode — the GAPFLOOR-1
shape at the diagonal seat (the general Hermitian
form is `GibbsGapFloor`'s, cited on this module's
face). No sign condition on `β` is needed: the bound
is the partition sum dominating its ground term. -/
theorem coldWeight_le_exp_neg_gap {E : Fin N → ℝ}
    {i₀ : Fin N} (β : ℝ) (i : Fin N) :
    coldWeight β E i ≤ Real.exp (-(β * (E i - E i₀))) := by
  rw [coldWeight_eq]
  have hterm : Real.exp (-(β * E i₀)) ≤ coldPartition β E := by
    show Real.exp (-(β * E i₀)) ≤ ∑ j, Real.exp (-(β * E j))
    exact Finset.single_le_sum
      (f := fun j => Real.exp (-(β * E j)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i₀)
  have hcalc : Real.exp (-(β * E i)) / coldPartition β E
      ≤ Real.exp (-(β * E i)) / Real.exp (-(β * E i₀)) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le
      (Real.exp_pos _) hterm
  refine le_trans hcalc ?_
  have harg : (-(β * E i)) - (-(β * E i₀))
      = -(β * (E i - E i₀)) := by ring
  rw [← Real.exp_sub, harg]

/-- **H-3b (the scope's theorem 3, total form):** the
total off-ground weight is at most `(N − 1) · e^{−βΔ}`
wherever `Δ` undercuts every excited height — excited
weight dies like `e^{−βΔ}` (the GAPFLOOR-1 shape). -/
theorem offGround_weight_le {E : Fin N → ℝ} {i₀ : Fin N}
    (hi₀ : ∀ i, E i₀ ≤ E i) {β Δ : ℝ} (hβ : 0 ≤ β)
    (hΔ : ∀ i, i ≠ i₀ → Δ ≤ E i - E i₀) :
    ∑ i ∈ Finset.univ \ {i₀}, coldWeight β E i
      ≤ (N - 1 : ℝ) * Real.exp (-(β * Δ)) := by
  have hcard : (Finset.univ \ {i₀} : Finset (Fin N)).card
      = N - 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, Finset.card_singleton]
  calc ∑ i ∈ Finset.univ \ {i₀}, coldWeight β E i
      ≤ ∑ i ∈ Finset.univ \ {i₀}, Real.exp (-(β * Δ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi₀' : i ≠ i₀ :=
          fun h => (Finset.mem_sdiff.mp hi).2
            (Finset.mem_singleton.mpr h)
        exact le_trans (coldWeight_le_exp_neg_gap β i)
          (Real.exp_le_exp.mpr (neg_le_neg
            (mul_le_mul_of_nonneg_left (hΔ i hi₀') hβ)))
    _ = (N - 1 : ℝ) * Real.exp (-(β * Δ)) := by
        have hN1 : 1 ≤ N :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) i₀.2)
        rw [Finset.sum_const, hcard, nsmul_eq_mul,
          Nat.cast_sub hN1, Nat.cast_one]

/-! ## §4 — the two ends are genuinely different -/

/-- **H-4 (the scope's theorem 4):** when the spectrum
has a second distinct level above the ground mode, the
hot state and the cold state are different operators —
uniformity and the point mass are not the same end. -/
theorem hotState_ne_coldState {E : Fin N → ℝ} {i₀ : Fin N}
    (h2 : ∃ i, E i ≠ E i₀) : hotState ≠ coldState E i₀ := by
  obtain ⟨i, hi⟩ := h2
  have hi₀' : i ≠ i₀ := fun h => hi (h ▸ rfl)
  have hN : (N : ℂ) ≠ 0 := by
    have h0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i₀.2
    exact_mod_cast h0.ne'
  intro h
  have happ := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i i) h
  simp only [hotState, coldState, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.diagonal_apply_eq, if_neg hi₀'] at happ
  exact inv_ne_zero hN happ

end ThetLogos
