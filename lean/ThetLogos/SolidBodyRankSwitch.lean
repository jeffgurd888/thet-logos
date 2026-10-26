import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import ThetLogos.SolidBody

/-!
# ThetLogos.SolidBodyRankSwitch — the frozen rank-crossing switch

Brick 2 of the variable-intermediate-axis program (scoping memo
`varaxis-scoping-2026-10-26.md` §B; ledger item 9), built on the
`SolidBody` foundation. Abstract body only.

## What is proved (T1, from the foundation's definitions)

Fix a designated labeled axis `k` and let `i, j` be the other two
axes, ordered so that `(i, j, k)` is cyclic in the foundation's Euler
convention (`ω̇ᵢ = ((Iⱼ − Iₖ)/Iᵢ)·ωⱼ·ωₖ`). For a spin `Ω` held on
axis `k`, the FROZEN linearization in `(δωᵢ, δωⱼ)` is

  `δω̇ᵢ = ((Iⱼ − Iₖ)/Iᵢ)·Ω · δωⱼ`,   `δω̇ⱼ = ((Iₖ − Iᵢ)/Iⱼ)·Ω · δωᵢ`,

and its type is controlled by the off-diagonal product

  `qₖ = Ω² · (Iⱼ − Iₖ)(Iₖ − Iᵢ) / (Iᵢ · Iⱼ)`        (`rankQ` below).

The exact sign theorem (all three cases, all three labeled axes):

* `qₖ > 0` iff `Iₖ` lies strictly between `Iᵢ` and `Iⱼ`
  (intermediate: hyperbolic / growing);
* `qₖ = 0` iff `Iₖ = Iᵢ` or `Iₖ = Iⱼ` (tie: degenerate);
* `qₖ < 0` iff `Iₖ` lies strictly outside the other two
  (extremal: elliptic / oscillatory).

Crossing corollary: along any continuous path of positive labeled
moments on which axis `k` passes from strictly intermediate to
strictly extremal, there is a crossing time at which `Iₖ` equals a
neighboring moment, and the frozen linearization changes type
across it (positive `qₖ` at the start, negative at the end).

## Fences

FROZEN coefficients only. This brick proves nothing about what a
trajectory does while the moments `I(t)` are actually changing —
that is Brick 3, a different (nonautonomous) model. No physical
body is modeled; in particular nothing here is about any planet.
NO CLAIM. Parts of any official statement closed by this file: 0.
-/

namespace ThetLogos

/-! ## The general-axis frozen linearization package -/

/-- Frozen linearization coefficient of `δωⱼ` in `δω̇ᵢ`, for spin
`Ω` held on axis `k`, with `(i, j, k)` cyclic:
`δω̇ᵢ = linCoeffI Iᵢ Iⱼ Iₖ Ω · δωⱼ`. -/
noncomputable def linCoeffI (Ii Ij Ik Ω : ℝ) : ℝ := ((Ij - Ik) / Ii) * Ω

/-- Frozen linearization coefficient of `δωᵢ` in `δω̇ⱼ`, for spin
`Ω` held on axis `k`, with `(i, j, k)` cyclic:
`δω̇ⱼ = linCoeffJ Iᵢ Iⱼ Iₖ Ω · δωᵢ`. -/
noncomputable def linCoeffJ (Ii Ij Ik Ω : ℝ) : ℝ := ((Ik - Ii) / Ij) * Ω

/-- The un-normalized core of the off-diagonal product:
`(Iⱼ − Iₖ)(Iₖ − Iᵢ)`. Its sign is the sign of `rankQ` whenever the
moments `Iᵢ, Iⱼ` are positive and `Ω ≠ 0`. -/
def rankCore (Ii Ij Ik : ℝ) : ℝ := (Ij - Ik) * (Ik - Ii)

/-- The off-diagonal product controlling the frozen linearization's
type: `qₖ = Ω² · (Iⱼ − Iₖ)(Iₖ − Iᵢ) / (Iᵢ · Iⱼ)`. -/
noncomputable def rankQ (Ii Ij Ik Ω : ℝ) : ℝ :=
  Ω ^ 2 * ((Ij - Ik) * (Ik - Ii)) / (Ii * Ij)

/-- `rankQ` in factored form: a scalar multiple of `rankCore`. -/
theorem rankQ_eq_factor_mul_core (Ii Ij Ik Ω : ℝ) :
    rankQ Ii Ij Ik Ω = (Ω ^ 2 / (Ii * Ij)) * rankCore Ii Ij Ik := by
  unfold rankQ rankCore
  ring

/-- `rankQ` is the product of the two frozen linearization
coefficients: `qₖ = linCoeffI · linCoeffJ`. -/
theorem rankQ_eq_linCoeffI_mul_linCoeffJ (Ii Ij Ik Ω : ℝ)
    (hIi : Ii ≠ 0) (hIj : Ij ≠ 0) :
    rankQ Ii Ij Ik Ω = linCoeffI Ii Ij Ik Ω * linCoeffJ Ii Ij Ik Ω := by
  unfold rankQ linCoeffI linCoeffJ
  field_simp

/-! ## The sign of the core — pure order facts, no hypotheses -/

/-- The core is positive iff `Iₖ` lies strictly between `Iᵢ` and
`Iⱼ`. -/
theorem rankCore_pos_iff (Ii Ij Ik : ℝ) :
    0 < rankCore Ii Ij Ik ↔
      (Ii < Ik ∧ Ik < Ij) ∨ (Ij < Ik ∧ Ik < Ii) := by
  unfold rankCore
  rw [mul_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- The core vanishes iff `Iₖ` ties with a neighboring moment. -/
theorem rankCore_eq_zero_iff (Ii Ij Ik : ℝ) :
    rankCore Ii Ij Ik = 0 ↔ Ik = Ii ∨ Ik = Ij := by
  unfold rankCore
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr (eq_of_sub_eq_zero h).symm
    · exact Or.inl (eq_of_sub_eq_zero h)
  · rintro (h | h)
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (by rw [h]; ring)

/-- The core is negative iff `Iₖ` lies strictly outside the other
two moments (below both or above both). -/
theorem rankCore_neg_iff (Ii Ij Ik : ℝ) :
    rankCore Ii Ij Ik < 0 ↔
      (Ik < Ii ∧ Ik < Ij) ∨ (Ii < Ik ∧ Ij < Ik) := by
  unfold rankCore
  rw [mul_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

/-! ## The sign of `qₖ` — transfer through the positive factor -/

/-- The scalar factor `Ω² / (Iᵢ · Iⱼ)` is strictly positive when
`Iᵢ, Iⱼ > 0` and `Ω ≠ 0`, so `rankQ` has exactly the sign of
`rankCore`. -/
theorem rankQ_pos_iff (Ii Ij Ik Ω : ℝ) (hIi : 0 < Ii) (hIj : 0 < Ij)
    (hΩ : Ω ≠ 0) :
    0 < rankQ Ii Ij Ik Ω ↔
      (Ii < Ik ∧ Ik < Ij) ∨ (Ij < Ik ∧ Ik < Ii) := by
  have hfac : 0 < Ω ^ 2 / (Ii * Ij) :=
    div_pos (sq_pos_of_ne_zero hΩ) (mul_pos hIi hIj)
  rw [rankQ_eq_factor_mul_core, mul_pos_iff_of_pos_left hfac]
  exact rankCore_pos_iff Ii Ij Ik

/-- `qₖ = 0` iff `Iₖ` ties with a neighboring moment. -/
theorem rankQ_eq_zero_iff (Ii Ij Ik Ω : ℝ) (hIi : 0 < Ii)
    (hIj : 0 < Ij) (hΩ : Ω ≠ 0) :
    rankQ Ii Ij Ik Ω = 0 ↔ Ik = Ii ∨ Ik = Ij := by
  have hfac : Ω ^ 2 / (Ii * Ij) ≠ 0 :=
    ne_of_gt (div_pos (sq_pos_of_ne_zero hΩ) (mul_pos hIi hIj))
  rw [rankQ_eq_factor_mul_core, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hfac
    · exact (rankCore_eq_zero_iff Ii Ij Ik).mp h
  · intro h
    exact Or.inr ((rankCore_eq_zero_iff Ii Ij Ik).mpr h)

/-- `qₖ < 0` iff `Iₖ` lies strictly outside the other two moments. -/
theorem rankQ_neg_iff (Ii Ij Ik Ω : ℝ) (hIi : 0 < Ii) (hIj : 0 < Ij)
    (hΩ : Ω ≠ 0) :
    rankQ Ii Ij Ik Ω < 0 ↔
      (Ik < Ii ∧ Ik < Ij) ∨ (Ii < Ik ∧ Ij < Ik) := by
  have hfac : 0 < Ω ^ 2 / (Ii * Ij) :=
    div_pos (sq_pos_of_ne_zero hΩ) (mul_pos hIi hIj)
  rw [rankQ_eq_factor_mul_core]
  constructor
  · intro h
    have hcore : rankCore Ii Ij Ik < 0 := by
      rcases lt_or_ge (rankCore Ii Ij Ik) 0 with h' | h'
      · exact h'
      · exact absurd h (not_lt.mpr (mul_nonneg hfac.le h'))
    exact (rankCore_neg_iff Ii Ij Ik).mp hcore
  · intro h
    exact mul_neg_of_pos_of_neg hfac ((rankCore_neg_iff Ii Ij Ik).mpr h)

/-! ## The three labeled axes of a solid body

Cyclic assignment, following the foundation's Euler convention.
For spin on axis `0` (moment `I₁`), the transverse pair `(i, j)` is
`(1, 2)`, i.e. `(Iᵢ, Iⱼ, Iₖ) = (I₂, I₃, I₁)`; for spin on axis `1`,
`(Iᵢ, Iⱼ, Iₖ) = (I₃, I₁, I₂)`; for spin on axis `2`,
`(Iᵢ, Iⱼ, Iₖ) = (I₁, I₂, I₃)`. -/

/-- `qₖ` for spin held on axis `0` (moment `I₁`). -/
noncomputable def rankQAxis0 (b : SolidBody) (Ω : ℝ) : ℝ :=
  rankQ b.I2 b.I3 b.I1 Ω

/-- `qₖ` for spin held on axis `1` (moment `I₂`). -/
noncomputable def rankQAxis1 (b : SolidBody) (Ω : ℝ) : ℝ :=
  rankQ b.I3 b.I1 b.I2 Ω

/-- `qₖ` for spin held on axis `2` (moment `I₃`). -/
noncomputable def rankQAxis2 (b : SolidBody) (Ω : ℝ) : ℝ :=
  rankQ b.I1 b.I2 b.I3 Ω

/-- Axis `0`: `qₖ > 0` iff `I₁` lies strictly between `I₂` and
`I₃`. -/
theorem rankQAxis0_pos_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    0 < rankQAxis0 b Ω ↔
      (b.I2 < b.I1 ∧ b.I1 < b.I3) ∨ (b.I3 < b.I1 ∧ b.I1 < b.I2) :=
  rankQ_pos_iff b.I2 b.I3 b.I1 Ω b.I2_pos b.I3_pos hΩ

/-- Axis `0`: `qₖ = 0` iff `I₁` ties with a neighboring moment. -/
theorem rankQAxis0_eq_zero_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    rankQAxis0 b Ω = 0 ↔ b.I1 = b.I2 ∨ b.I1 = b.I3 :=
  rankQ_eq_zero_iff b.I2 b.I3 b.I1 Ω b.I2_pos b.I3_pos hΩ

/-- Axis `0`: `qₖ < 0` iff `I₁` lies strictly outside the other
two moments. -/
theorem rankQAxis0_neg_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    rankQAxis0 b Ω < 0 ↔
      (b.I1 < b.I2 ∧ b.I1 < b.I3) ∨ (b.I2 < b.I1 ∧ b.I3 < b.I1) :=
  rankQ_neg_iff b.I2 b.I3 b.I1 Ω b.I2_pos b.I3_pos hΩ

/-- Axis `1`: `qₖ > 0` iff `I₂` lies strictly between `I₁` and
`I₃` — the intermediate-axis seat of the foundation. -/
theorem rankQAxis1_pos_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    0 < rankQAxis1 b Ω ↔
      (b.I3 < b.I2 ∧ b.I2 < b.I1) ∨ (b.I1 < b.I2 ∧ b.I2 < b.I3) :=
  rankQ_pos_iff b.I3 b.I1 b.I2 Ω b.I3_pos b.I1_pos hΩ

/-- Axis `1`: `qₖ = 0` iff `I₂` ties with a neighboring moment. -/
theorem rankQAxis1_eq_zero_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    rankQAxis1 b Ω = 0 ↔ b.I2 = b.I3 ∨ b.I2 = b.I1 :=
  rankQ_eq_zero_iff b.I3 b.I1 b.I2 Ω b.I3_pos b.I1_pos hΩ

/-- Axis `1`: `qₖ < 0` iff `I₂` lies strictly outside the other
two moments. -/
theorem rankQAxis1_neg_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    rankQAxis1 b Ω < 0 ↔
      (b.I2 < b.I3 ∧ b.I2 < b.I1) ∨ (b.I3 < b.I2 ∧ b.I1 < b.I2) :=
  rankQ_neg_iff b.I3 b.I1 b.I2 Ω b.I3_pos b.I1_pos hΩ

/-- Axis `2`: `qₖ > 0` iff `I₃` lies strictly between `I₁` and
`I₂`. -/
theorem rankQAxis2_pos_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    0 < rankQAxis2 b Ω ↔
      (b.I1 < b.I3 ∧ b.I3 < b.I2) ∨ (b.I2 < b.I3 ∧ b.I3 < b.I1) :=
  rankQ_pos_iff b.I1 b.I2 b.I3 Ω b.I1_pos b.I2_pos hΩ

/-- Axis `2`: `qₖ = 0` iff `I₃` ties with a neighboring moment. -/
theorem rankQAxis2_eq_zero_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    rankQAxis2 b Ω = 0 ↔ b.I3 = b.I1 ∨ b.I3 = b.I2 :=
  rankQ_eq_zero_iff b.I1 b.I2 b.I3 Ω b.I1_pos b.I2_pos hΩ

/-- Axis `2`: `qₖ < 0` iff `I₃` lies strictly outside the other
two moments — the maximum-axis seat of the foundation (for
`I₁ < I₂ < I₃`) and the minimum-axis seat (for `I₃ < I₁ < I₂`). -/
theorem rankQAxis2_neg_iff (b : SolidBody) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    rankQAxis2 b Ω < 0 ↔
      (b.I3 < b.I1 ∧ b.I3 < b.I2) ∨ (b.I1 < b.I3 ∧ b.I2 < b.I3) :=
  rankQ_neg_iff b.I1 b.I2 b.I3 Ω b.I1_pos b.I2_pos hΩ

/-! ## Consistency with the foundation's two fixed seats

The foundation's intermediate seat (spin about axis `1`) uses the
coefficients `linCoeffA` (for `δω₀`) and `linCoeffB` (for `δω₂`).
In the present package's cyclic assignment for axis `1`,
`(i, j) = (2, 0)`: `linCoeffI` is the coefficient of `δω₀` in
`δω̇₂`, and `linCoeffJ` is the coefficient of `δω₂` in `δω̇₀`. -/

/-- At the axis-`1` seat, `linCoeffI` is the foundation's
`linCoeffB` — definitionally. -/
theorem linCoeffI_axis1 (b : SolidBody) (Ω : ℝ) :
    linCoeffI b.I3 b.I1 b.I2 Ω = linCoeffB b Ω := rfl

/-- At the axis-`1` seat, `linCoeffJ` is the foundation's
`linCoeffA` — definitionally. -/
theorem linCoeffJ_axis1 (b : SolidBody) (Ω : ℝ) :
    linCoeffJ b.I3 b.I1 b.I2 Ω = linCoeffA b Ω := rfl

/-- At the axis-`1` seat, `qₖ` is the foundation's coefficient
product `linCoeffA · linCoeffB` — the quantity whose square root
is the growth rate `γ` (`growthRate_sq`). -/
theorem rankQAxis1_eq_linCoeffA_mul_linCoeffB (b : SolidBody)
    (Ω : ℝ) :
    rankQAxis1 b Ω = linCoeffA b Ω * linCoeffB b Ω := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  rw [rankQAxis1, rankQ_eq_linCoeffI_mul_linCoeffJ _ _ _ _ h3 h1,
    linCoeffI_axis1, linCoeffJ_axis1, mul_comm]

/-- At the axis-`2` seat, `linCoeffI` is the foundation's
`linCoeffA` — definitionally. -/
theorem linCoeffI_axis2 (b : SolidBody) (Ω : ℝ) :
    linCoeffI b.I1 b.I2 b.I3 Ω = linCoeffA b Ω := rfl

/-- At the axis-`2` seat, `linCoeffJ` is the foundation's
`stabCoeffB` — definitionally. -/
theorem linCoeffJ_axis2 (b : SolidBody) (Ω : ℝ) :
    linCoeffJ b.I1 b.I2 b.I3 Ω = stabCoeffB b Ω := rfl

/-- At the axis-`2` seat, `qₖ = linCoeffA · stabCoeffB` — the
product the foundation's `stableRate_sq` identifies as `−ν²`. -/
theorem rankQAxis2_eq_linCoeffA_mul_stabCoeffB (b : SolidBody)
    (Ω : ℝ) :
    rankQAxis2 b Ω = linCoeffA b Ω * stabCoeffB b Ω := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  rw [rankQAxis2, rankQ_eq_linCoeffI_mul_linCoeffJ _ _ _ _ h1 h2,
    linCoeffI_axis2, linCoeffJ_axis2]

/-- At the maximum-axis seat (`I₁ < I₂ < I₃`, spin on axis `2`),
`qₖ = −ν² ≤ 0`: the frozen linearization is elliptic, matching
`rankQAxis2_neg_iff`. -/
theorem rankQAxis2_eq_neg_stableRate_sq (b : SolidBody) (Ω : ℝ)
    (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) :
    rankQAxis2 b Ω = -(stableRate b Ω) ^ 2 := by
  rw [rankQAxis2_eq_linCoeffA_mul_stabCoeffB,
    stableRate_sq b Ω h12 h23]
  ring

/-! ## The crossing corollary

A statement about a *path of frozen problems*, one per instant —
not about any trajectory of a body with changing moments. -/

/-- The frozen product `qₖ` evaluated along a path of labeled
moments `t ↦ (Iᵢ t, Iⱼ t, Iₖ t)`. -/
noncomputable def rankQPath (Ii Ij Ik : ℝ → ℝ) (Ω : ℝ) (t : ℝ) :
    ℝ :=
  rankQ (Ii t) (Ij t) (Ik t) Ω

/-- **Rank-crossing switch.** Along a continuous path of positive
labeled moments on `[0, 1]` on which the designated axis `k`
passes from strictly intermediate (at `t = 0`) to strictly
extremal (at `t = 1`), there is a crossing time at which `Iₖ`
equals a neighboring moment; the frozen product is positive at
the start and negative at the end — the frozen linearization
changes type across the crossing. -/
theorem rankQ_crossing (Ii Ij Ik : ℝ → ℝ) (Ω : ℝ) (hΩ : Ω ≠ 0)
    (hIi : Continuous Ii) (hIj : Continuous Ij)
    (hIk : Continuous Ik)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < Ii t ∧ 0 < Ij t ∧ 0 < Ik t)
    (hstart : (Ii 0 < Ik 0 ∧ Ik 0 < Ij 0) ∨
      (Ij 0 < Ik 0 ∧ Ik 0 < Ii 0))
    (hend : (Ik 1 < Ii 1 ∧ Ik 1 < Ij 1) ∨
      (Ii 1 < Ik 1 ∧ Ij 1 < Ik 1)) :
    (∃ t ∈ Set.Icc (0 : ℝ) 1, Ik t = Ii t ∨ Ik t = Ij t) ∧
      0 < rankQPath Ii Ij Ik Ω 0 ∧
      rankQPath Ii Ij Ik Ω 1 < 0 := by
  have hfun : rankQPath Ii Ij Ik Ω =
      fun t => Ω ^ 2 * ((Ij t - Ik t) * (Ik t - Ii t)) /
        (Ii t * Ij t) := by
    funext t
    rfl
  have hcont : ContinuousOn (rankQPath Ii Ij Ik Ω) (Set.Icc 0 1) := by
    rw [hfun]
    apply ContinuousOn.div
    · exact (by fun_prop : Continuous
        fun t => Ω ^ 2 * ((Ij t - Ik t) * (Ik t - Ii t))).continuousOn
    · exact (by fun_prop : Continuous
        fun t => Ii t * Ij t).continuousOn
    · intro t ht
      exact mul_ne_zero (ne_of_gt (hpos t ht).1)
        (ne_of_gt (hpos t ht).2.1)
  have hp0 := hpos 0 (Set.left_mem_Icc.mpr zero_le_one)
  have hp1 := hpos 1 (Set.right_mem_Icc.mpr zero_le_one)
  have hq0 : 0 < rankQPath Ii Ij Ik Ω 0 :=
    (rankQ_pos_iff _ _ _ _ hp0.1 hp0.2.1 hΩ).mpr hstart
  have hq1 : rankQPath Ii Ij Ik Ω 1 < 0 :=
    (rankQ_neg_iff _ _ _ _ hp1.1 hp1.2.1 hΩ).mpr hend
  have hmem : (0 : ℝ) ∈ Set.Icc (rankQPath Ii Ij Ik Ω 1)
      (rankQPath Ii Ij Ik Ω 0) := ⟨hq1.le, hq0.le⟩
  obtain ⟨t, ht, hqt⟩ :=
    intermediate_value_Icc' zero_le_one hcont hmem
  refine ⟨⟨t, ht, ?_⟩, hq0, hq1⟩
  exact (rankQ_eq_zero_iff _ _ _ _ (hpos t ht).1 (hpos t ht).2.1
    hΩ).mp hqt

/-- An affine combination of two positive reals stays positive on
`[0, 1]`. -/
theorem affineCombo_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1 - t) * A + t * B := by
  obtain ⟨ht0, ht1⟩ := ht
  have h3 : (1 - t) * (min A B) + t * (min A B) ≤
      (1 - t) * A + t * B :=
    add_le_add
      (mul_le_mul_of_nonneg_left (min_le_left A B)
        (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (min_le_right A B) ht0)
  have h4 : (1 - t) * (min A B) + t * (min A B) = min A B := by
    ring
  have h5 : 0 < min A B := lt_min hA hB
  linarith

/-- The crossing corollary for the affine path family
`I(t) = (1 − t)·A + t·B` between two moment triples: if axis `k`
is strictly intermediate at `A` and strictly extremal at `B`,
some affine interpolant has `Iₖ` tied with a neighbor. -/
theorem rankQ_crossing_affine (AIi AIj AIk BIi BIj BIk Ω : ℝ)
    (hΩ : Ω ≠ 0)
    (hA : 0 < AIi ∧ 0 < AIj ∧ 0 < AIk)
    (hB : 0 < BIi ∧ 0 < BIj ∧ 0 < BIk)
    (hstart : (AIi < AIk ∧ AIk < AIj) ∨
      (AIj < AIk ∧ AIk < AIi))
    (hend : (BIk < BIi ∧ BIk < BIj) ∨
      (BIi < BIk ∧ BIj < BIk)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) * AIk + t * BIk = (1 - t) * AIi + t * BIi ∨
      (1 - t) * AIk + t * BIk = (1 - t) * AIj + t * BIj := by
  obtain ⟨⟨t, ht, hteq⟩, -, -⟩ := rankQ_crossing
    (fun t => (1 - t) * AIi + t * BIi)
    (fun t => (1 - t) * AIj + t * BIj)
    (fun t => (1 - t) * AIk + t * BIk) Ω hΩ
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun t ht => ⟨affineCombo_pos hA.1 hB.1 ht,
      affineCombo_pos hA.2.1 hB.2.1 ht,
      affineCombo_pos hA.2.2 hB.2.2 ht⟩)
    (by simpa using hstart) (by simpa using hend)
  exact ⟨t, ht, hteq⟩

end ThetLogos
