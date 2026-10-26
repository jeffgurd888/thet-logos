import Mathlib.Tactic
import ThetLogos.SolidBody

/-!
# ThetLogos.SolidBodyPolhode — N0: the polhode algebra package

Shared prerequisite N0 of the nonlinear rigid-body program
(scoping memo `nonlinear-rigid-scoping-2026-10-26.md` §0), built on
the `SolidBody` foundation. Fixed body, frozen coefficients,
abstract body only.

## What is proved (T1, from definitions/hypotheses; classical core T4)

For a body with `0 < I₁ < I₂ < I₃` and a momentum vector
`M : Fin 3 → ℝ` on the level set `𝒫_E` (`Σ Mᵢ² = Λ`,
`Σ Mᵢ²/Iᵢ = 2E`), the two constraints are linear in the squares
`(M₁², M₂², M₃²)`, so with `u := M₂²` each of `M₁²`, `M₃²` is an
affine function of `u`, with explicit coefficients (`m1SqOfU`,
`m3SqOfU`, factored as `slope • (root − u)`). At the separatrix
energy `E_sep = Λ/(2I₂)` both affine forms are proportional to
`(Λ − u)`, vanish exactly at `u = Λ`, and `M₁ = 0` on `𝒫_{E_sep}`
holds exactly at the saddles `M = (0, ±√Λ, 0)`. Endpoint values at
`u = 0` and at the maximal `u = min uRoot1 uRoot3` (per band) are
included, as are the two band definitions and the three levels.

## ⚠ Correction to the scoping memo (a finding, reported loudly)

The memo (§0) registers "`M₃²` affine **increasing** in `u`". That
is FALSE under the memo's own conventions: `M₃²` is affine
**decreasing** in `u`, exactly like `M₁²` — necessarily, since the
two slopes sum to `−1` (because `M₁² + u + M₃² = Λ`); here both
slopes are in `(−1, 0)` and sum (as the positive quantities
`slope1`, `slope3` below) to `1`. This module proves the true
version: both `m1SqOfU` and `m3SqOfU` are `StrictAnti` in `u`
(`m1SqOfU_strictAnti`, `m3SqOfU_strictAnti`). All other registered
§0 forms check out and are proved as registered.

## Fences

Prerequisite only: NO period, NO portrait/topology, NO dynamics is
claimed. NO CLAIM. Parts of any official (Clay) statement closed
by this file: 0.
-/

namespace ThetLogos

/-! ## Levels and bands -/

/-- The critical energy level of axis `k`: `Eₖ = Λ / (2·Iₖ)`, i.e.
`2Eₖ = Λ/Iₖ`, attained at the axis points `±√Λ·eₖ`. -/
noncomputable def levelEnergy (b : SolidBody) (Λ : ℝ) (k : Fin 3) : ℝ :=
  Λ / (2 * momInertia b k)

/-- The separatrix energy `E_sep = Λ / (2I₂)`, the middle level. -/
noncomputable def sepEnergy (b : SolidBody) (Λ : ℝ) : ℝ := Λ / (2 * b.I2)

theorem sepEnergy_eq_levelEnergy_one (b : SolidBody) (Λ : ℝ) :
    sepEnergy b Λ = levelEnergy b Λ 1 := rfl

theorem two_mul_levelEnergy (b : SolidBody) (Λ : ℝ) (k : Fin 3)
    (hk : momInertia b k ≠ 0) : 2 * levelEnergy b Λ k = Λ / momInertia b k := by
  unfold levelEnergy
  field_simp

/-- For `Λ > 0` the three levels are ordered
`E₂ (axis 2) < E_sep (axis 1) < E₀ (axis 0)`, matching
`Λ/I₁ > Λ/I₂ > Λ/I₃`. -/
theorem levelEnergy_order (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ) :
    levelEnergy b Λ 2 < levelEnergy b Λ 1 ∧
      levelEnergy b Λ 1 < levelEnergy b Λ 0 := by
  constructor
  · unfold levelEnergy
    simp only [momInertia_two, momInertia_one]
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) b.I3_pos)
      (mul_pos (by norm_num) b.I2_pos)]
    nlinarith [hΛ, h23, b.I2_pos]
  · unfold levelEnergy
    simp only [momInertia_one, momInertia_zero]
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) b.I2_pos)
      (mul_pos (by norm_num) b.I1_pos)]
    nlinarith [hΛ, h12, b.I1_pos]

/-- Top band: `Λ/I₂ < 2E < Λ/I₁` (the `M₁`-band, around `±√Λ·e₁`). -/
def inTopBand (b : SolidBody) (Λ E : ℝ) : Prop :=
  Λ / b.I2 < 2 * E ∧ 2 * E < Λ / b.I1

/-- Bottom band: `Λ/I₃ < 2E < Λ/I₂` (the `M₃`-band, around
`±√Λ·e₃`). -/
def inBotBand (b : SolidBody) (Λ E : ℝ) : Prop :=
  Λ / b.I3 < 2 * E ∧ 2 * E < Λ / b.I2

/-! ## The affine package -/

/-- The (positive) decay rate of `M₁²` in `u = M₂²`:
`slope1 = I₁(I₃−I₂) / (I₂(I₃−I₁)) ∈ (0, 1)`, and
`M₁² = intercept₁ − slope1 · u` on `𝒫_E`. -/
noncomputable def slope1 (b : SolidBody) : ℝ :=
  b.I1 * (b.I3 - b.I2) / (b.I2 * (b.I3 - b.I1))

/-- The (positive) decay rate of `M₃²` in `u = M₂²`:
`slope3 = I₃(I₂−I₁) / (I₂(I₃−I₁)) ∈ (0, 1)`, and
`M₃² = intercept₃ − slope3 · u` on `𝒫_E`. -/
noncomputable def slope3 (b : SolidBody) : ℝ :=
  b.I3 * (b.I2 - b.I1) / (b.I2 * (b.I3 - b.I1))

/-- `M₁²` as an affine function of `u = M₂²` on `𝒫_E`:
`m1SqOfU = (I₁I₂(2E·I₃−Λ) − I₁(I₃−I₂)·u) / (I₂(I₃−I₁))`. -/
noncomputable def m1SqOfU (b : SolidBody) (Λ E u : ℝ) : ℝ :=
  (b.I1 * b.I2 * (2 * E * b.I3 - Λ) - b.I1 * (b.I3 - b.I2) * u)
    / (b.I2 * (b.I3 - b.I1))

/-- `M₃²` as an affine function of `u = M₂²` on `𝒫_E`:
`m3SqOfU = (I₂I₃(Λ−2E·I₁) − I₃(I₂−I₁)·u) / (I₂(I₃−I₁))`. -/
noncomputable def m3SqOfU (b : SolidBody) (Λ E u : ℝ) : ℝ :=
  (b.I2 * b.I3 * (Λ - 2 * E * b.I1) - b.I3 * (b.I2 - b.I1) * u)
    / (b.I2 * (b.I3 - b.I1))

/-- The unique zero of `M₁²` as a function of `u`:
`uRoot1 = I₂(2E·I₃−Λ)/(I₃−I₂)`. -/
noncomputable def uRoot1 (b : SolidBody) (Λ E : ℝ) : ℝ :=
  b.I2 * (2 * E * b.I3 - Λ) / (b.I3 - b.I2)

/-- The unique zero of `M₃²` as a function of `u`:
`uRoot3 = I₂(Λ−2E·I₁)/(I₂−I₁)`. -/
noncomputable def uRoot3 (b : SolidBody) (Λ E : ℝ) : ℝ :=
  b.I2 * (Λ - 2 * E * b.I1) / (b.I2 - b.I1)

/-- The maximal feasible `u` for given `(E, Λ)`: the smaller of the
two roots (both affine factors must stay `≥ 0`). -/
noncomputable def uMax (b : SolidBody) (Λ E : ℝ) : ℝ :=
  min (uRoot1 b Λ E) (uRoot3 b Λ E)

theorem slope1_pos (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) :
    0 < slope1 b :=
  div_pos (mul_pos b.I1_pos (sub_pos.mpr h23))
    (mul_pos b.I2_pos (sub_pos.mpr (lt_trans h12 h23)))

theorem slope3_pos (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) :
    0 < slope3 b :=
  div_pos (mul_pos b.I3_pos (sub_pos.mpr h12))
    (mul_pos b.I2_pos (sub_pos.mpr (lt_trans h12 h23)))

/-- The two decay rates sum to `1` — the slope form of
`M₁² + u + M₃² = Λ`. -/
theorem slope1_add_slope3 (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) : slope1 b + slope3 b = 1 := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold slope1 slope3
  field_simp
  ring

/-- Factored form: `M₁² = slope1 · (uRoot1 − u)` as affine
functions. -/
theorem m1SqOfU_eq_slope1_mul (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E u : ℝ) :
    m1SqOfU b Λ E u = slope1 b * (uRoot1 b Λ E - u) := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  have h32 : b.I3 - b.I2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h23)
  unfold m1SqOfU slope1 uRoot1
  field_simp

/-- Factored form: `M₃² = slope3 · (uRoot3 − u)` as affine
functions. -/
theorem m3SqOfU_eq_slope3_mul (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E u : ℝ) :
    m3SqOfU b Λ E u = slope3 b * (uRoot3 b Λ E - u) := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  have h21 : b.I2 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h12)
  unfold m3SqOfU slope3 uRoot3
  field_simp

/-- Endpoint value at `u = 0`: `M₁² = I₁(2E·I₃−Λ)/(I₃−I₁)`. -/
theorem m1SqOfU_at_zero (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    m1SqOfU b Λ E 0 = b.I1 * (2 * E * b.I3 - Λ) / (b.I3 - b.I1) := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold m1SqOfU
  field_simp
  ring

/-- Endpoint value at `u = 0`: `M₃² = I₃(Λ−2E·I₁)/(I₃−I₁)`. -/
theorem m3SqOfU_at_zero (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    m3SqOfU b Λ E 0 = b.I3 * (Λ - 2 * E * b.I1) / (b.I3 - b.I1) := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold m3SqOfU
  field_simp
  ring

/-- `M₁²` is affine **decreasing** in `u` (strictly). -/
theorem m1SqOfU_strictAnti (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) : StrictAnti (m1SqOfU b Λ E) := by
  intro u v huv
  rw [m1SqOfU_eq_slope1_mul b h12 h23, m1SqOfU_eq_slope1_mul b h12 h23]
  exact mul_lt_mul_of_pos_left (by linarith) (slope1_pos b h12 h23)

/-- `M₃²` is affine **decreasing** in `u` (strictly) — the
correction to the memo's "increasing": see the module header. -/
theorem m3SqOfU_strictAnti (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) : StrictAnti (m3SqOfU b Λ E) := by
  intro u v huv
  rw [m3SqOfU_eq_slope3_mul b h12 h23, m3SqOfU_eq_slope3_mul b h12 h23]
  exact mul_lt_mul_of_pos_left (by linarith) (slope3_pos b h12 h23)

theorem m1SqOfU_at_uRoot1 (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    m1SqOfU b Λ E (uRoot1 b Λ E) = 0 := by
  rw [m1SqOfU_eq_slope1_mul b h12 h23, sub_self, mul_zero]

theorem m3SqOfU_at_uRoot3 (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    m3SqOfU b Λ E (uRoot3 b Λ E) = 0 := by
  rw [m3SqOfU_eq_slope3_mul b h12 h23, sub_self, mul_zero]

/-! ## The level set and the bridge from the foundation -/

/-- Membership in the polhode level set `𝒫_E`: the two first
integrals, in momentum coordinates. -/
def onPolhode (b : SolidBody) (M : Fin 3 → ℝ) (Λ E : ℝ) : Prop :=
  (∑ i, (M i) ^ 2) = Λ ∧ (∑ i, (M i) ^ 2 / momInertia b i) = 2 * E

theorem onPolhode_iff (b : SolidBody) (M : Fin 3 → ℝ) (Λ E : ℝ) :
    onPolhode b M Λ E ↔
      (M 0) ^ 2 + (M 1) ^ 2 + (M 2) ^ 2 = Λ ∧
        (M 0) ^ 2 / b.I1 + (M 1) ^ 2 / b.I2 + (M 2) ^ 2 / b.I3 = 2 * E := by
  unfold onPolhode
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [momInertia_zero, momInertia_one, momInertia_two]

/-- Bridge: for `M = angMom b ω`, the momentum-sphere sum is the
foundation's `angMomSq`. -/
theorem sum_angMom_sq (b : SolidBody) (ω : Fin 3 → ℝ) :
    (∑ i, (angMom b ω i) ^ 2) = angMomSq b ω := rfl

/-- Bridge: for `M = angMom b ω`, the weighted sum is twice the
foundation's `rotEnergy`. -/
theorem sum_angMom_sq_div (b : SolidBody) (ω : Fin 3 → ℝ) :
    (∑ i, (angMom b ω i) ^ 2 / momInertia b i) = 2 * rotEnergy b ω := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  unfold rotEnergy
  simp only [Fin.sum_univ_three, angMom, momInertia_zero, momInertia_one,
    momInertia_two]
  field_simp

/-- Hence every `ω` lies on the polhode of its own conserved
quantities: `onPolhode b (angMom b ω) (angMomSq b ω) (rotEnergy b ω)`. -/
theorem angMom_onPolhode (b : SolidBody) (ω : Fin 3 → ℝ) :
    onPolhode b (angMom b ω) (angMomSq b ω) (rotEnergy b ω) :=
  ⟨sum_angMom_sq b ω, sum_angMom_sq_div b ω⟩

/-! ## The affine identities on `𝒫_E` -/

/-- **Affine form for `M₁²`:** on `𝒫_E`, `M₁²` is the affine
function `m1SqOfU` of `u = M₂²`. -/
theorem affine_M1 (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3)
    (M : Fin 3 → ℝ) (Λ E : ℝ) (hM : onPolhode b M Λ E) :
    (M 0) ^ 2 = m1SqOfU b Λ E ((M 1) ^ 2) := by
  obtain ⟨hS, hE⟩ := (onPolhode_iff b M Λ E).mp hM
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold m1SqOfU
  field_simp at hE ⊢
  linear_combination hE - (b.I1 * b.I2) * hS

/-- **Affine form for `M₃²`:** on `𝒫_E`, `M₃²` is the affine
function `m3SqOfU` of `u = M₂²`. -/
theorem affine_M3 (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3)
    (M : Fin 3 → ℝ) (Λ E : ℝ) (hM : onPolhode b M Λ E) :
    (M 2) ^ 2 = m3SqOfU b Λ E ((M 1) ^ 2) := by
  obtain ⟨hS, hE⟩ := (onPolhode_iff b M Λ E).mp hM
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold m3SqOfU
  field_simp at hE ⊢
  linear_combination -hE + (b.I2 * b.I3) * hS

/-- Each squared component on `𝒫_E` is at most `Λ`. -/
theorem sq_le_of_onPolhode (b : SolidBody) (M : Fin 3 → ℝ) (Λ E : ℝ)
    (hM : onPolhode b M Λ E) (i : Fin 3) : (M i) ^ 2 ≤ Λ := by
  have hsum : (∑ j, (M j) ^ 2) = Λ := hM.1
  have h := Finset.single_le_sum (f := fun j => (M j) ^ 2)
    (fun j _ => sq_nonneg (M j)) (Finset.mem_univ i)
  linarith

/-- On `𝒫_E`, `u ≤ uRoot1` (else `M₁²` would be negative). -/
theorem u_le_uRoot1 (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3)
    (M : Fin 3 → ℝ) (Λ E : ℝ) (hM : onPolhode b M Λ E) :
    (M 1) ^ 2 ≤ uRoot1 b Λ E := by
  have h := affine_M1 b h12 h23 M Λ E hM
  rw [m1SqOfU_eq_slope1_mul b h12 h23] at h
  by_contra hc
  push Not at hc
  have hneg : slope1 b * (uRoot1 b Λ E - (M 1) ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (slope1_pos b h12 h23) (by linarith)
  nlinarith [sq_nonneg (M 0)]

/-- On `𝒫_E`, `u ≤ uRoot3` (else `M₃²` would be negative). -/
theorem u_le_uRoot3 (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3)
    (M : Fin 3 → ℝ) (Λ E : ℝ) (hM : onPolhode b M Λ E) :
    (M 1) ^ 2 ≤ uRoot3 b Λ E := by
  have h := affine_M3 b h12 h23 M Λ E hM
  rw [m3SqOfU_eq_slope3_mul b h12 h23] at h
  by_contra hc
  push Not at hc
  have hneg : slope3 b * (uRoot3 b Λ E - (M 1) ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (slope3_pos b h12 h23) (by linarith)
  nlinarith [sq_nonneg (M 2)]

/-- On `𝒫_E`, `u` is at most the maximal feasible value `uMax`. -/
theorem u_le_uMax (b : SolidBody) (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3)
    (M : Fin 3 → ℝ) (Λ E : ℝ) (hM : onPolhode b M Λ E) :
    (M 1) ^ 2 ≤ uMax b Λ E :=
  le_min (u_le_uRoot1 b h12 h23 M Λ E hM) (u_le_uRoot3 b h12 h23 M Λ E hM)

/-- Off the separatrix or on it, `M₁²` vanishes exactly at its
root: on `𝒫_E`, `M₁² = 0 ↔ u = uRoot1` (a simple root — the affine
slope is nonzero). -/
theorem m1Sq_eq_zero_iff (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ E : ℝ)
    (hM : onPolhode b M Λ E) :
    (M 0) ^ 2 = 0 ↔ (M 1) ^ 2 = uRoot1 b Λ E := by
  have h := affine_M1 b h12 h23 M Λ E hM
  rw [m1SqOfU_eq_slope1_mul b h12 h23] at h
  rw [h, mul_eq_zero]
  constructor
  · rintro (hc | hc)
    · exact absurd hc (ne_of_gt (slope1_pos b h12 h23))
    · linarith
  · intro hc
    exact Or.inr (by linarith)

/-- On `𝒫_E`, `M₃² = 0 ↔ u = uRoot3` (simple root). -/
theorem m3Sq_eq_zero_iff (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ E : ℝ)
    (hM : onPolhode b M Λ E) :
    (M 2) ^ 2 = 0 ↔ (M 1) ^ 2 = uRoot3 b Λ E := by
  have h := affine_M3 b h12 h23 M Λ E hM
  rw [m3SqOfU_eq_slope3_mul b h12 h23] at h
  rw [h, mul_eq_zero]
  constructor
  · rintro (hc | hc)
    · exact absurd hc (ne_of_gt (slope3_pos b h12 h23))
    · linarith
  · intro hc
    exact Or.inr (by linarith)

/-- Endpoint values at `u = 0`: if `M ∈ 𝒫_E` has `M₂ = 0`, the
other two squares are the intercepts. -/
theorem endpoint_at_u_zero (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ E : ℝ)
    (hM : onPolhode b M Λ E) (h2 : M 1 = 0) :
    (M 0) ^ 2 = b.I1 * (2 * E * b.I3 - Λ) / (b.I3 - b.I1) ∧
      (M 2) ^ 2 = b.I3 * (Λ - 2 * E * b.I1) / (b.I3 - b.I1) := by
  have hu : (M 1) ^ 2 = 0 := by rw [h2]; norm_num
  refine ⟨?_, ?_⟩
  · rw [affine_M1 b h12 h23 M Λ E hM, hu, m1SqOfU_at_zero b h12 h23]
  · rw [affine_M3 b h12 h23 M Λ E hM, hu, m3SqOfU_at_zero b h12 h23]

/-! ## The separatrix -/

/-- At `E = E_sep`, `M₁² = slope1 · (Λ − u)` as affine functions. -/
theorem m1SqOfU_at_sep (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ u : ℝ) :
    m1SqOfU b Λ (sepEnergy b Λ) u = slope1 b * (Λ - u) := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold m1SqOfU slope1 sepEnergy
  field_simp

/-- At `E = E_sep`, `M₃² = slope3 · (Λ − u)` as affine functions. -/
theorem m3SqOfU_at_sep (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ u : ℝ) :
    m3SqOfU b Λ (sepEnergy b Λ) u = slope3 b * (Λ - u) := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  unfold m3SqOfU slope3 sepEnergy
  field_simp

/-- At `E = E_sep` both roots coalesce at `u = Λ`: `uRoot1 = Λ`. -/
theorem uRoot1_at_sep (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) :
    uRoot1 b Λ (sepEnergy b Λ) = Λ := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h32 : b.I3 - b.I2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h23)
  unfold uRoot1 sepEnergy
  field_simp

/-- At `E = E_sep`, `uRoot3 = Λ`. -/
theorem uRoot3_at_sep (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) :
    uRoot3 b Λ (sepEnergy b Λ) = Λ := by
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h21 : b.I2 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h12)
  unfold uRoot3 sepEnergy
  field_simp

/-- Hence at the separatrix the maximal feasible `u` is `Λ`. -/
theorem uMax_at_sep (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) :
    uMax b Λ (sepEnergy b Λ) = Λ := by
  unfold uMax
  rw [uRoot1_at_sep b h12 h23, uRoot3_at_sep b h12 h23, min_self]

/-- On `𝒫_{E_sep}`, `M₁²` vanishes exactly at `u = Λ` and nowhere
else in range. -/
theorem sep_m1Sq_eq_zero_iff (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ : ℝ)
    (hM : onPolhode b M Λ (sepEnergy b Λ)) :
    (M 0) ^ 2 = 0 ↔ (M 1) ^ 2 = Λ := by
  have h := affine_M1 b h12 h23 M Λ (sepEnergy b Λ) hM
  rw [m1SqOfU_at_sep b h12 h23] at h
  rw [h, mul_eq_zero]
  constructor
  · rintro (hc | hc)
    · exact absurd hc (ne_of_gt (slope1_pos b h12 h23))
    · linarith
  · intro hc
    exact Or.inr (by linarith)

/-- On `𝒫_{E_sep}`, `M₃²` vanishes exactly at `u = Λ`. -/
theorem sep_m3Sq_eq_zero_iff (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ : ℝ)
    (hM : onPolhode b M Λ (sepEnergy b Λ)) :
    (M 2) ^ 2 = 0 ↔ (M 1) ^ 2 = Λ := by
  have h := affine_M3 b h12 h23 M Λ (sepEnergy b Λ) hM
  rw [m3SqOfU_at_sep b h12 h23] at h
  rw [h, mul_eq_zero]
  constructor
  · rintro (hc | hc)
    · exact absurd hc (ne_of_gt (slope3_pos b h12 h23))
    · linarith
  · intro hc
    exact Or.inr (by linarith)

/-- Component data of a saddle point does lie on `𝒫_{E_sep}`:
`M₀ = 0`, `M₂ = 0`, `M₂²`-component `M₁² = Λ` give both integrals. -/
theorem onPolhode_of_saddle_components (b : SolidBody) (M : Fin 3 → ℝ)
    (Λ : ℝ) (h0 : M 0 = 0) (h2 : M 2 = 0) (h1 : (M 1) ^ 2 = Λ) :
    onPolhode b M Λ (sepEnergy b Λ) := by
  rw [onPolhode_iff]
  have h2' : b.I2 ≠ 0 := b.I2_pos.ne'
  refine ⟨by rw [h0, h2, h1]; norm_num, ?_⟩
  rw [h0, h2, h1]
  unfold sepEnergy
  field_simp
  ring

/-- **Saddle characterization.** On `𝒫_{E_sep}` (with `Λ > 0`),
`M₁ = 0` holds exactly at the two saddles:
`M = (0, ±√Λ, 0)`, stated componentwise. -/
theorem sep_saddle (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ : ℝ) (hΛ : 0 < Λ)
    (hM : onPolhode b M Λ (sepEnergy b Λ)) :
    M 0 = 0 ↔ M 2 = 0 ∧ (M 1 = Real.sqrt Λ ∨ M 1 = -Real.sqrt Λ) := by
  constructor
  · intro h0
    have hu : (M 1) ^ 2 = Λ :=
      (sep_m1Sq_eq_zero_iff b h12 h23 M Λ hM).mp (by rw [h0]; norm_num)
    have h3 : (M 2) ^ 2 = 0 :=
      (sep_m3Sq_eq_zero_iff b h12 h23 M Λ hM).mpr hu
    refine ⟨pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h3, ?_⟩
    have hsq : (M 1) ^ 2 = (Real.sqrt Λ) ^ 2 := by
      rw [Real.sq_sqrt hΛ.le]; exact hu
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
  · rintro ⟨h2, h1⟩
    have hu : (M 1) ^ 2 = Λ := by
      rcases h1 with h | h
      · rw [h]; exact Real.sq_sqrt hΛ.le
      · rw [h, neg_sq]; exact Real.sq_sqrt hΛ.le
    have h0sq : (M 0) ^ 2 = 0 :=
      (sep_m1Sq_eq_zero_iff b h12 h23 M Λ hM).mpr hu
    exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h0sq

/-! ## Band endpoint structure (the portrait brick's input) -/

/-- In the top band, `uRoot3 < Λ` (from `Λ/I₂ < 2E`). -/
theorem uRoot3_lt_of_topBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (Λ E : ℝ) (hband : inTopBand b Λ E) :
    uRoot3 b Λ E < Λ := by
  have hI2 : 0 < b.I2 := b.I2_pos
  have hΛE : Λ < 2 * E * b.I2 := by
    have h := hband.1
    rwa [div_lt_iff₀ hI2] at h
  unfold uRoot3
  rw [div_lt_iff₀ (sub_pos.mpr h12)]
  nlinarith [b.I1_pos, hΛE]

/-- In the top band, `Λ ≤ uRoot1` (from `Λ/I₂ < 2E`). -/
theorem le_uRoot1_of_topBand (b : SolidBody) (h23 : b.I2 < b.I3)
    (Λ E : ℝ) (hband : inTopBand b Λ E) :
    Λ ≤ uRoot1 b Λ E := by
  have hΛE : Λ < 2 * E * b.I2 := by
    have hb := hband.1
    rwa [div_lt_iff₀ b.I2_pos] at hb
  unfold uRoot1
  rw [le_div_iff₀ (sub_pos.mpr h23)]
  nlinarith [b.I3_pos, hΛE]

/-- In the top band the maximal feasible `u` is `uRoot3`. -/
theorem uMax_eq_uRoot3_of_topBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inTopBand b Λ E) :
    uMax b Λ E = uRoot3 b Λ E := by
  unfold uMax
  apply min_eq_right
  exact le_trans (uRoot3_lt_of_topBand b h12 Λ E hband).le
    (le_uRoot1_of_topBand b h23 Λ E hband)

/-- In the bottom band, `uRoot1 < Λ` (from `2E < Λ/I₂`). -/
theorem uRoot1_lt_of_botBand (b : SolidBody) (h23 : b.I2 < b.I3)
    (Λ E : ℝ) (hband : inBotBand b Λ E) :
    uRoot1 b Λ E < Λ := by
  have hΛE : 2 * E * b.I2 < Λ := by
    have hb := hband.2
    rwa [lt_div_iff₀ b.I2_pos] at hb
  unfold uRoot1
  rw [div_lt_iff₀ (sub_pos.mpr h23)]
  nlinarith [b.I3_pos, hΛE]

/-- In the bottom band, `Λ ≤ uRoot3` (from `2E < Λ/I₂`). -/
theorem le_uRoot3_of_botBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (Λ E : ℝ) (hband : inBotBand b Λ E) :
    Λ ≤ uRoot3 b Λ E := by
  have hΛE : 2 * E * b.I2 < Λ := by
    have hb := hband.2
    rwa [lt_div_iff₀ b.I2_pos] at hb
  unfold uRoot3
  rw [le_div_iff₀ (sub_pos.mpr h12)]
  nlinarith [b.I1_pos, hΛE]

/-- In the bottom band the maximal feasible `u` is `uRoot1`. -/
theorem uMax_eq_uRoot1_of_botBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inBotBand b Λ E) :
    uMax b Λ E = uRoot1 b Λ E := by
  unfold uMax
  apply min_eq_left
  exact le_trans (uRoot1_lt_of_botBand b h23 Λ E hband).le
    (le_uRoot3_of_botBand b h12 Λ E hband)

/-- The root-difference identity behind the top-band bound:
`slope1 · (uRoot1 − uRoot3) = (I₁I₂/(I₂−I₁)) · (2E − Λ/I₂)`. -/
theorem slope1_mul_root_diff (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    slope1 b * (uRoot1 b Λ E - uRoot3 b Λ E)
      = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2) := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  have h32 : b.I3 - b.I2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h23)
  have h21 : b.I2 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h12)
  unfold slope1 uRoot1 uRoot3
  field_simp
  ring

/-- The root-difference identity behind the bottom-band bound:
`slope3 · (uRoot3 − uRoot1) = (I₂I₃/(I₃−I₂)) · (Λ/I₂ − 2E)`. -/
theorem slope3_mul_root_diff (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    slope3 b * (uRoot3 b Λ E - uRoot1 b Λ E)
      = (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E) := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  have h32 : b.I3 - b.I2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h23)
  have h21 : b.I2 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h12)
  unfold slope3 uRoot1 uRoot3
  field_simp
  ring

/-- Endpoint values at maximal `u`, top band: at `u = uMax`,
`M₃²`-form vanishes and `M₁²`-form takes its band minimum
`(I₁I₂/(I₂−I₁))·(2E − Λ/I₂)`. -/
theorem endpoint_at_uMax_top (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inTopBand b Λ E) :
    m3SqOfU b Λ E (uMax b Λ E) = 0 ∧
      m1SqOfU b Λ E (uMax b Λ E)
        = (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2) := by
  rw [uMax_eq_uRoot3_of_topBand b h12 h23 Λ E hband]
  refine ⟨m3SqOfU_at_uRoot3 b h12 h23 Λ E, ?_⟩
  rw [m1SqOfU_eq_slope1_mul b h12 h23, slope1_mul_root_diff b h12 h23]

/-- Endpoint values at maximal `u`, bottom band: at `u = uMax`,
`M₁²`-form vanishes and `M₃²`-form takes its band minimum
`(I₂I₃/(I₃−I₂))·(Λ/I₂ − 2E)`. -/
theorem endpoint_at_uMax_bot (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inBotBand b Λ E) :
    m1SqOfU b Λ E (uMax b Λ E) = 0 ∧
      m3SqOfU b Λ E (uMax b Λ E)
        = (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E) := by
  rw [uMax_eq_uRoot1_of_botBand b h12 h23 Λ E hband]
  refine ⟨m1SqOfU_at_uRoot1 b h12 h23 Λ E, ?_⟩
  rw [m3SqOfU_eq_slope3_mul b h12 h23, slope3_mul_root_diff b h12 h23]

/-- **Top-band lower bound** (memo §2's `c`, explicit):
on `𝒫_E` in the top band, `M₁² ≥ (I₁I₂/(I₂−I₁))·(2E − Λ/I₂) > 0`;
in particular `M₁` never vanishes there. -/
theorem topBand_m1Sq_lower (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ E : ℝ)
    (hband : inTopBand b Λ E) (hM : onPolhode b M Λ E) :
    0 < (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2) ∧
      (b.I1 * b.I2 / (b.I2 - b.I1)) * (2 * E - Λ / b.I2) ≤ (M 0) ^ 2 := by
  have hfac : 0 < 2 * E - Λ / b.I2 := sub_pos.mpr hband.1
  have hc : 0 < b.I1 * b.I2 / (b.I2 - b.I1) :=
    div_pos (mul_pos b.I1_pos b.I2_pos) (sub_pos.mpr h12)
  refine ⟨mul_pos hc hfac, ?_⟩
  have h := affine_M1 b h12 h23 M Λ E hM
  rw [m1SqOfU_eq_slope1_mul b h12 h23] at h
  rw [h, ← slope1_mul_root_diff b h12 h23]
  exact mul_le_mul_of_nonneg_left
    (by linarith [u_le_uRoot3 b h12 h23 M Λ E hM]) (slope1_pos b h12 h23).le

/-- **Bottom-band lower bound:** on `𝒫_E` in the bottom band,
`M₃² ≥ (I₂I₃/(I₃−I₂))·(Λ/I₂ − 2E) > 0`; `M₃` never vanishes there. -/
theorem botBand_m3Sq_lower (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ E : ℝ)
    (hband : inBotBand b Λ E) (hM : onPolhode b M Λ E) :
    0 < (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E) ∧
      (b.I2 * b.I3 / (b.I3 - b.I2)) * (Λ / b.I2 - 2 * E) ≤ (M 2) ^ 2 := by
  have hfac : 0 < Λ / b.I2 - 2 * E := sub_pos.mpr hband.2
  have hc : 0 < b.I2 * b.I3 / (b.I3 - b.I2) :=
    div_pos (mul_pos b.I2_pos b.I3_pos) (sub_pos.mpr h23)
  refine ⟨mul_pos hc hfac, ?_⟩
  have h := affine_M3 b h12 h23 M Λ E hM
  rw [m3SqOfU_eq_slope3_mul b h12 h23] at h
  rw [h, ← slope3_mul_root_diff b h12 h23]
  exact mul_le_mul_of_nonneg_left
    (by linarith [u_le_uRoot1 b h12 h23 M Λ E hM]) (slope3_pos b h12 h23).le

end ThetLogos
