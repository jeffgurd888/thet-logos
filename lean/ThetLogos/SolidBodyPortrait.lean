import Mathlib.Tactic
import ThetLogos.SolidBodyPolhode
import ThetLogos.SolidBodyRankSwitch

/-!
# ThetLogos.SolidBodyPortrait — the polhode portrait brick

The portrait stage of the nonlinear rigid-body program (scoping
memo `nonlinear-rigid-scoping-2026-10-26.md` §2), built on the N0
package `SolidBodyPolhode` (landed) and Brick 2
`SolidBodyRankSwitch`. Fixed body, frozen coefficients, abstract
body only.

## What is proved (T1, from definitions/hypotheses; classical core T4)

For a body with `0 < I₁ < I₂ < I₃`, momentum scale `Λ`, and the
polhode level set `𝒫_E = {M | Σ Mᵢ² = Λ, Σ Mᵢ²/Iᵢ = 2E}`:

* **Band separation.** In the top band (`Λ/I₂ < 2E < Λ/I₁`) the
  first component never vanishes on `𝒫_E` (N0's explicit bound
  `M₁² ≥ (I₁I₂/(I₂−I₁))·(2E − Λ/I₂) > 0`), so `𝒫_E` is covered by
  the two disjoint half-spaces `{M₁ > 0}` and `{M₁ < 0}` — both
  open in the ambient space, both meeting `𝒫_E` (exhibited points
  with `M₂ = 0`) — and no continuous curve inside `𝒫_E` joins a
  point of one piece to a point of the other. The bottom band is
  symmetric, with `M₃` in place of `M₁`.
* **Separatrix.** At `E = E_sep`, within `𝒫_{E_sep}`, `M₁ = 0`
  holds exactly at the two saddles `(0, ±√Λ, 0)` (N0's
  `sep_saddle`, restated over the level set), and every continuous
  curve inside `𝒫_{E_sep}` from `M₁ > 0` to `M₁ < 0` passes through
  a saddle (IVT).
* **Crossing corollary.** The saddle's labeled axis (index `1`, the
  middle moment) is the *unique* labeled axis with Brick 2's frozen
  product `rankQ > 0`; axes `0` and `2` have `rankQ < 0`. Along
  Brick 2's moment paths (`rankQ_crossing`), the crossing therefore
  exchanges which labeled axis carries the frozen portrait's
  saddle — a statement about the family of frozen portraits, not
  about any trajectory.

## Conventions — the corrected affine directions

Both affine forms of N0 are **decreasing** in `u = M₂²`
(`m1SqOfU_strictAnti`, `m3SqOfU_strictAnti`, landed). The scoping
memo's §0 wording ("`M₃²` increasing") was wrong and is superseded
by the N0 landing dossier; nothing here consumes it.

## Fences

Separation is stated as cover + disjoint + nonempty + open
half-spaces + path obstruction. The exact connected-component
COUNT is the L-grade follow-on and is **not** proved or claimed
here. Frozen coefficients throughout; no trajectory follows a
portrait change. NO CLAIM. Parts of any official (Clay) statement
closed by this file: 0.
-/

namespace ThetLogos

/-- The polhode level set `𝒫_E` as a set of momentum vectors:
`Σ Mᵢ² = Λ` and `Σ Mᵢ²/Iᵢ = 2E` (N0's `onPolhode`). -/
def polhodeSet (b : SolidBody) (Λ E : ℝ) : Set (Fin 3 → ℝ) :=
  {M | onPolhode b M Λ E}

/-! ## The two `u = 0` sum identities -/

/-- At `u = 0` the two affine forms sum to `Λ`:
`m1SqOfU b Λ E 0 + m3SqOfU b Λ E 0 = Λ`. -/
theorem m1SqOfU_zero_add_m3SqOfU_zero (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    m1SqOfU b Λ E 0 + m3SqOfU b Λ E 0 = Λ := by
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  rw [m1SqOfU_at_zero b h12 h23, m3SqOfU_at_zero b h12 h23]
  field_simp
  ring

/-- At `u = 0` the two affine forms solve the energy constraint:
`m1SqOfU b Λ E 0 / I₁ + m3SqOfU b Λ E 0 / I₃ = 2 * E`. -/
theorem m1SqOfU_zero_div_add_m3SqOfU_zero (b : SolidBody)
    (h12 : b.I1 < b.I2) (h23 : b.I2 < b.I3) (Λ E : ℝ) :
    m1SqOfU b Λ E 0 / b.I1 + m3SqOfU b Λ E 0 / b.I3 = 2 * E := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have h31 : b.I3 - b.I1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans h12 h23))
  rw [m1SqOfU_at_zero b h12 h23, m3SqOfU_at_zero b h12 h23]
  field_simp
  ring

/-! ## Exhibited points on `𝒫_E` (the `M₂ = 0` points) -/

/-- Point-membership criterion: any vector `![s₁, 0, s₃]` whose two
outer squares are the affine forms' values at `u = 0` lies on
`𝒫_E` — the two sum identities are exactly the level set's two
constraints. No sign hypothesis: only squares enter. -/
theorem point_mem_polhodeSet (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (s₁ s₃ : ℝ)
    (h₁ : s₁ ^ 2 = m1SqOfU b Λ E 0) (h₃ : s₃ ^ 2 = m3SqOfU b Λ E 0) :
    ![s₁, 0, s₃] ∈ polhodeSet b Λ E := by
  have hsum := m1SqOfU_zero_add_m3SqOfU_zero b h12 h23 Λ E
  have hdiv := m1SqOfU_zero_div_add_m3SqOfU_zero b h12 h23 Λ E
  show onPolhode b ![s₁, 0, s₃] Λ E
  rw [onPolhode_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  constructor
  · rw [h₁, h₃]; linarith [hsum]
  · rw [h₁, h₃]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, add_zero]
    linarith [hdiv]

/-- The exhibited `𝒫_E` point with `M₁ = +√(intercept₁)`,
`M₂ = 0`, `M₃ = +√(intercept₃)`, the intercepts being the affine
forms' values at `u = 0`. -/
noncomputable def ptPos0 (b : SolidBody) (Λ E : ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (m1SqOfU b Λ E 0), 0, Real.sqrt (m3SqOfU b Λ E 0)]

/-- The exhibited `𝒫_E` point with `M₁ = −√(intercept₁)`. -/
noncomputable def ptNeg0 (b : SolidBody) (Λ E : ℝ) : Fin 3 → ℝ :=
  ![-Real.sqrt (m1SqOfU b Λ E 0), 0, Real.sqrt (m3SqOfU b Λ E 0)]

/-- The exhibited `𝒫_E` point with `M₃ = −√(intercept₃)`. -/
noncomputable def ptNeg2 (b : SolidBody) (Λ E : ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (m1SqOfU b Λ E 0), 0, -Real.sqrt (m3SqOfU b Λ E 0)]

theorem ptPos0_mem (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (ha : 0 ≤ m1SqOfU b Λ E 0) (hc : 0 ≤ m3SqOfU b Λ E 0) :
    ptPos0 b Λ E ∈ polhodeSet b Λ E :=
  point_mem_polhodeSet b h12 h23 Λ E _ _
    (Real.sq_sqrt ha) (Real.sq_sqrt hc)

theorem ptNeg0_mem (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (ha : 0 ≤ m1SqOfU b Λ E 0) (hc : 0 ≤ m3SqOfU b Λ E 0) :
    ptNeg0 b Λ E ∈ polhodeSet b Λ E :=
  point_mem_polhodeSet b h12 h23 Λ E _ _
    (by rw [neg_sq]; exact Real.sq_sqrt ha) (Real.sq_sqrt hc)

theorem ptNeg2_mem (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (ha : 0 ≤ m1SqOfU b Λ E 0) (hc : 0 ≤ m3SqOfU b Λ E 0) :
    ptNeg2 b Λ E ∈ polhodeSet b Λ E :=
  point_mem_polhodeSet b h12 h23 Λ E _ _
    (Real.sq_sqrt ha) (by rw [neg_sq]; exact Real.sq_sqrt hc)

/-! ## Intercept positivity in the bands -/

/-- Top band: the first intercept is positive (uses `Λ > 0`:
`2E > Λ/I₂` gives `2E·I₃ > Λ·I₃/I₂ > Λ`). -/
theorem m1SqOfU_zero_pos_of_topBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hΛ : 0 < Λ)
    (hband : inTopBand b Λ E) : 0 < m1SqOfU b Λ E 0 := by
  have hΛE : Λ < 2 * E * b.I2 := by
    have h := hband.1
    rwa [div_lt_iff₀ b.I2_pos] at h
  have hE3 : Λ < 2 * E * b.I3 := by nlinarith [hΛ, hΛE, b.I2_pos, h23]
  rw [m1SqOfU_at_zero b h12 h23]
  exact div_pos (mul_pos b.I1_pos (by linarith))
    (sub_pos.mpr (lt_trans h12 h23))

/-- Top band: the third intercept is positive (from `2E < Λ/I₁`). -/
theorem m3SqOfU_zero_pos_of_topBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (hband : inTopBand b Λ E) : 0 < m3SqOfU b Λ E 0 := by
  have hE1 : 2 * E * b.I1 < Λ := by
    have h := hband.2
    rwa [lt_div_iff₀ b.I1_pos] at h
  rw [m3SqOfU_at_zero b h12 h23]
  exact div_pos (mul_pos b.I3_pos (by linarith))
    (sub_pos.mpr (lt_trans h12 h23))

/-- Bottom band: the first intercept is positive (from
`2E > Λ/I₃`). -/
theorem m1SqOfU_zero_pos_of_botBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ)
    (hband : inBotBand b Λ E) : 0 < m1SqOfU b Λ E 0 := by
  have hE3 : Λ < 2 * E * b.I3 := by
    have h := hband.1
    rwa [div_lt_iff₀ b.I3_pos] at h
  rw [m1SqOfU_at_zero b h12 h23]
  exact div_pos (mul_pos b.I1_pos (by linarith))
    (sub_pos.mpr (lt_trans h12 h23))

/-- Bottom band: the third intercept is positive (uses `Λ > 0`:
`2E < Λ/I₂` gives `2E·I₁ < Λ·I₁/I₂ < Λ`). -/
theorem m3SqOfU_zero_pos_of_botBand (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hΛ : 0 < Λ)
    (hband : inBotBand b Λ E) : 0 < m3SqOfU b Λ E 0 := by
  have hE2 : 2 * E * b.I2 < Λ := by
    have h := hband.2
    rwa [lt_div_iff₀ b.I2_pos] at h
  have hE1 : 2 * E * b.I1 < Λ := by nlinarith [hΛ, hE2, b.I1_pos, h12]
  rw [m3SqOfU_at_zero b h12 h23]
  exact div_pos (mul_pos b.I3_pos (by linarith))
    (sub_pos.mpr (lt_trans h12 h23))

/-! ## Band separation -/

/-- In the top band, `M₁` never vanishes on `𝒫_E` (N0's explicit
lower bound on `M₁²` is positive). -/
theorem topBand_m1_ne_zero (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inTopBand b Λ E)
    (M : Fin 3 → ℝ) (hM : M ∈ polhodeSet b Λ E) : M 0 ≠ 0 := by
  obtain ⟨hpos, hle⟩ := topBand_m1Sq_lower b h12 h23 M Λ E hband hM
  intro h0
  rw [h0] at hle
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hle
  exact (lt_irrefl _ (lt_of_lt_of_le hpos hle)).elim

/-- In the bottom band, `M₃` never vanishes on `𝒫_E`. -/
theorem botBand_m3_ne_zero (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inBotBand b Λ E)
    (M : Fin 3 → ℝ) (hM : M ∈ polhodeSet b Λ E) : M 2 ≠ 0 := by
  obtain ⟨hpos, hle⟩ := botBand_m3Sq_lower b h12 h23 M Λ E hband hM
  intro h0
  rw [h0] at hle
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hle
  exact (lt_irrefl _ (lt_of_lt_of_le hpos hle)).elim

/-- The half-spaces are open in the ambient space. -/
theorem isOpen_m0_pos : IsOpen {M : Fin 3 → ℝ | 0 < M 0} :=
  isOpen_lt continuous_const (continuous_apply 0)

/-- The half-spaces are open in the ambient space. -/
theorem isOpen_m0_neg : IsOpen {M : Fin 3 → ℝ | M 0 < 0} :=
  isOpen_lt (continuous_apply 0) continuous_const

/-- The half-spaces are open in the ambient space. -/
theorem isOpen_m2_pos : IsOpen {M : Fin 3 → ℝ | 0 < M 2} :=
  isOpen_lt continuous_const (continuous_apply 2)

/-- The half-spaces are open in the ambient space. -/
theorem isOpen_m2_neg : IsOpen {M : Fin 3 → ℝ | M 2 < 0} :=
  isOpen_lt (continuous_apply 2) continuous_const

/-- **Top-band separation (cover):** `𝒫_E` is covered by the two
half-spaces `{M₁ > 0}` and `{M₁ < 0}`. -/
theorem topBand_polhode_subset (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inTopBand b Λ E) :
    polhodeSet b Λ E ⊆
      {M : Fin 3 → ℝ | 0 < M 0} ∪ {M : Fin 3 → ℝ | M 0 < 0} := by
  intro M hM
  have hne := topBand_m1_ne_zero b h12 h23 Λ E hband M hM
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Bottom-band separation (cover):** `𝒫_E` is covered by
`{M₃ > 0}` and `{M₃ < 0}`. -/
theorem botBand_polhode_subset (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inBotBand b Λ E) :
    polhodeSet b Λ E ⊆
      {M : Fin 3 → ℝ | 0 < M 2} ∪ {M : Fin 3 → ℝ | M 2 < 0} := by
  intro M hM
  have hne := botBand_m3_ne_zero b h12 h23 Λ E hband M hM
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The two top-band pieces of `𝒫_E` are disjoint. -/
theorem topBand_disjoint (b : SolidBody) (Λ E : ℝ) :
    Disjoint (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | 0 < M 0})
      (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | M 0 < 0}) := by
  rw [Set.disjoint_left]
  rintro M ⟨-, hpos⟩ ⟨-, hneg⟩
  change (0 : ℝ) < M 0 at hpos
  change M 0 < (0 : ℝ) at hneg
  exact (lt_irrefl _ (lt_trans hneg hpos)).elim

/-- The two bottom-band pieces of `𝒫_E` are disjoint. -/
theorem botBand_disjoint (b : SolidBody) (Λ E : ℝ) :
    Disjoint (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | 0 < M 2})
      (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | M 2 < 0}) := by
  rw [Set.disjoint_left]
  rintro M ⟨-, hpos⟩ ⟨-, hneg⟩
  change (0 : ℝ) < M 2 at hpos
  change M 2 < (0 : ℝ) at hneg
  exact (lt_irrefl _ (lt_trans hneg hpos)).elim

/-- The positive top-band piece is nonempty: it contains the
exhibited point `ptPos0` (whose first component is `+√a > 0`). -/
theorem topBand_pos_nonempty (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hΛ : 0 < Λ)
    (hband : inTopBand b Λ E) :
    (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | 0 < M 0}).Nonempty := by
  have ha := m1SqOfU_zero_pos_of_topBand b h12 h23 Λ E hΛ hband
  have hc := m3SqOfU_zero_pos_of_topBand b h12 h23 Λ E hband
  refine ⟨ptPos0 b Λ E, ptPos0_mem b h12 h23 Λ E ha.le hc.le, ?_⟩
  show 0 < ptPos0 b Λ E 0
  rw [ptPos0]
  simp only [Matrix.cons_val_zero]
  exact Real.sqrt_pos.mpr ha

/-- The negative top-band piece is nonempty (`ptNeg0`). -/
theorem topBand_neg_nonempty (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hΛ : 0 < Λ)
    (hband : inTopBand b Λ E) :
    (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | M 0 < 0}).Nonempty := by
  have ha := m1SqOfU_zero_pos_of_topBand b h12 h23 Λ E hΛ hband
  have hc := m3SqOfU_zero_pos_of_topBand b h12 h23 Λ E hband
  refine ⟨ptNeg0 b Λ E, ptNeg0_mem b h12 h23 Λ E ha.le hc.le, ?_⟩
  show ptNeg0 b Λ E 0 < 0
  rw [ptNeg0]
  simp only [Matrix.cons_val_zero]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr ha)

/-- The positive bottom-band piece is nonempty (`ptPos0`, whose
third component is `+√c > 0`). -/
theorem botBand_pos_nonempty (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hΛ : 0 < Λ)
    (hband : inBotBand b Λ E) :
    (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | 0 < M 2}).Nonempty := by
  have ha := m1SqOfU_zero_pos_of_botBand b h12 h23 Λ E hband
  have hc := m3SqOfU_zero_pos_of_botBand b h12 h23 Λ E hΛ hband
  refine ⟨ptPos0 b Λ E, ptPos0_mem b h12 h23 Λ E ha.le hc.le, ?_⟩
  show 0 < ptPos0 b Λ E 2
  rw [ptPos0]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  exact Real.sqrt_pos.mpr hc

/-- The negative bottom-band piece is nonempty (`ptNeg2`). -/
theorem botBand_neg_nonempty (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hΛ : 0 < Λ)
    (hband : inBotBand b Λ E) :
    (polhodeSet b Λ E ∩ {M : Fin 3 → ℝ | M 2 < 0}).Nonempty := by
  have ha := m1SqOfU_zero_pos_of_botBand b h12 h23 Λ E hband
  have hc := m3SqOfU_zero_pos_of_botBand b h12 h23 Λ E hΛ hband
  refine ⟨ptNeg2 b Λ E, ptNeg2_mem b h12 h23 Λ E ha.le hc.le, ?_⟩
  show ptNeg2 b Λ E 2 < 0
  rw [ptNeg2]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr hc)

/-! ## Path obstruction (IVT) -/

/-- **Top-band path obstruction:** no continuous curve staying in
`𝒫_E` on `[0, 1]` joins a point with `M₁ > 0` to a point with
`M₁ < 0` — the two pieces of the separation are joined by no path
inside the level set. -/
theorem topBand_no_path_crossing (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inTopBand b Λ E)
    {x y : Fin 3 → ℝ} (hx0 : 0 < x 0) (hy0 : y 0 < 0)
    {γ : ℝ → Fin 3 → ℝ} (hγcont : Continuous γ)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ polhodeSet b Λ E)
    (hγ0 : γ 0 = x) (hγ1 : γ 1 = y) : False := by
  have hf : Continuous fun t => (γ t) 0 :=
    (continuous_apply 0).comp hγcont
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t => (γ t) 0) 1)
      ((fun t => (γ t) 0) 0) := by
    simp only [hγ0, hγ1]
    exact ⟨hy0.le, hx0.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one
    hf.continuousOn hmem
  have hne := topBand_m1_ne_zero b h12 h23 Λ E hband (γ t) (hγ t ht)
  exact hne hft

/-- **Bottom-band path obstruction:** symmetric, with `M₃`. -/
theorem botBand_no_path_crossing (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ E : ℝ) (hband : inBotBand b Λ E)
    {x y : Fin 3 → ℝ} (hx2 : 0 < x 2) (hy2 : y 2 < 0)
    {γ : ℝ → Fin 3 → ℝ} (hγcont : Continuous γ)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ polhodeSet b Λ E)
    (hγ0 : γ 0 = x) (hγ1 : γ 1 = y) : False := by
  have hf : Continuous fun t => (γ t) 2 :=
    (continuous_apply 2).comp hγcont
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t => (γ t) 2) 1)
      ((fun t => (γ t) 2) 0) := by
    simp only [hγ0, hγ1]
    exact ⟨hy2.le, hx2.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one
    hf.continuousOn hmem
  have hne := botBand_m3_ne_zero b h12 h23 Λ E hband (γ t) (hγ t ht)
  exact hne hft

/-! ## The separatrix -/

/-- **Saddle criterion, set form** (N0's `sep_saddle` over the
level set): on `𝒫_{E_sep}` with `Λ > 0`, `M₁ = 0` holds exactly at
the two saddles `M = (0, ±√Λ, 0)`, stated componentwise. -/
theorem sep_saddle_set (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (M : Fin 3 → ℝ) (Λ : ℝ) (hΛ : 0 < Λ)
    (hM : M ∈ polhodeSet b Λ (sepEnergy b Λ)) :
    M 0 = 0 ↔ M 2 = 0 ∧ (M 1 = Real.sqrt Λ ∨ M 1 = -Real.sqrt Λ) :=
  sep_saddle b h12 h23 M Λ hΛ hM

/-- **Separatrix path property:** every continuous curve inside
`𝒫_{E_sep}` on `[0, 1]` from a point with `M₁ > 0` to a point with
`M₁ < 0` passes through a saddle: at some time `t`, the curve is
at `(0, ±√Λ, 0)` componentwise (`M₀`-component `0`, third
component `0`, middle component `±√Λ`). IVT + `sep_saddle`. -/
theorem sep_path_through_saddle (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Λ : ℝ) (hΛ : 0 < Λ)
    {x y : Fin 3 → ℝ} (hx0 : 0 < x 0) (hy0 : y 0 < 0)
    {γ : ℝ → Fin 3 → ℝ} (hγcont : Continuous γ)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t ∈ polhodeSet b Λ (sepEnergy b Λ))
    (hγ0 : γ 0 = x) (hγ1 : γ 1 = y) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (γ t) 0 = 0 ∧ (γ t) 2 = 0 ∧
        ((γ t) 1 = Real.sqrt Λ ∨ (γ t) 1 = -Real.sqrt Λ) := by
  have hf : Continuous fun t => (γ t) 0 :=
    (continuous_apply 0).comp hγcont
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t => (γ t) 0) 1)
      ((fun t => (γ t) 0) 0) := by
    simp only [hγ0, hγ1]
    exact ⟨hy0.le, hx0.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one
    hf.continuousOn hmem
  have hM := hγ t ht
  have hsad := (sep_saddle_set b h12 h23 (γ t) Λ hΛ hM).mp hft
  exact ⟨t, ht, hft, hsad.1, hsad.2⟩

/-! ## The crossing corollary -/

/-- **The saddle axis is Brick 2's positive-`q` axis.** For
`Ω ≠ 0`, the middle labeled axis — index `1`, the axis carrying
the separatrix saddles by `sep_saddle` — is the unique labeled
axis with frozen product `rankQ > 0`: `rankQAxis1 > 0` while
`rankQAxis0 < 0` and `rankQAxis2 < 0` (Brick 2's trichotomy:
positive iff the moment is strictly intermediate). -/
theorem saddle_axis_rankQ_signs (b : SolidBody) (h12 : b.I1 < b.I2)
    (h23 : b.I2 < b.I3) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    0 < rankQAxis1 b Ω ∧ rankQAxis0 b Ω < 0 ∧ rankQAxis2 b Ω < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (rankQAxis1_pos_iff b Ω hΩ).mpr (Or.inr ⟨h12, h23⟩)
  · exact (rankQAxis0_neg_iff b Ω hΩ).mpr
      (Or.inl ⟨h12, lt_trans h12 h23⟩)
  · exact (rankQAxis2_neg_iff b Ω hΩ).mpr
      (Or.inr ⟨lt_trans h12 h23, h23⟩)

/-- **Saddle-label exchange along a moment path** (Brick 2's
`rankQ_crossing`, with its portrait reading). Along a continuous
path of positive labeled moments on `[0, 1]` carrying the
designated axis `k` from strictly intermediate to strictly
extremal, there is a crossing time at which `Iₖ` ties a neighbor,
and the frozen product passes from positive to negative. Read
through `saddle_axis_rankQ_signs`: at the start the designated
axis is the one whose frozen portrait (at its own sorted instant)
carries the separatrix saddle; at the end it is not — the saddle's
labeled axis is exchanged across the crossing. A statement about
the family of frozen portraits along the path, not about any
trajectory. -/
theorem saddle_label_exchange (Ii Ij Ik : ℝ → ℝ) (Ω : ℝ)
    (hΩ : Ω ≠ 0) (hIi : Continuous Ii) (hIj : Continuous Ij)
    (hIk : Continuous Ik)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < Ii t ∧ 0 < Ij t ∧ 0 < Ik t)
    (hstart : (Ii 0 < Ik 0 ∧ Ik 0 < Ij 0) ∨
      (Ij 0 < Ik 0 ∧ Ik 0 < Ii 0))
    (hend : (Ik 1 < Ii 1 ∧ Ik 1 < Ij 1) ∨
      (Ii 1 < Ik 1 ∧ Ij 1 < Ik 1)) :
    (∃ t ∈ Set.Icc (0 : ℝ) 1, Ik t = Ii t ∨ Ik t = Ij t) ∧
      0 < rankQPath Ii Ij Ik Ω 0 ∧
      rankQPath Ii Ij Ik Ω 1 < 0 :=
  rankQ_crossing Ii Ij Ik Ω hΩ hIi hIj hIk hpos hstart hend

end ThetLogos
