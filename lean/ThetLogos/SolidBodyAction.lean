import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import ThetLogos.SolidBodyActionPin

/-!
# ThetLogos.SolidBodyAction — UA-3 CONTENT: the rent theorems

The derivation, in the order it is proved:

1. **Algebra engine** (`sb_firstVar_ibp`): the first-variation
   integrand factors pointwise as a total derivative plus the
   bulk pairing `Σᵢ ξᵢ · (−Iᵢ·(ω'ᵢ − eulerRHSᵢ))`. Pure algebra
   (`field_simp`/`ring` after the module's simp expansions).
2. **Fundamental lemma** (`sb_integral_eq_zero_imp`): a continuous
   field whose pairing integral against every endpoint-vanishing
   differentiable `ξ` vanishes on a window vanishes at every
   interior point (squared-bump test field).
3. **Weak-derivative core** (`sb_firstVar_update`,
   `sb_weak_deriv_eq`): stationarity tested against the
   single-coordinate fields `φ·eᵢ₀` puts no derivative on `ω`:
   it says exactly that each momentum coordinate `H = Iᵢ₀·ωᵢ₀`
   has the continuous field `K = Iᵢ₀·eulerRHSᵢ₀(ω)` as a *weak*
   derivative, and a continuous weak derivative is the
   derivative — the defect `H − ∫K` pairs trivially against
   every `C¹` slope, hence is constant on every window.
4. **The rent theorem** (`sb_stationary_iff_euler`):
   stationarity under the frame variation class ⟺ the module's
   Euler hypothesis verbatim. Forward by (3); reverse by the
   algebra engine read backwards, with the integrability case
   split (where the boundary-pairing derivative is not
   integrable, the interval integral is `0` by convention and
   there is nothing to prove).
5. **Windowed bulk vanishing** (`sb_bulk_vanishes`) and the
   **failure capability** (`sb_const_stationary_iff`):
   corollaries of (4). Stationarity is a genuine constraint:
   the constant path at `z` is stationary iff
   `eulerRHS b z = 0`, so most constant paths fail it.
6. **Conservation corollaries**
   (`sb_stationary_rotEnergy_const`,
   `sb_stationary_angMomSq_const`): a stationary trajectory
   satisfies the module's T4 hypothesis (via the rent theorem),
   so the module's landed conservation theorems apply with the
   hypothesis *derived*, not assumed.

REPAIR RECORD (2026-11-07, second resume — proofs only, no
statement changed): the first content draft (67a9213, unbuilt)
ran the forward direction through the fundamental lemma
applied to the bulk field, which needs the bulk field
continuous. Under the pin's differentiable-only hypotheses
`ω'` need not be continuous, the bulk field need not be
either, and the windowed integral identity the draft used
fails for wild variations (a non-integrable derivative makes
the interval integral a junk `0`, not a boundary difference).
The statements were all correct; the proof architecture is
repaired as in (3)–(4) above — the derivative is put on the
test field, never on `ω`. The pin's own defect (variable
capture in `sbStationary`) is repaired by the
parent-authorized alpha-rename recorded in the pin.

**NO CLAIM; dials 0/4; Dial 2 = 0.** Dial-ineligible mechanics,
in a gravity-free house, exactly as pinned.
-/

namespace ThetLogos

@[simp] lemma sbCross_zero (x : Fin 3 → ℝ) : sbCross x 0 = ![x 2 * 0 - x 1 * 0, x 0 * 0 - x 2 * 0, x 1 * 0 - x 0 * 0] := by
  funext i
  fin_cases i <;> simp [sbCross]

@[simp] lemma sbCross_apply_zero (x y : Fin 3 → ℝ) :
    sbCross x y 0 = x 1 * y 2 - x 2 * y 1 := rfl

@[simp] lemma sbCross_apply_one (x y : Fin 3 → ℝ) :
    sbCross x y 1 = x 2 * y 0 - x 0 * y 2 := rfl

@[simp] lemma sbCross_apply_two (x y : Fin 3 → ℝ) :
    sbCross x y 2 = x 0 * y 1 - x 1 * y 0 := rfl

/-- The bulk field of the first variation: `Fᵢ t = −Iᵢ·(ω'ᵢ t −
eulerRHSᵢ(ω t))`. Stationarity will force this to vanish; it is
*defined* here only as the pairing partner of `ξ` in the IBP
identity — the action and the variation class (pin) never mention
it. -/
noncomputable def sbBulk (b : SolidBody) (ω : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun i => - momInertia b i * (deriv (fun s => ω s i) t - eulerRHS b (ω t) i)

/-- **The IBP identity (pointwise).** The first-variation integrand
is, at every time, the derivative of the boundary pairing plus the
bulk pairing — provided the products `Lᵢ·ξᵢ` differentiate by the
product rule at `t` (the `hξ`/`hω` hypotheses, discharged in the
rent theorem from differentiability). Pure algebra given those
derivative values. -/
theorem sb_firstVar_ibp (b : SolidBody) (ω ξ : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hprod : ∀ i : Fin 3, HasDerivAt (fun s => angMom b (ω s) i * ξ s i)
      (deriv (fun s => ω s i) t * momInertia b i * ξ t i
        + angMom b (ω t) i * deriv (fun s => ξ s i) t) t) :
    sbFirstVar b ω ξ t
      = deriv (fun s => ∑ i, angMom b (ω s) i * ξ s i) t
        + ∑ i, ξ t i * sbBulk b ω t i := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have hderiv : deriv (fun s => ∑ i, angMom b (ω s) i * ξ s i) t
      = ∑ i, (deriv (fun s => ω s i) t * momInertia b i * ξ t i
        + angMom b (ω t) i * deriv (fun s => ξ s i) t) :=
    (HasDerivAt.fun_sum (fun i _ => hprod i)).deriv
  rw [hderiv]
  simp only [sbFirstVar, sbFrameVar, sbBulk, angMom, Fin.sum_univ_three,
    sbCross_apply_zero, sbCross_apply_one, sbCross_apply_two,
    momInertia_zero, momInertia_one, momInertia_two,
    eulerRHS_zero, eulerRHS_one, eulerRHS_two]
  field_simp
  ring

/-! ## The fundamental lemma at this seat

A continuous field `F : ℝ → Fin 3 → ℝ` whose pairing integral
against every endpoint-vanishing differentiable `ξ` is zero, on
every sub-horizon, vanishes identically. Proof: if `F t₀ i₀ ≠ 0`,
test against a `ξ` supported in a small interval around `t₀` with
the single coordinate `ξ i₀ = φ²·sign` built from a smooth bump `φ`
(`Real.smoothTransition`-free: the bump is assembled from
`exp (−1/x)` pieces via `Real.expNegInvGlue` — here we use the
elementary polynomial bump on `Finset`-free grounds: `ξ i₀ t =
(F t₀ i₀) * (bump t)²` with `bump` a `C¹` tent of compact support;
the square makes the integrand `F t i₀ * F t₀ i₀ * bump² ≥
(1/2)(F t₀ i₀)²·bump²` near `t₀`, strictly positive somewhere, so
the integral is positive — contradiction. The tent used is
`C¹` because it is a product of two Lipschitz ramps squared —
differentiability is checked directly. -/

/-- The bump profile on `[c, d]`: rises smoothly from `0` to `1`
on the first half, falls back to `0` on the second half — built
from `Real.smoothTransition`. Nonnegative, `C^∞`, supported in
`[c, d]`, and identically `1` at the midpoint. -/
noncomputable def sbBump (c d t : ℝ) : ℝ :=
  Real.smoothTransition ((2 * t - 2 * c) / (d - c)) *
    Real.smoothTransition ((2 * d - 2 * t) / (d - c))

lemma sbBump_nonneg (c d t : ℝ) : 0 ≤ sbBump c d t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma sbBump_differentiable (c d : ℝ) : Differentiable ℝ (sbBump c d) := by
  have hst : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have h1 : Differentiable ℝ fun t => (2 * t - 2 * c) / (d - c) :=
    ((differentiable_id.const_mul 2).sub_const (2 * c)).div_const (d - c)
  have h2 : Differentiable ℝ fun t => (2 * d - 2 * t) / (d - c) :=
    ((differentiable_const (2 * d)).sub
      (differentiable_id.const_mul 2)).div_const (d - c)
  unfold sbBump
  exact (hst.comp h1).mul (hst.comp h2)

/-- The test field of the fundamental lemma: concentrated in the
single coordinate `i₀`, the bump squared times the constant value
`F t₀ i₀` (orienting the pairing to `F t i₀ · F t₀ i₀ · bump²`). -/
noncomputable def sbTestField (F : ℝ → Fin 3 → ℝ) (t₀ : ℝ) (i₀ : Fin 3)
    (c d : ℝ) : ℝ → Fin 3 → ℝ :=
  fun t => Function.update 0 i₀ (F t₀ i₀ * (sbBump c d t) ^ 2)

lemma sbTestField_differentiable (F : ℝ → Fin 3 → ℝ) (t₀ : ℝ)
    (i₀ : Fin 3) (c d : ℝ) :
    ∀ i, Differentiable ℝ (fun s => sbTestField F t₀ i₀ c d s i) := by
  intro i
  by_cases hi : i = i₀
  · subst hi
    simp only [sbTestField, Function.update_self]
    exact ((sbBump_differentiable c d).pow 2).const_mul _
  · have : (fun s => sbTestField F t₀ i₀ c d s i) = fun _ => (0 : ℝ) := by
      funext s
      simp [sbTestField, Function.update_of_ne hi]
    rw [this]
    exact differentiable_const _

/-- The test field vanishes outside `[c, d]` (the bump does), in
particular at any point `≤ c` or `≥ d`. -/
lemma sbBump_eq_zero_of_le (hcd : c < d) (ht : t ≤ c) : sbBump c d t = 0 := by
  unfold sbBump
  have h1 : (2 * t - 2 * c) / (d - c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

lemma sbBump_eq_zero_of_ge (hcd : c < d) (ht : d ≤ t) : sbBump c d t = 0 := by
  unfold sbBump
  have h2 : (2 * d - 2 * t) / (d - c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]

lemma sbBump_mid (hcd : c < d) : sbBump c d ((c + d) / 2) = 1 := by
  unfold sbBump
  have hne : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcd)
  have h1 : (2 * ((c + d) / 2) - 2 * c) / (d - c) = 1 := by
    rw [div_eq_iff hne]; ring
  have h2 : (2 * d - 2 * ((c + d) / 2)) / (d - c) = 1 := by
    rw [div_eq_iff hne]; ring
  rw [h1, h2, Real.smoothTransition.one, mul_one]

/-- **Fundamental lemma.** If the continuous field `F` pairs to
zero against every admissible variation on `[a, b]`, then `F`
vanishes at every interior point. The test field is the squared
bump concentrated near the point, in the single offending
coordinate, oriented by the value of `F` there: the pairing
integrand becomes `F t i₀ · F t₀ i₀ · bump²`, nonnegative on the
whole line, and `≥ (F t₀ i₀)²/2 · bump²` on a neighbourhood of
`t₀` where `F · i₀` keeps half its value; the integral over that
neighbourhood is positive (a nonnegative continuous integrand,
positive at the bump's peak), contradicting the vanishing. -/
theorem sb_integral_eq_zero_imp {a b : ℝ} (hab : a < b) (F : ℝ → Fin 3 → ℝ)
    (hF : Continuous fun t => F t)
    (h : ∀ ξ : ℝ → Fin 3 → ℝ, (∀ i, Differentiable ℝ (fun s => ξ s i)) →
      ξ a = 0 → ξ b = 0 →
      ∫ t in a..b, (∑ i, ξ t i * F t i) = 0)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo a b) (i₀ : Fin 3) : F t₀ i₀ = 0 := by
  by_contra hne
  have hcont : Continuous fun t => F t i₀ * F t₀ i₀ :=
    ((continuous_apply i₀).comp hF).mul continuous_const
  -- a neighbourhood (c, d) ∋ t₀ inside (0, T) where the product keeps half value
  have hval : (F t₀ i₀) ^ 2 / 2 < (F t₀ i₀) * F t₀ i₀ := by
    have : (0:ℝ) < F t₀ i₀ * F t₀ i₀ := by
      rw [← sq]; exact sq_pos_of_ne_zero hne
    linarith
  have hpre := (hcont.tendsto t₀).eventually (eventually_gt_nhds hval)
  rw [Metric.eventually_nhds_iff] at hpre
  obtain ⟨ε, hε, hεball⟩ := hpre
  obtain ⟨c, d, hca, hct₀, htd, hdb, hball⟩ :
      ∃ c d : ℝ, a < c ∧ c < t₀ ∧ t₀ < d ∧ d < b ∧
        Set.Ioo c d ⊆ Metric.ball t₀ ε := by
    refine ⟨max (t₀ - ε / 2) ((a + t₀) / 2), min (t₀ + ε / 2) ((t₀ + b) / 2),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_max_of_lt_right (by linarith [ht₀.1])
    · exact max_lt (by linarith) (by linarith [ht₀.1])
    · exact lt_min (by linarith) (by linarith [ht₀.2])
    · have h1 := min_le_right (t₀ + ε / 2) ((t₀ + b) / 2)
      have h2 : min (t₀ + ε / 2) ((t₀ + b) / 2) < b := by linarith [ht₀.2]
      exact h2
    · intro x hx
      simp only [Metric.mem_ball, Real.dist_eq]
      have hx1 : max (t₀ - ε / 2) ((a + t₀) / 2) < x := hx.1
      have hx2 : x < min (t₀ + ε / 2) ((t₀ + b) / 2) := hx.2
      have h1 : t₀ - ε / 2 < x := lt_of_le_of_lt (le_max_left _ _) hx1
      have h2 : x < t₀ + ε / 2 := lt_of_lt_of_le hx2 (min_le_left _ _)
      rw [abs_sub_lt_iff]
      constructor <;> linarith
  have hcd : c < d := lt_trans hct₀ htd
  -- the pairing integral for the test field, computed two ways
  set ξ := sbTestField F t₀ i₀ c d with hξdef
  have hξa : ξ a = 0 := by
    have hb : sbBump c d a = 0 := sbBump_eq_zero_of_le hcd (le_of_lt hca)
    simp [hξdef, sbTestField, hb]
  have hξb : ξ b = 0 := by
    have hb : sbBump c d b = 0 := sbBump_eq_zero_of_ge hcd (le_of_lt hdb)
    simp [hξdef, sbTestField, hb]
  have hpair := h ξ (sbTestField_differentiable F t₀ i₀ c d) hξa hξb
  -- the integrand of the pairing is `F t i₀ * F t₀ i₀ * bump²`
  have hξi₀ : ∀ t : ℝ, ξ t i₀ = F t₀ i₀ * (sbBump c d t) ^ 2 := by
    intro t
    simp only [hξdef, sbTestField, Function.update_self]
  have hξne : ∀ (t : ℝ) (j : Fin 3), j ≠ i₀ → ξ t j = 0 := by
    intro t j hj
    simp only [hξdef, sbTestField, Function.update_of_ne hj, Pi.zero_apply]
  have hinteg : ∀ t : ℝ, (∑ i, ξ t i * F t i)
      = F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 := by
    intro t
    rw [Finset.sum_eq_single i₀
      (fun j _ hj => by rw [hξne t j hj, zero_mul])
      (fun hmem => absurd (Finset.mem_univ i₀) hmem), hξi₀ t]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hinteg t)] at hpair
  -- the integrand is nonnegative everywhere
  have hnn : ∀ t : ℝ, 0 ≤ F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 := by
    intro t
    by_cases ht : t ∈ Set.Ioo c d
    · have hge := hεball (hball ht)
      have hhalf : (F t₀ i₀) ^ 2 / 2 ≤ F t i₀ * F t₀ i₀ := le_of_lt hge
      calc (0:ℝ) ≤ (F t₀ i₀) ^ 2 / 2 * (sbBump c d t) ^ 2 :=
            mul_nonneg (by positivity) (sq_nonneg _)
        _ ≤ (F t i₀ * F t₀ i₀) * (sbBump c d t) ^ 2 :=
            mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
        _ = F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 := by ring
    · by_cases htc : t ≤ c
      · rw [sbBump_eq_zero_of_le hcd htc]; simp
      · have htd' : d ≤ t := le_of_not_gt (fun hh => ht ⟨lt_of_not_ge htc, hh⟩)
        rw [sbBump_eq_zero_of_ge hcd htd']; simp
  have hbump : Continuous fun t => sbBump c d t := by
    have hst : Continuous Real.smoothTransition :=
      (Real.smoothTransition.contDiff (n := 1)).continuous
    have h1 : Continuous fun t => (2 * t - 2 * c) / (d - c) :=
      ((continuous_id.const_mul 2).sub continuous_const).div_const (d - c)
    have h2 : Continuous fun t => (2 * d - 2 * t) / (d - c) :=
      ((continuous_const.sub (continuous_id.const_mul 2)).div_const (d - c))
    unfold sbBump
    exact (hst.comp h1).mul (hst.comp h2)
  have hcont' : Continuous fun t => F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
    (((continuous_apply i₀).comp hF).mul continuous_const).mul (hbump.pow 2)
  have hint : IntervalIntegrable (fun t => F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
      MeasureTheory.volume a b := hcont'.intervalIntegrable a b
  -- split (0,T) = (0,c)+(c,d)+(d,T); the integrand vanishes on the outer pieces
  have hsplit : (∫ t in a..b, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
      = ∫ t in c..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 := by
    have h0c : IntervalIntegrable (fun t => F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
        MeasureTheory.volume a c := hcont'.intervalIntegrable a c
    have h0d : IntervalIntegrable (fun t => F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
        MeasureTheory.volume a d := hcont'.intervalIntegrable a d
    have e1 : (∫ t in a..c, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2) = 0 := by
      have hcongr : (∫ t in a..c, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
          = ∫ t in a..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hca.le] at ht
        show F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 = 0
        rw [sbBump_eq_zero_of_le hcd ht.2]; simp
      rw [hcongr, intervalIntegral.integral_zero]
    have e2 : (∫ t in d..b, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2) = 0 := by
      have hcongr : (∫ t in d..b, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
          = ∫ t in d..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hdb.le] at ht
        show F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 = 0
        rw [sbBump_eq_zero_of_ge hcd ht.1]; simp
      rw [hcongr, intervalIntegral.integral_zero]
    have h1 : (∫ t in a..b, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
        = (∫ t in a..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
          + ∫ t in d..b, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
      (intervalIntegral.integral_add_adjacent_intervals h0d
        (hcont'.intervalIntegrable d b)).symm
    have h2 : (∫ t in a..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
        = (∫ t in a..c, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
          + ∫ t in c..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
      (intervalIntegral.integral_add_adjacent_intervals h0c
        (hcont'.intervalIntegrable c d)).symm
    rw [h1, h2, e1, e2, zero_add, add_zero]
  rw [hsplit] at hpair
  -- positivity: the integrand is continuous and positive at the
  -- midpoint, hence positive on a neighbourhood, and nonnegative
  -- everywhere, so the integral over (c,d) is positive by
  -- `intervalIntegral_pos_of_pos_on` applied to a small sub-interval
  -- plus nonnegativity on the rest.
  have hmidpos : (0:ℝ) < F ((c + d) / 2) i₀ * F t₀ i₀ * (sbBump c d ((c + d) / 2)) ^ 2 := by
    have hmem : (c + d) / 2 ∈ Set.Ioo c d := ⟨by linarith, by linarith⟩
    have hge := hεball (hball hmem)
    rw [sbBump_mid hcd]
    nlinarith [sq_pos_of_ne_zero hne, hge]
  have hnbhd := (hcont'.tendsto _).eventually (eventually_gt_nhds hmidpos)
  rw [Metric.eventually_nhds_iff] at hnbhd
  obtain ⟨δ, hδ, hδball⟩ := hnbhd
  set e := max c ((c + d) / 2 - δ / 2) with hedef
  set f := min d ((c + d) / 2 + δ / 2) with hfdef
  have hef : e < f := by
    simp only [hedef, hfdef, max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  have hec : c ≤ e := le_max_left _ _
  have hfd : f ≤ d := min_le_left _ _
  have hsubint : IntervalIntegrable
      (fun t => F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2) MeasureTheory.volume c d :=
    hcont'.intervalIntegrable c d
  have hpos_ef : (0:ℝ) < ∫ t in e..f, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont'.intervalIntegrable e f) _ hef
    intro x hx
    have hxball : x ∈ Metric.ball ((c + d) / 2) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hx1 : (c + d) / 2 - δ / 2 < x :=
        lt_of_le_of_lt (le_max_right _ _) hx.1
      have hx2 : x < (c + d) / 2 + δ / 2 :=
        lt_of_lt_of_le hx.2 (min_le_right _ _)
      rw [abs_sub_lt_iff]; constructor <;> linarith
    exact hδball hxball
  have hnn_ce : (0:ℝ) ≤ ∫ t in c..e, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hec (fun t => hnn t)
  have hnn_fd : (0:ℝ) ≤ ∫ t in f..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hfd (fun t => hnn t)
  have hadd1 : (∫ t in c..e, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
      + ∫ t in e..f, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2
      = ∫ t in c..f, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont'.intervalIntegrable c e) (hcont'.intervalIntegrable e f)
  have hadd2 : (∫ t in c..f, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2)
      + ∫ t in f..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2
      = ∫ t in c..d, F t i₀ * F t₀ i₀ * (sbBump c d t) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont'.intervalIntegrable c f) (hcont'.intervalIntegrable f d)
  linarith [hpair, hpos_ef, hnn_ce, hnn_fd, hadd1, hadd2]

/-! ## The weak-derivative core

Stationarity tested against a single-coordinate field `φ·eᵢ₀`
never differentiates `ω`: the first variation at that field is
`Iᵢ₀·ωᵢ₀·φ' + φ·(Iᵢ₀·eulerRHSᵢ₀(ω))` pointwise, so stationarity
says the momentum coordinate has the Euler field as a *weak*
derivative. The scalar lemma `sb_weak_deriv_eq` is the
bootstrap: a continuous weak derivative is the derivative. -/

/-- The single-coordinate test field `φ·eᵢ₀` is admissible:
each coordinate is differentiable (it is `φ` at `i₀` and `0`
elsewhere). -/
lemma sb_update_differentiable (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (i₀ : Fin 3) :
    ∀ j, Differentiable ℝ
      (fun s => Function.update (0 : Fin 3 → ℝ) i₀ (φ s) j) := by
  intro j
  by_cases hj : j = i₀
  · subst hj
    have hfun : (fun s => Function.update (0 : Fin 3 → ℝ) j (φ s) j)
        = φ := by
      funext s; simp
    rw [hfun]; exact hφ
  · have hfun : (fun s => Function.update (0 : Fin 3 → ℝ) i₀ (φ s) j)
        = fun _ => (0 : ℝ) := by
      funext s; simp [Function.update_of_ne hj]
    rw [hfun]; exact differentiable_const _

/-- The single-coordinate test field vanishes wherever `φ`
does. -/
lemma sb_update_eq_zero (φ : ℝ → ℝ) (i₀ : Fin 3) {x : ℝ} (hx : φ x = 0) :
    (fun s => Function.update (0 : Fin 3 → ℝ) i₀ (φ s)) x = 0 := by
  funext j
  by_cases hj : j = i₀
  · subst hj; simp [hx]
  · simp [Function.update_of_ne hj]

/-- The first variation at a single-coordinate test field,
pointwise: only the `i₀` momentum pairs with `φ'`, and the
frame pairing collapses to `φ` times the Euler field at `i₀`
(times the moment). Pure algebra — no derivative of `ω`
appears. -/
lemma sb_firstVar_update (b : SolidBody) (ω : ℝ → Fin 3 → ℝ) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (i₀ : Fin 3) (t : ℝ) :
    sbFirstVar b ω (fun s => Function.update (0 : Fin 3 → ℝ) i₀ (φ s)) t
      = angMom b (ω t) i₀ * deriv φ t
        + φ t * (momInertia b i₀ * eulerRHS b (ω t) i₀) := by
  have h1 : b.I1 ≠ 0 := b.I1_pos.ne'
  have h2 : b.I2 ≠ 0 := b.I2_pos.ne'
  have h3 : b.I3 ≠ 0 := b.I3_pos.ne'
  have hderiv : ∀ j : Fin 3,
      deriv (fun s => Function.update (0 : Fin 3 → ℝ) i₀ (φ s) j) t
        = if j = i₀ then deriv φ t else 0 := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      rw [if_pos rfl]
      have hfun : (fun s => Function.update (0 : Fin 3 → ℝ) j (φ s) j)
          = φ := by
        funext s; simp
      rw [hfun]
    · rw [if_neg hj]
      have hfun : (fun s => Function.update (0 : Fin 3 → ℝ) i₀ (φ s) j)
          = fun _ => (0 : ℝ) := by
        funext s; simp [Function.update_of_ne hj]
      rw [hfun]; simp
  fin_cases i₀ <;>
    simp only [sbFirstVar, sbFrameVar, Fin.sum_univ_three, hderiv] <;>
    simp [angMom, sbCross_apply_zero, sbCross_apply_one, sbCross_apply_two,
      momInertia_zero, momInertia_one, momInertia_two,
      eulerRHS_zero, eulerRHS_one, eulerRHS_two] <;>
    field_simp <;> ring

/-- **Weak derivative = derivative.** If the continuous field
`H` pairs against every `C¹` endpoint-vanishing slope exactly
like the continuous field `K` (integration by parts with no
boundary terms), then `H` is differentiable at every interior
point with derivative `K`. Proof: the defect
`R = H − (H c + ∫K)` pairs to zero against every `C¹` slope;
testing against the slope of `∫(R − mean)` gives
`∫(R − mean)² = 0`, and a continuous square with zero integral
forces `R ≡ mean` on the window — so `R` is locally constant
at `t₀`, and `H = (H c + ∫K) + R` differentiates to `K t₀`. -/
theorem sb_weak_deriv_eq {c d : ℝ} (hcd : c < d) (H K : ℝ → ℝ)
    (hH : Continuous H) (hK : Continuous K)
    (h : ∀ φ : ℝ → ℝ, Differentiable ℝ φ → Continuous (deriv φ) →
      φ c = 0 → φ d = 0 →
      ∫ t in c..d, (H t * deriv φ t + φ t * K t) = 0)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo c d) :
    deriv H t₀ = K t₀ := by
  have hWcont : Continuous fun t => ∫ s in c..t, K s :=
    (intervalIntegral.differentiable_integral_of_continuous hK).continuous
  have hRcont : Continuous fun t => H t - (H c + ∫ s in c..t, K s) :=
    hH.sub (continuous_const.add hWcont)
  -- the defect pairs trivially against every C¹ slope
  have hkey : ∀ φ : ℝ → ℝ, Differentiable ℝ φ → Continuous (deriv φ) →
      φ c = 0 → φ d = 0 →
      ∫ t in c..d, ((H t - (H c + ∫ s in c..t, K s)) * deriv φ t) = 0 := by
    intro φ hφ hφ' hφc hφd
    have hIntφ' : ∫ t in c..d, deriv φ t = 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => (hφ x).hasDerivAt) (hφ'.intervalIntegrable c d), hφd, hφc,
        sub_self]
    have hIBP : ∫ t in c..d, (K t * φ t
        + (∫ s in c..t, K s) * deriv φ t) = 0 := by
      have hder : ∀ x ∈ Set.uIcc c d, HasDerivAt
          (fun t => (∫ s in c..t, K s) * φ t)
          (K x * φ x + (∫ s in c..x, K s) * deriv φ x) x := by
        intro x _
        exact (hK.integral_hasStrictDerivAt c x).hasDerivAt.mul
          (hφ x).hasDerivAt
      have hint : IntervalIntegrable (fun t => K t * φ t
          + (∫ s in c..t, K s) * deriv φ t) MeasureTheory.volume c d :=
        ((hK.mul hφ.continuous).intervalIntegrable c d).add
          ((hWcont.mul hφ').intervalIntegrable c d)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
      simp [hφc, hφd]
    have hintH : IntervalIntegrable (fun t => H t * deriv φ t)
        MeasureTheory.volume c d := (hH.mul hφ').intervalIntegrable c d
    have hintK : IntervalIntegrable (fun t => φ t * K t)
        MeasureTheory.volume c d :=
      ((hφ.continuous).mul hK).intervalIntegrable c d
    have hintW : IntervalIntegrable
        (fun t => (∫ s in c..t, K s) * deriv φ t) MeasureTheory.volume c d :=
      (hWcont.mul hφ').intervalIntegrable c d
    have hintKφ : IntervalIntegrable (fun t => K t * φ t)
        MeasureTheory.volume c d :=
      (hK.mul hφ.continuous).intervalIntegrable c d
    have hintc : IntervalIntegrable (fun t => H c * deriv φ t)
        MeasureTheory.volume c d :=
      (continuous_const.mul hφ').intervalIntegrable c d
    have hsplit : ∫ t in c..d, ((H t - (H c + ∫ s in c..t, K s)) * deriv φ t)
        = (∫ t in c..d, (H t * deriv φ t + φ t * K t))
          - (∫ t in c..d, (K t * φ t + (∫ s in c..t, K s) * deriv φ t))
          - H c * ∫ t in c..d, deriv φ t := by
      rw [← intervalIntegral.integral_sub (hintH.add hintK) (hintKφ.add hintW),
        ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub
          ((hintH.add hintK).sub (hintKφ.add hintW)) hintc]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [hsplit, h φ hφ hφ' hφc hφd, hIBP, hIntφ', mul_zero, sub_zero, sub_zero]
  -- the mean of the defect, and `∫ (R − mean) = 0`
  set m : ℝ := (∫ t in c..d, (H t - (H c + ∫ s in c..t, K s))) / (d - c)
    with hmdef
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcd)
  have hm : (d - c) * m = ∫ t in c..d, (H t - (H c + ∫ s in c..t, K s)) :=
    mul_div_cancel₀ _ hdc
  have hgint : ∫ t in c..d, ((H t - (H c + ∫ s in c..t, K s)) - m) = 0 := by
    rw [intervalIntegral.integral_sub (hRcont.intervalIntegrable c d)
      (continuous_const.intervalIntegrable c d), intervalIntegral.integral_const,
      smul_eq_mul, hm, sub_self]
  -- Φ = ∫(R − mean): C¹, endpoint-vanishing, derivative `R − mean`
  have hΦdiff : Differentiable ℝ (fun t => ∫ s in c..t,
      ((H s - (H c + ∫ u in c..s, K u)) - m)) :=
    intervalIntegral.differentiable_integral_of_continuous
      (hRcont.sub continuous_const)
  have hΦderiv : deriv (fun t => ∫ s in c..t,
        ((H s - (H c + ∫ u in c..s, K u)) - m))
      = fun t => (H t - (H c + ∫ s in c..t, K s)) - m := by
    funext t
    exact (hRcont.sub continuous_const).deriv_integral _ c t
  have hΦC1 : Continuous (deriv (fun t => ∫ s in c..t,
      ((H s - (H c + ∫ u in c..s, K u)) - m))) := by
    rw [hΦderiv]; exact hRcont.sub continuous_const
  have hΦc : (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) c
      = 0 := intervalIntegral.integral_same
  have hΦd : (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) d
      = 0 := hgint
  have hIntΦ' : ∫ t in c..d, deriv (fun t => ∫ s in c..t,
      ((H s - (H c + ∫ u in c..s, K u)) - m)) t = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hΦdiff x).hasDerivAt) (hΦC1.intervalIntegrable c d)]
    show (∫ s in c..d, ((H s - (H c + ∫ u in c..s, K u)) - m))
        - (∫ s in c..c, ((H s - (H c + ∫ u in c..s, K u)) - m)) = 0
    rw [hgint, intervalIntegral.integral_same, sub_zero]
  have hsq0 : ∫ t in c..d, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
      = 0 := by
    have hΦint := hkey (fun t => ∫ s in c..t,
      ((H s - (H c + ∫ u in c..s, K u)) - m)) hΦdiff hΦC1 hΦc hΦd
    have hIntRΦ : IntervalIntegrable (fun t => (H t - (H c + ∫ s in c..t, K s))
        * deriv (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t)
        MeasureTheory.volume c d := by
      have hc : Continuous fun t => (H t - (H c + ∫ s in c..t, K s))
          * deriv (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t :=
        hRcont.mul hΦC1
      exact hc.intervalIntegrable c d
    have hIntmΦ : IntervalIntegrable (fun t => m * deriv
        (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t)
        MeasureTheory.volume c d := by
      have hc : Continuous fun t => m * deriv
          (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t :=
        continuous_const.mul hΦC1
      exact hc.intervalIntegrable c d
    have hInt2 : ∫ t in c..d, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
        = (∫ t in c..d, (H t - (H c + ∫ s in c..t, K s)) * deriv
            (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t)
          - m * ∫ t in c..d, deriv
            (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hIntRΦ hIntmΦ]
      apply intervalIntegral.integral_congr
      intro t _
      show ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
          = (H t - (H c + ∫ s in c..t, K s)) * deriv
              (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t
            - m * deriv
              (fun t => ∫ s in c..t, ((H s - (H c + ∫ u in c..s, K u)) - m)) t
      have hdt := congrFun hΦderiv t
      rw [hdt]; ring
    rw [hInt2, hΦint, hIntΦ', mul_zero, sub_zero]
  -- a continuous square with zero integral: the defect is its mean
  have hRm : ∀ t ∈ Set.Icc c d,
      (H t - (H c + ∫ s in c..t, K s)) = m := by
    intro t₁ ht₁
    by_contra hne
    have hgcont : Continuous fun t =>
        ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2 :=
      (hRcont.sub continuous_const).pow 2
    have hg1 : (0:ℝ) < ((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hpre := (hgcont.tendsto t₁).eventually
      (eventually_gt_nhds (half_lt_self hg1))
    rw [Metric.eventually_nhds_iff] at hpre
    obtain ⟨δ, hδ, hδball⟩ := hpre
    set e := max c (t₁ - δ / 2) with hedef
    set f := min d (t₁ + δ / 2) with hfdef
    have hec : c ≤ e := le_max_left _ _
    have hfd : f ≤ d := min_le_left _ _
    have hef : e < f := by
      simp only [hedef, hfdef, max_lt_iff, lt_min_iff]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [ht₁.1, ht₁.2, hcd, hδ]
    have hIntcd : IntervalIntegrable
        (fun t => ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2)
        MeasureTheory.volume c d := hgcont.intervalIntegrable c d
    have hglow : ∀ t ∈ Set.Icc e f,
        ((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2
          ≤ ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2 := by
      intro t ht
      have hball : t ∈ Metric.ball t₁ δ := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hx1 : t₁ - δ / 2 ≤ t := le_trans (le_max_right _ _) ht.1
        have hx2 : t ≤ t₁ + δ / 2 := le_trans ht.2 (min_le_right _ _)
        rw [abs_sub_lt_iff]; constructor <;> linarith
      exact le_of_lt (hδball hball)
    have hsplit3 : ∫ t in c..d, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
        = (∫ t in c..e, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2)
          + (∫ t in e..f, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2)
          + (∫ t in f..d, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
          (hgcont.intervalIntegrable c e) (hgcont.intervalIntegrable e f),
        intervalIntegral.integral_add_adjacent_intervals
          (hgcont.intervalIntegrable c f) (hgcont.intervalIntegrable f d)]
    have hlow : (f - e) * (((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2)
        ≤ ∫ t in e..f, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2 := by
      have hcongr : ∫ t in e..f, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
          = (∫ t in e..f, (((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2))
            + ∫ t in e..f, (((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
              - ((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2) := by
        have hgint2 : IntervalIntegrable
            (fun t => ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
              - ((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2)
            MeasureTheory.volume e f := by
          have hc2 : Continuous fun t =>
              ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
                - ((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2 :=
            ((hRcont.sub continuous_const).pow 2).sub continuous_const
          exact hc2.intervalIntegrable e f
        rw [← intervalIntegral.integral_add
          (continuous_const.intervalIntegrable e f) hgint2]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      have hnn2 : (0:ℝ) ≤ ∫ t in e..f,
          (((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2
            - ((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2) :=
        intervalIntegral.integral_nonneg hef.le (fun t ht => by
          have hgl := hglow t ht; linarith)
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
      linarith
    have hce : (0:ℝ) ≤ ∫ t in c..e, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hec (fun t => sq_nonneg _)
    have hfd' : (0:ℝ) ≤ ∫ t in f..d, ((H t - (H c + ∫ s in c..t, K s)) - m) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hfd (fun t => sq_nonneg _)
    have hpos : (0:ℝ) < (f - e)
        * (((H t₁ - (H c + ∫ s in c..t₁, K s)) - m) ^ 2 / 2) :=
      mul_pos (sub_pos.mpr hef) (half_pos hg1)
    linarith [hsq0, hsplit3, hlow, hce, hfd', hpos]
  -- the defect is locally constant at t₀, so H differentiates to K
  have hReq : (fun t => H t - (H c + ∫ s in c..t, K s)) =ᶠ[nhds t₀]
      (fun _ => m) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht₀.1 ht₀.2)
      (fun t ht => hRm t (Set.Ioo_subset_Icc_self ht))
  have hR0 : HasDerivAt (fun t => H t - (H c + ∫ s in c..t, K s)) 0 t₀ :=
    (hasDerivAt_const t₀ m).congr_of_eventuallyEq hReq
  have hWH : HasDerivAt
      (fun t => (H c + ∫ s in c..t, K s) + (H t - (H c + ∫ s in c..t, K s)))
      (K t₀ + 0) t₀ :=
    ((hK.integral_hasStrictDerivAt c t₀).hasDerivAt.const_add (H c)).add hR0
  have hfun : (fun t => (H c + ∫ s in c..t, K s)
      + (H t - (H c + ∫ s in c..t, K s))) = H := by
    funext t; ring
  have hHder : HasDerivAt H (K t₀) t₀ := by
    have h2 := hfun ▸ hWH
    simpa using h2
  exact hHder.deriv

/-- **THE RENT THEOREM.** For a differentiable trajectory `ω`,
stationarity under the frame variation class is *equivalent* to
the module's T4 hypothesis verbatim: the Euler equations hold at
every time in every coordinate.

Forward: stationarity tested on the single-coordinate fields
`φ·eᵢ₀` on the window `(t₀ − 1, t₀ + 1)` says the momentum
coordinate `Iᵢ₀·ωᵢ₀` has the continuous field
`Iᵢ₀·eulerRHSᵢ₀(ω)` as weak derivative; by `sb_weak_deriv_eq`
it is the derivative; cancel `Iᵢ₀ > 0`.

Reverse: under the Euler equations the bulk field vanishes
identically, so by the IBP identity the first variation is the
integral of a total derivative. Where that derivative is
integrable, FTC and the endpoint conditions give `0`; where it
is not, the interval integral is `0` by convention. Either way,
stationarity holds. -/
theorem sb_stationary_iff_euler (b : SolidBody)
    (ω : ℝ → Fin 3 → ℝ) (hω : ∀ i, Differentiable ℝ (fun s => ω s i)) :
    sbStationary b ω ↔
      ∀ t i, deriv (fun s => ω s i) t = eulerRHS b (ω t) i := by
  constructor
  · intro hstat t₀ i₀
    have hωc : ∀ i, Continuous fun s => ω s i := fun i => (hω i).continuous
    have hEcont : Continuous fun t => eulerRHS b (ω t) := by
      rw [continuous_pi_iff]
      intro j
      fin_cases j
      · simp only [eulerRHS_zero]
        exact (continuous_const.mul (hωc 1)).mul (hωc 2)
      · simp only [eulerRHS_one]
        exact (continuous_const.mul (hωc 2)).mul (hωc 0)
      · simp only [eulerRHS_two]
        exact (continuous_const.mul (hωc 0)).mul (hωc 1)
    have hI : 0 < momInertia b i₀ := by
      fin_cases i₀ <;>
        simp only [momInertia_zero, momInertia_one, momInertia_two] <;>
        [exact b.I1_pos; exact b.I2_pos; exact b.I3_pos]
    have hH : Continuous fun t => angMom b (ω t) i₀ :=
      (hω i₀).continuous.const_mul _
    have hK : Continuous fun t => momInertia b i₀ * eulerRHS b (ω t) i₀ :=
      continuous_const.mul ((continuous_apply i₀).comp hEcont)
    have hdis : ∀ φ : ℝ → ℝ, Differentiable ℝ φ → Continuous (deriv φ) →
        φ (t₀ - 1) = 0 → φ (t₀ + 1) = 0 →
        ∫ t in (t₀ - 1)..(t₀ + 1), ((fun s => angMom b (ω s) i₀) t
          * deriv φ t + φ t * (fun s => momInertia b i₀
            * eulerRHS b (ω s) i₀) t) = 0 := by
      intro φ hφ hφ' hφa hφb
      have hstat' := hstat (t₀ - 1) (t₀ + 1) (by linarith)
        (fun s => Function.update 0 i₀ (φ s))
        (sb_update_differentiable φ hφ i₀)
        (sb_update_eq_zero φ i₀ hφa) (sb_update_eq_zero φ i₀ hφb)
      have hcongr : (∫ t in (t₀ - 1)..(t₀ + 1),
            ((fun s => angMom b (ω s) i₀) t * deriv φ t
              + φ t * (fun s => momInertia b i₀ * eulerRHS b (ω s) i₀) t))
          = ∫ t in (t₀ - 1)..(t₀ + 1),
            sbFirstVar b ω (fun s => Function.update 0 i₀ (φ s)) t :=
        intervalIntegral.integral_congr
          (fun t _ => (sb_firstVar_update b ω φ hφ i₀ t).symm)
      rw [hcongr]; exact hstat'
    have hweak := sb_weak_deriv_eq (show (t₀ - 1) < t₀ + 1 by linarith)
      (fun t => angMom b (ω t) i₀)
      (fun t => momInertia b i₀ * eulerRHS b (ω t) i₀)
      hH hK hdis t₀ ⟨by linarith, by linarith⟩
    have hderiv : deriv (fun t => angMom b (ω t) i₀) t₀
        = momInertia b i₀ * deriv (fun s => ω s i₀) t₀ :=
      deriv_const_mul _ ((hω i₀) t₀)
    rw [hderiv] at hweak
    exact mul_left_cancel₀ (ne_of_gt hI) hweak
  · intro hEuler a bb hab ξ hξ hξa hξb
    have hprod : ∀ (ξ : ℝ → Fin 3 → ℝ),
        (∀ i, Differentiable ℝ (fun s => ξ s i)) →
        ∀ i (x : ℝ), HasDerivAt (fun s => angMom b (ω s) i * ξ s i)
          (deriv (fun s => ω s i) x * momInertia b i * ξ x i
            + angMom b (ω x) i * deriv (fun s => ξ s i) x) x := by
      intro ξ hξ i x
      have hmul : HasDerivAt (fun s => momInertia b i * ω s i * ξ s i)
          (momInertia b i * deriv (fun s => ω s i) x * ξ x i
            + momInertia b i * ω x i * deriv (fun s => ξ s i) x) x :=
        (((hω i) x).hasDerivAt.const_mul (momInertia b i)).mul
          ((hξ i) x).hasDerivAt
      have hfun : (fun s => angMom b (ω s) i * ξ s i)
          = (fun s => momInertia b i * ω s i * ξ s i) := rfl
      rw [hfun]
      have hval : deriv (fun s => ω s i) x * momInertia b i * ξ x i
            + angMom b (ω x) i * deriv (fun s => ξ s i) x
          = momInertia b i * deriv (fun s => ω s i) x * ξ x i
            + momInertia b i * ω x i * deriv (fun s => ξ s i) x := by
        simp only [angMom]; ring
      rw [hval]; exact hmul
    have hsum : ∀ x : ℝ, HasDerivAt (fun s => ∑ i, angMom b (ω s) i * ξ s i)
        (∑ i, (deriv (fun s => ω s i) x * momInertia b i * ξ x i
          + angMom b (ω x) i * deriv (fun s => ξ s i) x)) x :=
      fun x => HasDerivAt.fun_sum (fun i _ => hprod ξ hξ i x)
    have hfun : (fun t => sbFirstVar b ω ξ t)
        = fun t => deriv (fun s => ∑ i, angMom b (ω s) i * ξ s i) t := by
      funext t
      have hbulk0 : ∀ i : Fin 3, sbBulk b ω t i = 0 := by
        intro i
        simp only [sbBulk, hEuler t i, sub_self, mul_zero, neg_zero]
      rw [sb_firstVar_ibp b ω ξ t (hprod ξ hξ · t), (hsum t).deriv]
      simp [hbulk0]
    have hfunEq : (fun t => deriv (fun s => ∑ i, angMom b (ω s) i * ξ s i) t)
        = fun t => ∑ i, (deriv (fun s => ω s i) t * momInertia b i * ξ t i
            + angMom b (ω t) i * deriv (fun s => ξ s i) t) :=
      funext fun t => (hsum t).deriv
    by_cases hf'int : IntervalIntegrable
        (fun t => deriv (fun s => ∑ i, angMom b (ω s) i * ξ s i) t)
        MeasureTheory.volume a bb
    · rw [hfunEq] at hf'int
      rw [hfun, hfunEq, intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hsum x) hf'int]
      simp [hξa, hξb]
    · rw [hfun, intervalIntegral.integral_undef hf'int]

/-- **Windowed bulk vanishing** (corollary of the rent theorem):
at a stationary trajectory the bulk field vanishes at every
interior point of every window — i.e. the Euler residual is zero
wherever the trajectory is probed. -/
theorem sb_bulk_vanishes (b : SolidBody) {a bb : ℝ} (hab : a < bb)
    (ω : ℝ → Fin 3 → ℝ) (hω : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hstat : sbStationary b ω) :
    ∀ t ∈ Set.Ioo a bb, sbBulk b ω t = 0 := by
  intro t _
  funext j
  have hEj := (sb_stationary_iff_euler b ω hω).mp hstat t j
  simp only [sbBulk, hEj, sub_self, mul_zero, neg_zero, Pi.zero_apply]

/-- **The failure capability.** The constant path at `z` is
stationary iff `eulerRHS b z = 0`. So stationarity is a genuine
constraint with teeth: any constant path at a non-equilibrium
`z` — for a generic body, almost every `z` — is *not*
stationary. -/
theorem sb_const_stationary_iff (b : SolidBody) (z : Fin 3 → ℝ) :
    sbStationary b (fun _ => z) ↔ eulerRHS b z = 0 := by
  have hdiff : ∀ i, Differentiable ℝ (fun _ : ℝ => z i) :=
    fun i => differentiable_const _
  rw [sb_stationary_iff_euler b (fun _ => z) hdiff]
  constructor
  · intro h
    funext i
    have h1 : deriv (fun _ : ℝ => z i) 0 = eulerRHS b z i := h 0 i
    rw [(hasDerivAt_const (0 : ℝ) (z i)).deriv] at h1
    simpa using h1.symm
  · intro h t i
    show deriv (fun _ : ℝ => z i) t = eulerRHS b z i
    rw [(hasDerivAt_const t (z i)).deriv]
    exact (congrFun h i).symm

/-- Conservation, with the hypothesis derived: a stationary
trajectory conserves rotational energy — the module's
`rotEnergy_const`, its T4 hypothesis discharged by the rent
theorem. -/
theorem sb_stationary_rotEnergy_const (b : SolidBody)
    (ω : ℝ → Fin 3 → ℝ) (hω : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hstat : sbStationary b ω) :
    ∀ t, rotEnergy b (ω t) = rotEnergy b (ω 0) :=
  fun t => rotEnergy_const b ω
    ((sb_stationary_iff_euler b ω hω).mp hstat) hω t 0

/-- Conservation of `|L|²`, hypothesis derived the same way. -/
theorem sb_stationary_angMomSq_const (b : SolidBody)
    (ω : ℝ → Fin 3 → ℝ) (hω : ∀ i, Differentiable ℝ (fun s => ω s i))
    (hstat : sbStationary b ω) :
    ∀ t, angMomSq b (ω t) = angMomSq b (ω 0) :=
  fun t => angMomSq_const b ω
    ((sb_stationary_iff_euler b ω hω).mp hstat) hω t 0

end ThetLogos
