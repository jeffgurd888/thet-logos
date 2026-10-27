/-
# ThetLogos.PlaneCrossingBeta4 — κ₄^dep at general (G, ρ):
the closed form of the β⁴ dependent coefficient, and the
sign question reduced to one named component

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. This
module owns the fourth Taylor coefficient of the layer
kernel `𝒜 = layerKernel` at general `(G, ρ)`: its
constant part in closed form, and its dependent part
`κ₄^dep` as an explicit sum over primitive
distinct-column quadruples (upgraded to spatial
plaquettes at `5 ≤ N`). The sign of `κ₄^dep` is **not**
proved here: §Sign names the exact open component (the
plaquette-telescoping evaluation of `quadReMoment`).
Nothing in this module asserts positivity of `𝒜` at
any `β > 0`; `β2` and (H-PF) remain open.

**The named-space fence (K-K4G-2).** "Dependent part"
means the cumulant over partitions of the
DISTINCT-column support, exactly as in the κ₄ probe's
assembly correction: pair splits contribute the
constant `μ₂²`-type terms (they factor, by
`integral_colDens_pow_mul`, at `3 ≤ N`), plaquette
pair splits contribute `e₁²` constants. The N = 2
same-site-pair sector and the N = 4 wrap-line sector
are outside the fence of the closed form (`3 ≤ N` for
the assembly, `5 ≤ N` for the plaquette
identification), fenced out here exactly as the
N ≥ 3 theory fences them out elsewhere.
-/

import ThetLogos.PlaneCrossingBeta3
import ThetLogos.PolymerActivity

open MeasureTheory Finset

namespace ThetLogos

section Coeff4

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The fourth β-coefficient of `𝒜`: `∫ layerDensSum⁴ / 24`
(so `𝒜 = 1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ + O(β⁵)`). -/
noncomputable def betaCoeff4 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (layerDensSum ρ α u u') ^ 4 / 24
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **The expansion, real form, at order 4.** For every
real `β`, the stratum average of the layer exponential
is `1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ + R₅(β)` with `R₅`
the displayed tail series. FENCE: a Taylor coefficient
identity; no positivity of `𝒜` at any `β > 0` follows. -/
theorem layerKernel_real_expansion4 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
        - β ^ 3 * betaCoeff3 ρ μG u u'
        + β ^ 4 * betaCoeff4 ρ μG u u'
        + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
            / ((Nat.factorial (k + 5) : ℝ))
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hexp : ∀ α : LayerSite N → G,
      Real.exp (-(β * layerDensSum ρ α u u'))
        = ∑' n : ℕ, (-β * layerDensSum ρ α u u') ^ n
            / ((Nat.factorial n : ℝ)) := by
    intro α
    have h1 : Real.exp (-(β * layerDensSum ρ α u u'))
        = NormedSpace.exp (-(β * layerDensSum ρ α u u')) :=
      congrFun Real.exp_eq_exp_ℝ _
    rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
    apply tsum_congr
    intro n
    rw [neg_mul, smul_eq_mul, div_eq_inv_mul]
  have hSumm : Summable fun n => ∫ α,
        (-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_norm_term_int ρ μG hN hρcont β u u').of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have ht0 : (∫ α, (-β * layerDensSum ρ α u u') ^ 0
        / ((Nat.factorial 0 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)) = 1 := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 0 / ((Nat.factorial 0 : ℝ))
          = 1 :=
      fun α => by norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const, probReal_univ, one_smul]
  have ht1 : (∫ α, (-β * layerDensSum ρ α u u') ^ 1
        / ((Nat.factorial 1 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β * betaCoeff1 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 1 / ((Nat.factorial 1 : ℝ))
          = -β * layerDensSum ρ α u u' :=
      fun α => by
        simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht2 : (∫ α, (-β * layerDensSum ρ α u u') ^ 2
        / ((Nat.factorial 2 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 2 * betaCoeff2 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 2 / ((Nat.factorial 2 : ℝ))
          = β ^ 2 * ((layerDensSum ρ α u u') ^ 2 / 2) := by
      intro α
      have h2 : ((Nat.factorial 2 : ℝ)) = 2 := by
        norm_num [Nat.factorial]
      rw [h2]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht3 : (∫ α, (-β * layerDensSum ρ α u u') ^ 3
        / ((Nat.factorial 3 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β ^ 3 * betaCoeff3 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 3 / ((Nat.factorial 3 : ℝ))
          = -β ^ 3 * ((layerDensSum ρ α u u') ^ 3 / 6) := by
      intro α
      have h3 : ((Nat.factorial 3 : ℝ)) = 6 := by
        norm_num [Nat.factorial]
      rw [h3]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht4 : (∫ α, (-β * layerDensSum ρ α u u') ^ 4
        / ((Nat.factorial 4 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 4 * betaCoeff4 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 4 / ((Nat.factorial 4 : ℝ))
          = β ^ 4 * ((layerDensSum ρ α u u') ^ 4 / 24) := by
      intro α
      have h4 : ((Nat.factorial 4 : ℝ)) = 24 := by
        norm_num [Nat.factorial]
      rw [h4]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    ← (hasSum_integral_of_summable_integral_norm
      (fun n => integrable_term ρ μG hN hρcont β u u' n)
      (summable_norm_term_int ρ μG hN hρcont β u u')).tsum_eq,
    ← hSumm.sum_add_tsum_nat_add 5,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero,
    ht0, ht1, ht2, ht3, ht4]
  ring

/-- **The expansion of `𝒜` itself at order 4** (the
ℂ-valued layer kernel is the cast of the real
expansion). Same fence: no positivity conclusion. -/
theorem layerKernel_expansion4 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
          - β ^ 3 * betaCoeff3 ρ μG u u'
          + β ^ 4 * betaCoeff4 ρ μG u u'
          + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
              / ((Nat.factorial (k + 5) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
  have hreal : (∫ α, Real.exp (-(layerAction ρ β α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
    integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show Real.exp (-(layerAction ρ β α u u'))
        = Real.exp (-(β * layerDensSum ρ α u u'))
      rw [layerAction_eq])
  calc layerKernel μG ρ β u u'
      = ((∫ α, Real.exp (-(layerAction ρ β α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
        show (∫ α, (Real.exp (-(layerAction ρ β α u u')) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG)) = _
        exact integral_ofReal
    _ = ((1 - β * betaCoeff1 ρ μG u u'
          + β ^ 2 * betaCoeff2 ρ μG u u'
          - β ^ 3 * betaCoeff3 ρ μG u u'
          + β ^ 4 * betaCoeff4 ρ μG u u'
          + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
              / ((Nat.factorial (k + 5) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
        rw [hreal, layerKernel_real_expansion4 ρ μG hN hρcont β u u']

/-- **The tail bound at order 5:** `|R₅(β)| ≤
(2M|β|)⁵/120 · exp(2M|β|)`, from `(k+5)! ≥ 120·k!`
termwise. So the remainder after the β⁴ term is
genuinely `O(β⁵)` as `β → 0`, with an explicit
constant. (Still no positivity conclusion.) -/
theorem layerKernel_tail_bound4 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
        / ((Nat.factorial (k + 5) : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ (2 * colCount N * |β|) ^ 5 / 120
        * Real.exp (2 * colCount N * |β|) := by
  set X : ℝ := 2 * colCount N * |β| with hX
  have hc : (0 : ℝ) ≤ colCount N := Nat.cast_nonneg _
  have hXnn : 0 ≤ X :=
    mul_nonneg (mul_nonneg (by norm_num) hc) (abs_nonneg β)
  have hsumN : Summable fun k => ∫ α,
        ‖(-β * layerDensSum ρ α u u') ^ (k + 5)
          / ((Nat.factorial (k + 5) : ℝ))‖
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_nat_add_iff 5).mpr
      (summable_norm_term_int ρ μG hN hρcont β u u')
  have hsumN' : Summable fun k => ‖∫ α,
        (-β * layerDensSum ρ α u u') ^ (k + 5)
          / ((Nat.factorial (k + 5) : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
    hsumN.of_norm_bounded (fun k => by
      have h : ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
              / ((Nat.factorial (k + 5) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖
          ≤ ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 5)
              / ((Nat.factorial (k + 5) : ℝ))‖
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
        norm_integral_le_integral_norm _
      have h2 : ‖‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
              / ((Nat.factorial (k + 5) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖‖
          = ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
              / ((Nat.factorial (k + 5) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
        Real.norm_of_nonneg (norm_nonneg _)
      rw [h2]
      exact h)
  have hfact : ∀ k : ℕ, (Nat.factorial (k + 5) : ℝ)
      = ((k : ℝ) + 1) * (((k : ℝ) + 2)
        * (((k : ℝ) + 3) * (((k : ℝ) + 4)
          * (((k : ℝ) + 5) * (Nat.factorial k : ℝ))))) := by
    intro k
    have h : Nat.factorial (k + 5)
        = (k + 5) * ((k + 4) * ((k + 3) * ((k + 2)
          * ((k + 1) * Nat.factorial k)))) := by
      simp only [Nat.factorial_succ]
    calc (Nat.factorial (k + 5) : ℝ)
        = (((k + 5) * ((k + 4) * ((k + 3) * ((k + 2)
            * ((k + 1) * Nat.factorial k)))) : ℕ) : ℝ) := by
          rw [h]
      _ = ((k : ℝ) + 1) * (((k : ℝ) + 2)
            * (((k : ℝ) + 3) * (((k : ℝ) + 4)
              * (((k : ℝ) + 5) * (Nat.factorial k : ℝ))))) := by
          push_cast
          ring
  have hterm : ∀ k : ℕ, X ^ (k + 5) / (Nat.factorial (k + 5) : ℝ)
      ≤ (X ^ 5 / 120) * (X ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h120 : (120 : ℝ) ≤ ((k : ℝ) + 1) * (((k : ℝ) + 2)
        * (((k : ℝ) + 3) * (((k : ℝ) + 4) * ((k : ℝ) + 5)))) := by
      have e : ((k : ℝ) + 1) * (((k : ℝ) + 2)
            * (((k : ℝ) + 3) * (((k : ℝ) + 4) * ((k : ℝ) + 5))))
          = (k : ℝ) ^ 5 + 15 * (k : ℝ) ^ 4 + 85 * (k : ℝ) ^ 3
            + 225 * (k : ℝ) ^ 2 + 274 * (k : ℝ) + 120 := by ring
      rw [e]
      have h2 := pow_nonneg hk 2
      have h3 := pow_nonneg hk 3
      have h4 := pow_nonneg hk 4
      have h5 := pow_nonneg hk 5
      linarith
    have hpos : (0 : ℝ) < (Nat.factorial (k + 5) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hX5 : (0 : ℝ) ≤ X ^ 5 * X ^ k :=
      mul_nonneg (pow_nonneg hXnn 5) (pow_nonneg hXnn k)
    rw [div_le_iff₀ hpos]
    have hRHS : ((X ^ 5 / 120) * (X ^ k / (Nat.factorial k : ℝ)))
          * (Nat.factorial (k + 5) : ℝ)
        = (X ^ 5 / 120) * X ^ k
          * (((k : ℝ) + 1) * (((k : ℝ) + 2)
            * (((k : ℝ) + 3) * (((k : ℝ) + 4)
              * ((k : ℝ) + 5))))) := by
      rw [hfact k]
      field_simp
    rw [hRHS]
    calc X ^ (k + 5) = X ^ 5 * X ^ k := by ring
      _ ≤ (X ^ 5 / 120) * X ^ k
            * (((k : ℝ) + 1) * (((k : ℝ) + 2)
              * (((k : ℝ) + 3) * (((k : ℝ) + 4)
                * ((k : ℝ) + 5))))) := by
          have hnn : (0 : ℝ) ≤ X ^ 5 * X ^ k := hX5
          have hge : (1 : ℝ) ≤ (((k : ℝ) + 1) * (((k : ℝ) + 2)
              * (((k : ℝ) + 3) * (((k : ℝ) + 4)
                * ((k : ℝ) + 5))))) / 120 := by
            rw [le_div_iff₀ (by norm_num : (0:ℝ) < 120)]
            linarith [h120]
          calc X ^ 5 * X ^ k
              = (X ^ 5 * X ^ k) * 1 := by ring
            _ ≤ (X ^ 5 * X ^ k)
                  * ((((k : ℝ) + 1) * (((k : ℝ) + 2)
                    * (((k : ℝ) + 3) * (((k : ℝ) + 4)
                      * ((k : ℝ) + 5))))) / 120) :=
                mul_le_mul_of_nonneg_left hge hnn
            _ = (X ^ 5 / 120) * X ^ k
                  * (((k : ℝ) + 1) * (((k : ℝ) + 2)
                    * (((k : ℝ) + 3) * (((k : ℝ) + 4)
                      * ((k : ℝ) + 5))))) := by ring
  have hXeq : |β| * (2 * colCount N) = X := by rw [hX]; ring
  have hbound : ∀ k : ℕ,
      ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
          / ((Nat.factorial (k + 5) : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG)‖
        ≤ (X ^ 5 / 120) * (X ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    calc ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
            / ((Nat.factorial (k + 5) : ℝ))
            ∂(Measure.pi fun _ : LayerSite N => μG)‖
        ≤ ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 5)
            / ((Nat.factorial (k + 5) : ℝ))‖
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
          norm_integral_le_integral_norm _
      _ ≤ X ^ (k + 5) / (Nat.factorial (k + 5) : ℝ) := by
          calc ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 5)
                  / ((Nat.factorial (k + 5) : ℝ))‖
                  ∂(Measure.pi fun _ : LayerSite N => μG)
              ≤ ∫ _α : LayerSite N → G,
                  X ^ (k + 5) / ((Nat.factorial (k + 5) : ℝ))
                  ∂(Measure.pi fun _ : LayerSite N => μG) :=
                integral_mono_ae
                  (integrable_term ρ μG hN hρcont β u u' (k + 5)).norm
                  (integrable_const _)
                  (Filter.Eventually.of_forall fun α => by
                    have hb := norm_term_le ρ hN β u u' (k + 5) α
                    rwa [hXeq] at hb)
            _ = X ^ (k + 5) / ((Nat.factorial (k + 5) : ℝ)) := by
                rw [integral_const, probReal_univ, one_smul]
      _ ≤ (X ^ 5 / 120) * (X ^ k / (Nat.factorial k : ℝ)) :=
          hterm k
  calc ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
          / ((Nat.factorial (k + 5) : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ ∑' (k : ℕ), ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 5)
          / ((Nat.factorial (k + 5) : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
        norm_tsum_le_tsum_norm hsumN'
    _ ≤ ∑' (k : ℕ), (X ^ 5 / 120) * (X ^ k / (Nat.factorial k : ℝ)) :=
        hsumN'.tsum_le_tsum hbound
          ((Real.summable_pow_div_factorial X).mul_left _)
    _ = (X ^ 5 / 120) * Real.exp X := by
        rw [tsum_mul_left]
        congr 1
        have h1 : Real.exp X = NormedSpace.exp X :=
          congrFun Real.exp_eq_exp_ℝ _
        rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
        apply tsum_congr
        intro n
        rw [smul_eq_mul, div_eq_inv_mul]
    _ = (2 * colCount N * |β|) ^ 5 / 120
          * Real.exp (2 * colCount N * |β|) := by
        rw [hX]

end Coeff4

section ClosedForm4

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The closed value of the `j`-th single-column density
moment: `∫ dens_Pʲ = densMomentValue j` for every column
and every `(u, u')` (`colDensMoment_closed`). Only the
label `j` and the Haar moments `μₐ = ∫ (Re χ)ᵃ` enter. -/
noncomputable def densMomentValue (j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℝ))
    * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a

theorem densMomentValue_eq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) (j : ℕ) :
    colDensMoment ρ μG u u' P j = densMomentValue ρ μG j :=
  colDensMoment_closed ρ μG hN hρcont u u' P j

/-- The constant part of the fourth coefficient, in the
assembly's pattern values: with `M = colCount N`,
`B = 1 − e₁/d`, `Aⱼ = densMomentValue j`:
`M·A₄ + 4M(M−1)·A₃B + 3M(M−1)·A₂²
+ 6M(M−1)(M−2)·A₂B² + M(M−1)(M−2)(M−3)·B⁴`.
These are the `(4)`, `(3,1)`, `(2,2)`, `(2,1,1)`,
`(1,1,1,1)` pattern contributions with the dependent
`(1,1,1,1)` excess removed. -/
noncomputable def kappa4Const : ℝ :=
  colCount N * densMomentValue ρ μG 4
    + 4 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ))
    + 3 * colCount N * (colCount N - 1)
      * (densMomentValue ρ μG 2) ^ 2
    + 6 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
    + colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (1 - e1 ρ μG / (d : ℝ)) ^ 4

/-- **κ₄^dep**, the dependent part of the β⁴
coefficient: what remains of `betaCoeff4` after the
closed constant part is removed. -/
noncomputable def kappa4dep (u u' : LayerLink N → G) : ℝ :=
  betaCoeff4 ρ μG u u' - kappa4Const (N := N) ρ μG / 24

/-- The character moment of a finite set of columns:
`∫ ∏_{P ∈ C} Re χ(word_P)`. For a 4-element set `C` of
distinct columns this is the raw (un-cumulanted)
plaquette-type moment; its dependent excess over
`e₁⁴` is the summand of the closed form. -/
noncomputable def quadReMoment (C : Finset (LayerColumn N))
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, ∏ P ∈ C, colRe ρ u u' P α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- A 4-element set of columns is **primitive** if no
column in it has a private site within the set: every
site of every column is shared with another column of
the set. Primitive quadruples are exactly the
supports whose character moment does not factor. -/
def IsPrimitiveQuad (C : Finset (LayerColumn N)) : Prop :=
  C.card = 4 ∧ ∀ P ∈ C, ∀ s ∈ colSites P,
    ∃ Q ∈ C, Q ≠ P ∧ s ∈ colSites Q

/-- The finite set of primitive 4-column supports. -/
noncomputable def primitiveQuads : Finset (Finset (LayerColumn N)) :=
  Finset.univ.filter (fun C => C.card = 4
    ∧ ∀ P ∈ C, ∀ s ∈ colSites P,
      ∃ Q ∈ C, Q ≠ P ∧ s ∈ colSites Q)

/-- **The engine: split off one column at a private
site, against an arbitrary finite product of other
columns.** If `s ∈ colSites R` and no column of `F`
reads `s`, then for every exponent function `a` and
every `k`, `∫ (∏_{P ∈ F} r_P^{a P}) · r_Rᵏ
= μₖ · ∫ ∏_{P ∈ F} r_P^{a P}`. The product over `F`
is `α s`-blind, so the inner integral at `s` is the
one-column strip `integral_split_inner_pow`. This is
the order-4 form of the private-site mechanism behind
`integral_colRe_pow_mul_of_site`. -/
theorem integral_colRe_pow_split_finset (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (F : Finset (LayerColumn N))
    (a : LayerColumn N → ℕ) (R : LayerColumn N) (hR : R ∉ F)
    (s : LayerSite N) (hsR : s ∈ colSites R)
    (hsF : ∀ P ∈ F, s ∉ colSites P) (k : ℕ) :
    ∫ α : LayerSite N → G,
        (∏ P ∈ F, (colRe ρ u u' P α) ^ (a P))
          * (colRe ρ u u' R α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = realMoment ρ μG k *
        ∫ α : LayerSite N → G, ∏ P ∈ F, (colRe ρ u u' P α) ^ (a P)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
  classical
  set CF : ℝ := ∏ P ∈ F, (d : ℝ) ^ (a P) with hCF
  have hboundF : ∀ α : LayerSite N → G,
      ‖∏ P ∈ F, (colRe ρ u u' P α) ^ (a P)‖ ≤ CF := by
    intro α
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine le_trans (Finset.prod_le_prod₀
      (f := fun P => |(colRe ρ u u' P α) ^ (a P)|)
      (g := fun P => (d : ℝ) ^ (a P))
      (fun P _ => abs_nonneg _)
      (fun P _ => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_re_charFn_le ρ _) _)) ?_
    exact le_of_eq hCF.symm
  have hCFnn : (0 : ℝ) ≤ CF := by
    rw [hCF]
    exact Finset.prod_nonneg fun P _ =>
      pow_nonneg (Nat.cast_nonneg _) _
  have hInt : Integrable
      (fun z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
        (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s z)) ^ (a P))
          * (colRe ρ u u' R (splitRecomb s z)) ^ k)
      ((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
        (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    refine Integrable.of_bound ?_ (CF * (d : ℝ) ^ k)
      (Filter.Eventually.of_forall fun z => ?_)
    · exact ((Finset.measurable_prod F fun P _ =>
        ((measurable_colRe ρ hρcont u u' P).comp
          (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable
          ).pow_const _).mul
        (((measurable_colRe ρ hρcont u u' R).comp
          (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable
          ).pow_const _)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hboundF _) ?_
        (abs_nonneg _) hCFnn
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) _
  have htrans : ∫ α : LayerSite N → G,
        (∏ P ∈ F, (colRe ρ u u' P α) ^ (a P))
          * (colRe ρ u u' R α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G),
          (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s z)) ^ (a P))
            * (colRe ρ u u' R (splitRecomb s z)) ^ k
          ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
            (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    have h := (measurePreserving_splitEquiv μG
      ({s} : Finset (LayerSite N))).integral_comp
      (splitEquiv ({s} : Finset (LayerSite N))).measurableEmbedding
      (fun z => (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s z)) ^ (a P))
        * (colRe ρ u u' R (splitRecomb s z)) ^ k)
    have hL : ∫ U : LayerSite N → G,
          (fun z => (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s z)) ^ (a P))
            * (colRe ρ u u' R (splitRecomb s z)) ^ k)
            (splitEquiv ({s} : Finset (LayerSite N)) U)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∫ U : LayerSite N → G,
            (∏ P ∈ F, (colRe ρ u u' P U) ^ (a P))
              * (colRe ρ u u' R U) ^ k
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with U
      rw [splitRecomb_apply_split]
    rw [hL] at h
    exact h
  -- the F-product is blind to the split coordinate
  have hblind : ∀ (v : ↥({s} : Finset (LayerSite N)) → G)
      (w : ↥({s}ᶜ : Finset (LayerSite N)) → G) (P : LayerColumn N),
      P ∈ F → colRe ρ u u' P (splitRecomb s (v, w))
        = colRe ρ u u' P (splitRecomb s (fun _ => 1, w)) := by
    intro v w P hP
    have hsP : s ∉ colSites P := hsF P hP
    have hbP : P.1 ≠ s := by
      intro h
      apply hsP
      have hmem : P.1 ∈ colSites P := mem_colSites.mpr (Or.inl rfl)
      rw [h] at hmem
      exact hmem
    have hfP : layerShift P.2.1 P.2.2 P.1 ≠ s := by
      intro h
      apply hsP
      have hmem : layerShift P.2.1 P.2.2 P.1 ∈ colSites P :=
        mem_colSites.mpr (Or.inr rfl)
      rw [h] at hmem
      exact hmem
    have h1 : splitRecomb s (v, w) P.1
        = splitRecomb s (fun _ => 1, w) P.1 :=
      (splitRecomb_snd s (v, w) ⟨P.1,
        Finset.mem_compl.mpr (fun hmem =>
          hbP (Finset.mem_singleton.mp hmem))⟩).trans
        (splitRecomb_snd s (fun _ => 1, w) ⟨P.1,
          Finset.mem_compl.mpr (fun hmem =>
            hbP (Finset.mem_singleton.mp hmem))⟩).symm
    have h2 : splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
        = splitRecomb s (fun _ => 1, w)
            (layerShift P.2.1 P.2.2 P.1) :=
      (splitRecomb_snd s (v, w) ⟨layerShift P.2.1 P.2.2 P.1,
        Finset.mem_compl.mpr (fun hmem =>
          hfP (Finset.mem_singleton.mp hmem))⟩).trans
        (splitRecomb_snd s (fun _ => 1, w) ⟨layerShift P.2.1 P.2.2 P.1,
          Finset.mem_compl.mpr (fun hmem =>
            hfP (Finset.mem_singleton.mp hmem))⟩).symm
    exact congrArg (fun g => (charFn ρ g).re)
      (colWord_eq_of_agree u u' P.1 P.2.1 P.2.2 h1 h2)
  calc ∫ α : LayerSite N → G,
        (∏ P ∈ F, (colRe ρ u u' P α) ^ (a P))
          * (colRe ρ u u' R α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G),
            (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s z)) ^ (a P))
              * (colRe ρ u u' R (splitRecomb s z)) ^ k
            ∂((Measure.pi
              fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
              (Measure.pi
                fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) :=
        htrans
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            ∫ v : ↥({s} : Finset (LayerSite N)) → G,
              (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s (v, w))) ^ (a P))
                * (colRe ρ u u' R (splitRecomb s (v, w))) ^ k
              ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) :=
        integral_prod_symm _ hInt
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            (∏ P ∈ F, (colRe ρ u u' P
                (splitRecomb s (fun _ => 1, w))) ^ (a P))
              * realMoment ρ μG k
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) := by
        apply integral_congr_ae
        filter_upwards with w
        calc ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                (∏ P ∈ F, (colRe ρ u u' P (splitRecomb s (v, w))) ^ (a P))
                  * (colRe ρ u u' R (splitRecomb s (v, w))) ^ k
                ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            = ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                  (∏ P ∈ F, (colRe ρ u u' P
                      (splitRecomb s (fun _ => 1, w))) ^ (a P))
                    * (colRe ρ u u' R (splitRecomb s (v, w))) ^ k
                  ∂(Measure.pi
                    fun _ : ↥({s} : Finset (LayerSite N)) => μG) :=
              integral_congr_ae (Filter.Eventually.of_forall fun v =>
                congrArg (· * (colRe ρ u u' R (splitRecomb s (v, w))) ^ k)
                  (Finset.prod_congr rfl fun P hP =>
                    congrArg (· ^ (a P)) (hblind v w P hP)))
          _ = (∏ P ∈ F, (colRe ρ u u' P
                    (splitRecomb s (fun _ => 1, w))) ^ (a P))
                  * ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                      (colRe ρ u u' R (splitRecomb s (v, w))) ^ k
                      ∂(Measure.pi
                        fun _ : ↥({s} : Finset (LayerSite N)) => μG) :=
              integral_const_mul _ _
          _ = (∏ P ∈ F, (colRe ρ u u' P
                    (splitRecomb s (fun _ => 1, w))) ^ (a P))
                  * realMoment ρ μG k := by
              rw [integral_split_inner_pow ρ μG hN hρcont u u' R s hsR w k]
    _ = realMoment ρ μG k
          * ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
              ∏ P ∈ F, (colRe ρ u u' P
                  (splitRecomb s (fun _ => 1, w))) ^ (a P)
              ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall fun w =>
          mul_comm _ _)]
        exact integral_const_mul _ _
    _ = realMoment ρ μG k *
          ∫ α : LayerSite N → G, ∏ P ∈ F, (colRe ρ u u' P α) ^ (a P)
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
        congr 1
        rw [← integral_pi_restrict_real μG ({s}ᶜ : Finset (LayerSite N))
          (fun w => ∏ P ∈ F, (colRe ρ u u' P
            (splitRecomb s (fun _ => 1, w))) ^ (a P))]
        apply integral_congr_ae
        filter_upwards with U
        refine Finset.prod_congr rfl fun P hP => congrArg (· ^ (a P)) ?_
        have hsP : s ∉ colSites P := hsF P hP
        have hbP : P.1 ≠ s := by
          intro h
          apply hsP
          have hmem : P.1 ∈ colSites P := mem_colSites.mpr (Or.inl rfl)
          rw [h] at hmem
          exact hmem
        have hfP : layerShift P.2.1 P.2.2 P.1 ≠ s := by
          intro h
          apply hsP
          have hmem : layerShift P.2.1 P.2.2 P.1 ∈ colSites P :=
            mem_colSites.mpr (Or.inr rfl)
          rw [h] at hmem
          exact hmem
        have h1 : splitRecomb s
              (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                U ℓ.1) P.1 = U P.1 :=
          splitRecomb_snd s _ ⟨P.1,
            Finset.mem_compl.mpr (fun hmem =>
              hbP (Finset.mem_singleton.mp hmem))⟩
        have h2 : splitRecomb s
              (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                U ℓ.1) (layerShift P.2.1 P.2.2 P.1)
              = U (layerShift P.2.1 P.2.2 P.1) :=
          splitRecomb_snd s _ ⟨layerShift P.2.1 P.2.2 P.1,
            Finset.mem_compl.mpr (fun hmem =>
              hfP (Finset.mem_singleton.mp hmem))⟩
        exact congrArg (fun g => (charFn ρ g).re)
          (colWord_eq_of_agree u u' P.1 P.2.1 P.2.2 h1 h2)

/-- Products of column-character powers over a finite
support are integrable (entrywise bound `|r_P| ≤ d`). -/
theorem integrable_colRe_prod_pow
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (𝒮 : Finset (LayerColumn N))
    (a : LayerColumn N → ℕ) :
    Integrable (fun α : LayerSite N → G =>
        ∏ P ∈ 𝒮, (colRe ρ u u' P α) ^ (a P))
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine Integrable.of_bound
    (Finset.measurable_prod 𝒮 fun P _ =>
      (measurable_colRe ρ hρcont u u' P).pow_const _
      ).aestronglyMeasurable
    (∏ P ∈ 𝒮, (d : ℝ) ^ (a P))
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_prod₀
    (f := fun P => |(colRe ρ u u' P α) ^ (a P)|)
    (g := fun P => (d : ℝ) ^ (a P))
    (fun P _ => abs_nonneg _)
    (fun P _ => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_re_charFn_le ρ _) _)

/-- **The `(2,1,1)` character moment at three distinct
columns:** `∫ r_P² r_Q r_R = μ₂ e₁²`. The triple
alternative (`exists_private_site_triple`) supplies a
private site for one of the three columns; the engine
splits it off — with exponent `2` if the doubled
column is the private one (`μ₂` strip), with
exponent `1` otherwise (`e₁` strip) — and the
remaining two-column moment factors by
`integral_colRe_pow_mul` / `integral_cross`. -/
theorem integral_colRe_sq_mul_mul (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ 2
          * colRe ρ u u' Q α * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 := by
  classical
  -- the two-element support products, in explicit form
  have hprodPQ : ∀ α : LayerSite N → G,
      (∏ Z ∈ ({P, Q} : Finset (LayerColumn N)),
        (colRe ρ u u' Z α) ^ (if Z = P then 2 else 1))
        = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 1 := by
    intro α
    rw [Finset.prod_pair hPQ, if_pos rfl,
      if_neg (fun h : Q = P => hPQ h.symm)]
  have hprodPR : ∀ α : LayerSite N → G,
      (∏ Z ∈ ({P, R} : Finset (LayerColumn N)),
        (colRe ρ u u' Z α) ^ (if Z = P then 2 else 1))
        = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' R α) ^ 1 := by
    intro α
    rw [Finset.prod_pair hPR, if_pos rfl,
      if_neg (fun h : R = P => hPR h.symm)]
  have hprodQR : ∀ α : LayerSite N → G,
      (∏ Z ∈ ({Q, R} : Finset (LayerColumn N)),
        (colRe ρ u u' Z α) ^ (1 : ℕ))
        = (colRe ρ u u' Q α) ^ 1 * (colRe ρ u u' R α) ^ 1 := by
    intro α
    rw [Finset.prod_pair hQR]
  obtain (⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩) :=
    exists_private_site_triple hN hN3 hPQ hPR hQR
  · -- private site for P: split P off with exponent 2
    have heng := integral_colRe_pow_split_finset ρ μG hN hN3
      hρcont u u' ({Q, R} : Finset (LayerColumn N)) (fun _ => 1) P
      (by simp [hPQ, hPR]) s hs.1 (fun X hX => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hs.2.1
        · exact hs.2.2) 2
    simp only [hprodQR] at heng
    have hcongr : (∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ 2
          * colRe ρ u u' Q α * colRe ρ u u' R α
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
            ((colRe ρ u u' Q α) ^ 1 * (colRe ρ u u' R α) ^ 1)
              * (colRe ρ u u' P α) ^ 2
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall fun α => by
        simp only [pow_one]; ring)
    rw [hcongr, heng]
    congr 1
    rw [integral_congr_ae (Filter.Eventually.of_forall
      (fun α : LayerSite N → G => by
        show (colRe ρ u u' Q α) ^ 1 * (colRe ρ u u' R α) ^ 1
          = colRe ρ u u' Q α * colRe ρ u u' R α
        simp only [pow_one]))]
    exact integral_cross ρ μG hN hN3 hρcont u u' hQR
  · -- private site for Q: split Q off with exponent 1
    have heng := integral_colRe_pow_split_finset ρ μG hN hN3
      hρcont u u' ({P, R} : Finset (LayerColumn N))
      (fun Z => if Z = P then 2 else 1) Q
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hPQ h.symm, hQR⟩) s hs.1 (fun X hX => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hs.2.1
        · exact hs.2.2) 1
    simp only [hprodPR] at heng
    have hcongr : (∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ 2
          * colRe ρ u u' Q α * colRe ρ u u' R α
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
            ((colRe ρ u u' P α) ^ 2 * (colRe ρ u u' R α) ^ 1)
              * (colRe ρ u u' Q α) ^ 1
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall fun α => by
        simp only [pow_one]; ring)
    rw [hcongr, heng, realMoment_one,
      integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPR 2 1,
      realMoment_one]
    ring
  · -- private site for R: split R off with exponent 1
    have heng := integral_colRe_pow_split_finset ρ μG hN hN3
      hρcont u u' ({P, Q} : Finset (LayerColumn N))
      (fun Z => if Z = P then 2 else 1) R
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hPR h.symm, fun h => hQR h.symm⟩) s hs.1 (fun X hX => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hs.2.1
        · exact hs.2.2) 1
    simp only [hprodPQ] at heng
    have hcongr : (∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ 2
          * colRe ρ u u' Q α * colRe ρ u u' R α
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α : LayerSite N → G,
            ((colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 1)
              * (colRe ρ u u' R α) ^ 1
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall fun α => by
        simp only [pow_one])
    rw [hcongr, heng, realMoment_one,
      integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPQ 2 1,
      realMoment_one]
    ring

/-- **The quadruple character moment with a private
site at the last column:** `∫ r_P r_Q r_R r_S = e₁⁴`.
The engine splits `S` off (exponent `1` strip `e₁`),
leaving the distinct-triple moment `e₁³`. -/
theorem integral_colRe_quadruple_of_site (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R S : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hPS : P ≠ S) (hQR : Q ≠ R)
    (hQS : Q ≠ S) (hRS : R ≠ S) {s : LayerSite N}
    (hsS : s ∈ colSites S) (hsP : s ∉ colSites P)
    (hsQ : s ∉ colSites Q) (hsR : s ∉ colSites R) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α * colRe ρ u u' S α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (e1 ρ μG) ^ 4 := by
  classical
  have hprod : ∀ α : LayerSite N → G,
      (∏ Z ∈ ({P, Q, R} : Finset (LayerColumn N)),
        (colRe ρ u u' Z α) ^ (1 : ℕ))
        = colRe ρ u u' P α * (colRe ρ u u' Q α
            * colRe ρ u u' R α) := by
    intro α
    rw [Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
    simp only [pow_one]
  have heng := integral_colRe_pow_split_finset ρ μG hN hN3
    hρcont u u' ({P, Q, R} : Finset (LayerColumn N)) (fun _ => 1) S
    (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hPS h.symm, fun h => hQS h.symm, fun h => hRS h.symm⟩) s hsS (fun X hX => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl
      · exact hsP
      · exact hsQ
      · exact hsR) 1
  simp only [hprod] at heng
  have htr : ∫ α : LayerSite N → G, colRe ρ u u' P α
        * (colRe ρ u u' Q α * colRe ρ u u' R α)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (e1 ρ μG) ^ 3 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colRe ρ u u' P α * (colRe ρ u u' Q α
            * colRe ρ u u' R α)
        = colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α
      ring), integral_colRe_triple ρ μG hN hN3 hρcont u u' hPQ
      hPR hQR, realMoment_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
    show colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
        * colRe ρ u u' S α
      = (colRe ρ u u' P α * (colRe ρ u u' Q α
          * colRe ρ u u' R α)) * (colRe ρ u u' S α) ^ 1
    simp only [pow_one]; ring), heng, realMoment_one, htr]
  ring

/-- **The quadruple character moment factors whenever
some column has a private site within the four:**
`∫ r_P r_Q r_R r_S = e₁⁴`. (The complementary case —
no private site — is the primitive quadruple, whose
moment is the dependent excess of the closed form.) -/
theorem integral_colRe_quadruple_factor (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R S : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hPS : P ≠ S) (hQR : Q ≠ R)
    (hQS : Q ≠ S) (hRS : R ≠ S)
    (hpriv : (∃ s, s ∈ colSites P ∧ s ∉ colSites Q
        ∧ s ∉ colSites R ∧ s ∉ colSites S)
      ∨ (∃ s, s ∈ colSites Q ∧ s ∉ colSites P
        ∧ s ∉ colSites R ∧ s ∉ colSites S)
      ∨ (∃ s, s ∈ colSites R ∧ s ∉ colSites P
        ∧ s ∉ colSites Q ∧ s ∉ colSites S)
      ∨ (∃ s, s ∈ colSites S ∧ s ∉ colSites P
        ∧ s ∉ colSites Q ∧ s ∉ colSites R)) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α * colRe ρ u u' S α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (e1 ρ μG) ^ 4 := by
  rcases hpriv with (⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩)
  · rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
          * colRe ρ u u' S α
        = colRe ρ u u' Q α * colRe ρ u u' R α * colRe ρ u u' S α
          * colRe ρ u u' P α
      ring)]
    exact integral_colRe_quadruple_of_site ρ μG hN hN3 hρcont
      u u' hQR hQS (fun h => hPQ h.symm) hRS (fun h => hPR h.symm) (fun h => hPS h.symm)
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  · rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
          * colRe ρ u u' S α
        = colRe ρ u u' P α * colRe ρ u u' R α * colRe ρ u u' S α
          * colRe ρ u u' Q α
      ring)]
    exact integral_colRe_quadruple_of_site ρ μG hN hN3 hρcont
      u u' hPR hPS hPQ hRS (fun h => hQR h.symm) (fun h => hQS h.symm)
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  · rw [integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α
          * colRe ρ u u' S α
        = colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' S α
          * colRe ρ u u' R α
      ring)]
    exact integral_colRe_quadruple_of_site ρ μG hN hN3 hρcont
      u u' hPQ hPS hPR hQS hQR (fun h => hRS h.symm)
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  · exact integral_colRe_quadruple_of_site ρ μG hN hN3 hρcont
      u u' hPQ hPR hPS hQR hQS hRS hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/-- **Character moments of supports of size at most
three factor completely:** `∫ ∏_{P ∈ T} r_P
= e₁^{|T|}`. Assembled from `integral_colRe`,
`integral_cross`, `integral_colRe_triple` by the
cardinality of the support. -/
theorem integral_colRe_prod_of_card_le_three (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (T : Finset (LayerColumn N))
    (hT : T.card ≤ 3) :
    ∫ α : LayerSite N → G, ∏ P ∈ T, colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (e1 ρ μG) ^ T.card := by
  classical
  interval_cases hcard : T.card
  · have hT0 : T = ∅ := Finset.card_eq_zero.mp hcard
    simp only [hT0, Finset.prod_empty]
    rw [integral_const, probReal_univ, one_smul, pow_zero]
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
    simp only [hP, Finset.prod_singleton]
    rw [integral_colRe ρ μG hN hρcont u u' P, pow_one]
  · obtain ⟨P, Q, hPQ, hT2⟩ := Finset.card_eq_two.mp hcard
    simp only [hT2, Finset.prod_pair hPQ]
    rw [integral_cross ρ μG hN hN3 hρcont u u' hPQ]
  · obtain ⟨P, Q, R, hPQ, hPR, hQR, hT3⟩ :=
      Finset.card_eq_three.mp hcard
    have hprod : ∀ α : LayerSite N → G,
        ∏ Z ∈ ({P, Q, R} : Finset (LayerColumn N)),
          colRe ρ u u' Z α
          = colRe ρ u u' P α * (colRe ρ u u' Q α
              * colRe ρ u u' R α) := by
      intro α
      rw [Finset.prod_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
    rw [hT3, integral_congr_ae (Filter.Eventually.of_forall
      fun α => (hprod α).trans (by ring :
        colRe ρ u u' P α * (colRe ρ u u' Q α * colRe ρ u u' R α)
          = colRe ρ u u' P α * colRe ρ u u' Q α
            * colRe ρ u u' R α)),
      integral_colRe_triple ρ μG hN hN3 hρcont u u' hPQ hPR hQR,
      realMoment_one]

/-- **The density quadruple at a 4-element support:**
`∫ ∏_{P ∈ C} dens_P = B⁴ + d⁻⁴·(quadReMoment C − e₁⁴)`,
with `B = 1 − e₁/d`. Pointwise binomial expansion of
`∏ (1 − r_P/d)` over the powerset of `C`; every proper
subset moment factors (`e₁^{|T|}`, by the card ≤ 3
lemma), and the top subset is `quadReMoment C` by
definition. This identity holds for **every** distinct
quadruple: the excess over `B⁴` is present exactly
when the quadruple moment refuses to factor. -/
theorem integral_colDens_prod_quadruple (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (C : Finset (LayerColumn N))
    (hC : C.card = 4) :
    ∫ α : LayerSite N → G, ∏ P ∈ C, colDensC ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - e1 ρ μG / (d : ℝ)) ^ 4
        + ((d : ℝ)⁻¹) ^ 4 * (quadReMoment ρ μG C u u'
          - (e1 ρ μG) ^ 4) := by
  classical
  -- the pointwise powerset expansion
  have hpt : ∀ α : LayerSite N → G,
      ∏ P ∈ C, colDensC ρ u u' P α
        = ∑ T ∈ C.powerset, (-(d : ℝ)⁻¹) ^ T.card
            * ∏ P ∈ T, colRe ρ u u' P α := by
    intro α
    have h1 : ∏ P ∈ C, colDensC ρ u u' P α
        = ∏ P ∈ C, ((-(d : ℝ)⁻¹) * colRe ρ u u' P α + 1) := by
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [colDensC_eq]
      rw [div_eq_inv_mul]
      ring
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
      Finset.prod_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ (fun T _ =>
      Integrable.const_mul
        ((integrable_colRe_prod_pow ρ μG hρcont u u' T
          (fun _ => 1)).congr (Filter.Eventually.of_forall
            fun α => Finset.prod_congr rfl
              fun P _ => pow_one (colRe ρ u u' P α))) _)]
  -- evaluate each subset integral
  have hval : ∀ T ∈ C.powerset,
      ∫ α : LayerSite N → G, (-(d : ℝ)⁻¹) ^ T.card
          * ∏ P ∈ T, colRe ρ u u' P α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (-(d : ℝ)⁻¹) ^ T.card * (e1 ρ μG) ^ T.card
          + (if T = C then (-(d : ℝ)⁻¹) ^ 4
              * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
             else 0) := by
    intro T hT
    rw [integral_const_mul]
    have hsub : T ⊆ C := Finset.mem_powerset.mp hT
    by_cases hTC : T = C
    · subst hTC
      rw [if_pos rfl]
      have : ∫ α : LayerSite N → G, ∏ P ∈ T, colRe ρ u u' P α
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = quadReMoment ρ μG T u u' := rfl
      rw [this, hC]
      ring
    · rw [if_neg hTC]
      have hcard : T.card ≤ 3 := by
        rcases Nat.lt_or_ge T.card 4 with hlt | hge
        · omega
        · exfalso
          exact hTC (Finset.eq_of_subset_of_card_le hsub
            (by rw [hC]; exact hge))
      rw [integral_colRe_prod_of_card_le_three ρ μG hN hN3
        hρcont u u' T hcard]
      ring
  rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib]
  congr 1
  · -- the factorized part assembles to B⁴
    have hbase : ∀ T ∈ C.powerset,
        (-(d : ℝ)⁻¹) ^ T.card * (e1 ρ μG) ^ T.card
          = ((-(d : ℝ)⁻¹) * e1 ρ μG) ^ T.card := fun T _ =>
      (mul_pow _ _ _).symm
    rw [Finset.sum_congr rfl hbase]
    calc ∑ T ∈ C.powerset, ((-(d : ℝ)⁻¹) * e1 ρ μG) ^ T.card
        = ∑ T ∈ C.powerset,
            (∏ P ∈ T, ((-(d : ℝ)⁻¹) * e1 ρ μG))
              * ∏ P ∈ C \ T, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_const, Finset.prod_const_one, mul_one]
      _ = ∏ P ∈ C, ((-(d : ℝ)⁻¹) * e1 ρ μG + 1) :=
          (Finset.prod_add _ _ _).symm
      _ = (1 - e1 ρ μG / (d : ℝ)) ^ 4 := by
          rw [Finset.prod_const, hC]
          congr 1
          rw [div_eq_inv_mul]
          ring
  · -- the excess is carried by the top subset alone
    rw [Finset.sum_ite_eq' C.powerset C
      (fun T => (-(d : ℝ)⁻¹) ^ 4
        * (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4))]
    simp only [Finset.mem_powerset, Finset.Subset.refl, if_true]
    have hneg : (-(d : ℝ)⁻¹) ^ 4 = ((d : ℝ)⁻¹) ^ 4 := by ring
    rw [hneg]

/-- **The density pattern (2,1,1):**
`∫ dens_P² · dens_Q · dens_R = A₂ · B²` for distinct
`P, Q, R`. Proved by the pointwise expansion of
`(1 − r_P/d)²(1 − r_Q/d)(1 − r_R/d)` grouped by
integral value (singles `e₁`, crosses `e₁²`, square
`μ₂`, triple `e₁³`, square-single `μ₂e₁`, and the
(2,1,1) character moment `μ₂e₁²` of the previous
lemma). -/
theorem integral_colDens_sq_mul_mul (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q R : LayerColumn N}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ∫ α : LayerSite N → G, colDensC ρ u u' P α ^ 2
          * colDensC ρ u u' Q α * colDensC ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2 := by
  classical
  set x : ℝ := (d : ℝ)⁻¹ with hx
  -- monomial integrability, pointwise form
  have hIP : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α) (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_colRe ρ μG hρcont u u' P
  have hIQ : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' Q α) (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_colRe ρ μG hρcont u u' Q
  have hIR : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' R α) (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_colRe ρ μG hρcont u u' R
  have hIPQ : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α * colRe ρ u u' Q α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {P, Q}
      (fun _ => 1)).congr (Filter.Eventually.of_forall fun α => by
        simp only [Finset.prod_pair hPQ, pow_one])
  have hIPR : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {P, R}
      (fun _ => 1)).congr (Filter.Eventually.of_forall fun α => by
        simp only [Finset.prod_pair hPR, pow_one])
  have hIQR : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' Q α * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {Q, R}
      (fun _ => 1)).congr (Filter.Eventually.of_forall fun α => by
        simp only [Finset.prod_pair hQR, pow_one])
  have hIP2 : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α ^ 2)
      (Measure.pi fun _ : LayerSite N => μG) :=
    integrable_colRe_pow ρ μG hρcont u u' P 2
  have hIPQR : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α * colRe ρ u u' Q α * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {P, Q, R}
      (fun _ => 1)).congr (Filter.Eventually.of_forall fun α => by
        show (∏ Z ∈ ({P, Q, R} : Finset (LayerColumn N)),
            (colRe ρ u u' Z α) ^ (1 : ℕ))
          = colRe ρ u u' P α * colRe ρ u u' Q α
            * colRe ρ u u' R α
        rw [Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton,
            not_or]; exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR]
        simp only [pow_one]; ring)
  have hIP2Q : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {P, Q}
      (fun Z => if Z = P then 2 else 1)).congr
      (Filter.Eventually.of_forall fun α => by
        show (∏ Z ∈ ({P, Q} : Finset (LayerColumn N)),
            (colRe ρ u u' Z α) ^ (if Z = P then 2 else 1))
          = colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
        rw [Finset.prod_pair hPQ, if_pos rfl,
          if_neg (fun h : Q = P => hPQ h.symm)]
        simp only [pow_one])
  have hIP2R : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α ^ 2 * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {P, R}
      (fun Z => if Z = P then 2 else 1)).congr
      (Filter.Eventually.of_forall fun α => by
        show (∏ Z ∈ ({P, R} : Finset (LayerColumn N)),
            (colRe ρ u u' Z α) ^ (if Z = P then 2 else 1))
          = colRe ρ u u' P α ^ 2 * colRe ρ u u' R α
        rw [Finset.prod_pair hPR, if_pos rfl,
          if_neg (fun h : R = P => hPR h.symm)]
        simp only [pow_one])
  have hIP2QR : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
        * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_colRe_prod_pow ρ μG hρcont u u' {P, Q, R}
      (fun Z => if Z = P then 2 else 1)).congr
      (Filter.Eventually.of_forall fun α => by
        show (∏ Z ∈ ({P, Q, R} : Finset (LayerColumn N)),
            (colRe ρ u u' Z α) ^ (if Z = P then 2 else 1))
          = colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
            * colRe ρ u u' R α
        rw [Finset.prod_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton,
            not_or]; exact ⟨hPQ, hPR⟩), Finset.prod_pair hQR,
          if_pos rfl, if_neg (fun h : Q = P => hPQ h.symm),
          if_neg (fun h : R = P => hPR h.symm)]
        simp only [pow_one]; ring)
  -- group integrals
  have hI2P : Integrable (fun α : LayerSite N → G =>
      2 * colRe ρ u u' P α)
      (Measure.pi fun _ : LayerSite N => μG) := hIP.const_mul 2
  have hI2PQ : Integrable (fun α : LayerSite N → G =>
      2 * colRe ρ u u' P α + colRe ρ u u' Q α)
      (Measure.pi fun _ : LayerSite N => μG) := hI2P.add hIQ
  have hG1 : ∫ α : LayerSite N → G, (2 * colRe ρ u u' P α
        + colRe ρ u u' Q α + colRe ρ u u' R α)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 4 * e1 ρ μG := by
    rw [integral_add hI2PQ hIR, integral_add hI2P hIQ,
      integral_const_mul, integral_colRe ρ μG hN hρcont u u' P,
      integral_colRe ρ μG hN hρcont u u' Q,
      integral_colRe ρ μG hN hρcont u u' R]
    ring
  have hI2a : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' Q α * colRe ρ u u' R α
        + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hIQR.add (hIPQ.const_mul 2)
  have hI2b : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' Q α * colRe ρ u u' R α
        + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
        + 2 * (colRe ρ u u' P α * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hI2a.add (hIPR.const_mul 2)
  have hG2 : ∫ α : LayerSite N → G, (colRe ρ u u' Q α
        * colRe ρ u u' R α + 2 * (colRe ρ u u' P α
          * colRe ρ u u' Q α) + 2 * (colRe ρ u u' P α
          * colRe ρ u u' R α) + colRe ρ u u' P α ^ 2)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 5 * (e1 ρ μG) ^ 2 + realMoment ρ μG 2 := by
    rw [integral_add hI2b hIP2, integral_add hI2a
        (hIPR.const_mul 2), integral_add hIQR (hIPQ.const_mul 2),
      integral_const_mul, integral_const_mul,
      integral_cross ρ μG hN hN3 hρcont u u' hQR,
      integral_cross ρ μG hN hN3 hρcont u u' hPQ,
      integral_cross ρ μG hN hN3 hρcont u u' hPR,
      show ∫ α : LayerSite N → G, colRe ρ u u' P α ^ 2
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG 2 from
        colMoment_eq ρ μG hN hρcont u u' P 2]
    ring
  have hG3 : ∫ α : LayerSite N → G, colRe ρ u u' P α
        * colRe ρ u u' Q α * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (e1 ρ μG) ^ 3 := by
    rw [integral_colRe_triple ρ μG hN hN3 hρcont u u' hPQ hPR
      hQR, realMoment_one]
  have hG4 : ∫ α : LayerSite N → G, (colRe ρ u u' P α ^ 2
        * colRe ρ u u' Q α + colRe ρ u u' P α ^ 2
        * colRe ρ u u' R α)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 2 * (realMoment ρ μG 2 * e1 ρ μG) := by
    have h1 : ∫ α : LayerSite N → G, colRe ρ u u' P α ^ 2
          * colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG 2 * e1 ρ μG := by
      rw [integral_congr_ae (Filter.Eventually.of_forall
        fun α => by simp only [pow_one] :
          (fun α : LayerSite N → G => colRe ρ u u' P α ^ 2
            * colRe ρ u u' Q α) =ᵐ[Measure.pi
              fun _ : LayerSite N => μG]
            fun α => colRe ρ u u' P α ^ 2
              * (colRe ρ u u' Q α) ^ 1),
        integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPQ 2 1,
        realMoment_one]
    have h2 : ∫ α : LayerSite N → G, colRe ρ u u' P α ^ 2
          * colRe ρ u u' R α
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = realMoment ρ μG 2 * e1 ρ μG := by
      rw [integral_congr_ae (Filter.Eventually.of_forall
        fun α => by simp only [pow_one] :
          (fun α : LayerSite N → G => colRe ρ u u' P α ^ 2
            * colRe ρ u u' R α) =ᵐ[Measure.pi
              fun _ : LayerSite N => μG]
            fun α => colRe ρ u u' P α ^ 2
              * (colRe ρ u u' R α) ^ 1),
        integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPR 2 1,
        realMoment_one]
    rw [integral_add hIP2Q hIP2R, h1, h2]
    ring
  have hG5 : ∫ α : LayerSite N → G, colRe ρ u u' P α ^ 2
        * colRe ρ u u' Q α * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = realMoment ρ μG 2 * (e1 ρ μG) ^ 2 :=
    integral_colRe_sq_mul_mul ρ μG hN hN3 hρcont u u' hPQ hPR
      hQR
  -- the pointwise grouped expansion
  have hpt : ∀ α : LayerSite N → G,
      colDensC ρ u u' P α ^ 2 * colDensC ρ u u' Q α
          * colDensC ρ u u' R α
        = 1 - x * (2 * colRe ρ u u' P α + colRe ρ u u' Q α
            + colRe ρ u u' R α)
          + x ^ 2 * (colRe ρ u u' Q α * colRe ρ u u' R α
            + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
            + 2 * (colRe ρ u u' P α * colRe ρ u u' R α)
            + colRe ρ u u' P α ^ 2)
          - 2 * x ^ 3 * (colRe ρ u u' P α * colRe ρ u u' Q α
            * colRe ρ u u' R α)
          - x ^ 3 * (colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
            + colRe ρ u u' P α ^ 2 * colRe ρ u u' R α)
          + x ^ 4 * (colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
            * colRe ρ u u' R α) := by
    intro α
    rw [colDensC_eq, colDensC_eq, colDensC_eq, hx,
      div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul]
    ring
  -- assembly integrability, pointwise annotated
  have hInt1 : Integrable (fun α : LayerSite N → G =>
      2 * colRe ρ u u' P α + colRe ρ u u' Q α
        + colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) := hI2PQ.add hIR
  have hInt2 : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' Q α * colRe ρ u u' R α
        + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
        + 2 * (colRe ρ u u' P α * colRe ρ u u' R α)
        + colRe ρ u u' P α ^ 2)
      (Measure.pi fun _ : LayerSite N => μG) := hI2b.add hIP2
  have hInt4 : Integrable (fun α : LayerSite N → G =>
      colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
        + colRe ρ u u' P α ^ 2 * colRe ρ u u' R α)
      (Measure.pi fun _ : LayerSite N => μG) := hIP2Q.add hIP2R
  have hF1 : Integrable (fun _ : LayerSite N → G => (1 : ℝ))
      (Measure.pi fun _ : LayerSite N => μG) := integrable_const 1
  have hF2 : Integrable (fun α : LayerSite N → G =>
      x * (2 * colRe ρ u u' P α + colRe ρ u u' Q α
        + colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) := hInt1.const_mul x
  have hF3 : Integrable (fun α : LayerSite N → G =>
      x ^ 2 * (colRe ρ u u' Q α * colRe ρ u u' R α
        + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
        + 2 * (colRe ρ u u' P α * colRe ρ u u' R α)
        + colRe ρ u u' P α ^ 2))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hInt2.const_mul (x ^ 2)
  have hF4 : Integrable (fun α : LayerSite N → G =>
      2 * x ^ 3 * (colRe ρ u u' P α * colRe ρ u u' Q α
        * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hIPQR.const_mul (2 * x ^ 3)
  have hF5 : Integrable (fun α : LayerSite N → G =>
      x ^ 3 * (colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
        + colRe ρ u u' P α ^ 2 * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hInt4.const_mul (x ^ 3)
  have hF6 : Integrable (fun α : LayerSite N → G =>
      x ^ 4 * (colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
        * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) :=
    hIP2QR.const_mul (x ^ 4)
  have hT1 : Integrable (fun α : LayerSite N → G =>
      1 - x * (2 * colRe ρ u u' P α + colRe ρ u u' Q α
        + colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) := hF1.sub hF2
  have hT2 : Integrable (fun α : LayerSite N → G =>
      1 - x * (2 * colRe ρ u u' P α + colRe ρ u u' Q α
          + colRe ρ u u' R α)
        + x ^ 2 * (colRe ρ u u' Q α * colRe ρ u u' R α
          + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
          + 2 * (colRe ρ u u' P α * colRe ρ u u' R α)
          + colRe ρ u u' P α ^ 2))
      (Measure.pi fun _ : LayerSite N => μG) := hT1.add hF3
  have hT3 : Integrable (fun α : LayerSite N → G =>
      1 - x * (2 * colRe ρ u u' P α + colRe ρ u u' Q α
          + colRe ρ u u' R α)
        + x ^ 2 * (colRe ρ u u' Q α * colRe ρ u u' R α
          + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
          + 2 * (colRe ρ u u' P α * colRe ρ u u' R α)
          + colRe ρ u u' P α ^ 2)
        - 2 * x ^ 3 * (colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) := hT2.sub hF4
  have hT4 : Integrable (fun α : LayerSite N → G =>
      1 - x * (2 * colRe ρ u u' P α + colRe ρ u u' Q α
          + colRe ρ u u' R α)
        + x ^ 2 * (colRe ρ u u' Q α * colRe ρ u u' R α
          + 2 * (colRe ρ u u' P α * colRe ρ u u' Q α)
          + 2 * (colRe ρ u u' P α * colRe ρ u u' R α)
          + colRe ρ u u' P α ^ 2)
        - 2 * x ^ 3 * (colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α)
        - x ^ 3 * (colRe ρ u u' P α ^ 2 * colRe ρ u u' Q α
          + colRe ρ u u' P α ^ 2 * colRe ρ u u' R α))
      (Measure.pi fun _ : LayerSite N => μG) := hT3.sub hF5
  have hA2 : densMomentValue ρ μG 2
      = 1 - 2 * (d : ℝ)⁻¹ * e1 ρ μG
        + ((d : ℝ)⁻¹) ^ 2 * realMoment ρ μG 2 := by
    unfold densMomentValue
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose_self, Nat.choose_one_right, Nat.choose_zero_right,
      realMoment_zero, realMoment_one, pow_zero, pow_one,
      Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add hT4 hF6, integral_sub hT3 hF5,
    integral_sub hT2 hF4, integral_add hT1 hF3,
    integral_sub hF1 hF2, integral_const, probReal_univ,
    one_smul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    hG1, hG2, hG3, hG4, hG5, hA2, hx, div_eq_inv_mul]
  ring

end ClosedForm4

section CountingBridge

variable {N : ℕ}

/-- The nested erase sum: sum over ordered tuples of
distinct columns drawn from `A`, of `g` applied to
the accumulated set (starting from `C₀`). At length
`n` and `C₀ = ∅` this is the ordered-tuple form of a
sum over `n`-subsets. -/
noncomputable def nestSumFrom (g : Finset (LayerColumn N) → ℝ)
    (C₀ : Finset (LayerColumn N)) :
    ℕ → Finset (LayerColumn N) → ℝ
  | 0, _ => g C₀
  | (n + 1), A => ∑ P ∈ A, nestSumFrom g (insert P C₀) n
      (A.erase P)

/-- **The fiber step of the counting bridge:** summing
`h (insert P C)` over all pairs `(P, C)` with `C` an
`n`-subset of `A.erase P` counts each `(n+1)`-subset
of `A` exactly `n + 1` times. -/
theorem ordered_tuple_count (h : Finset (LayerColumn N) → ℝ)
    (A : Finset (LayerColumn N)) (n : ℕ) :
    ∑ P ∈ A, ∑ C ∈ (A.erase P).powersetCard n, h (insert P C)
      = (n + 1 : ℝ) * ∑ D ∈ A.powersetCard (n + 1), h D := by
  classical
  have hmaps : ∀ x ∈ A.sigma (fun P => (A.erase P).powersetCard n),
      (fun x : (Σ _ : LayerColumn N, Finset (LayerColumn N)) =>
        insert x.1 x.2) x ∈ A.powersetCard (n + 1) := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hP, hC⟩ := hx
    rw [Finset.mem_powersetCard] at hC ⊢
    obtain ⟨hCsub, hCcard⟩ := hC
    refine ⟨?_, ?_⟩
    · exact Finset.insert_subset hP
        (hCsub.trans (Finset.erase_subset x.1 A))
    · have hnot : x.1 ∉ x.2 :=
        fun hm => (Finset.notMem_erase x.1 A)
          (hCsub hm)
      rw [Finset.card_insert_of_notMem hnot, hCcard]
  have hfiber : ∀ D ∈ A.powersetCard (n + 1),
      ∑ x ∈ (A.sigma (fun P => (A.erase P).powersetCard n)
        ).filter (fun x : (Σ _ : LayerColumn N,
            Finset (LayerColumn N)) => insert x.1 x.2 = D),
        h (insert x.1 x.2) = (n + 1 : ℝ) * h D := by
    intro D hD
    rw [Finset.mem_powersetCard] at hD
    obtain ⟨hDsub, hDcard⟩ := hD
    have hfilter : (A.sigma (fun P => (A.erase P).powersetCard n)
        ).filter (fun x : (Σ _ : LayerColumn N,
            Finset (LayerColumn N)) => insert x.1 x.2 = D)
        = D.image (fun P => (⟨P, D.erase P⟩ :
            (Σ _ : LayerColumn N, Finset (LayerColumn N)))) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sigma,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨hP, hC⟩, hins⟩
        rw [Finset.mem_powersetCard] at hC
        obtain ⟨hCsub, hCcard⟩ := hC
        have hPD : x.1 ∈ D := hins ▸ Finset.mem_insert_self _ _
        have hCeq : x.2 = D.erase x.1 := by
          have h1 : x.1 ∉ x.2 :=
            fun hm => (Finset.notMem_erase x.1 A) (hCsub hm)
          have h2 : (insert x.1 x.2).erase x.1 = x.2 :=
            Finset.erase_insert h1
          rw [hins] at h2
          exact h2.symm
        exact ⟨x.1, hPD, by rw [← hCeq]⟩
      · rintro ⟨P, hPD, hx⟩
        have hPA : P ∈ A := hDsub hPD
        rw [← hx]
        refine ⟨⟨hPA, ?_⟩, ?_⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨Finset.erase_subset_erase P hDsub, ?_⟩
          rw [Finset.card_erase_of_mem hPD, hDcard]
          exact Nat.add_sub_cancel n 1
        · exact Finset.insert_erase hPD
    rw [hfilter]
    rw [Finset.sum_image (fun P hP Q hQ hPQ =>
      Sigma.mk.inj_iff.mp hPQ |>.1)]
    rw [Finset.sum_congr rfl (g := fun P : LayerColumn N => h D)
      (fun P hPD => by rw [Finset.insert_erase hPD])]
    rw [Finset.sum_const, hDcard, nsmul_eq_mul]
    norm_cast
  rw [Finset.sum_sigma' (f := fun (P : LayerColumn N)
      (C : Finset (LayerColumn N)) => h (insert P C))]
  show (∑ x ∈ A.sigma (fun P => (A.erase P).powersetCard n),
      h (insert x.1 x.2)) = (n + 1 : ℝ)
        * ∑ D ∈ A.powersetCard (n + 1), h D
  rw [← Finset.sum_fiberwise_of_maps_to hmaps,
    Finset.sum_congr rfl hfiber, Finset.mul_sum]

/-- **The counting bridge:** the nested erase sum of
length `n` over `A` is `n!` times the sum over the
`n`-subsets of `A`. -/
theorem nestSumFrom_eq (g : Finset (LayerColumn N) → ℝ) :
    ∀ (C₀ : Finset (LayerColumn N)) (n : ℕ)
      (A : Finset (LayerColumn N)),
      nestSumFrom g C₀ n A
        = (Nat.factorial n : ℝ) * ∑ C ∈ A.powersetCard n,
          g (C₀ ∪ C) := by
  intro C₀ n
  induction n generalizing C₀ with
  | zero =>
    intro A
    simp only [nestSumFrom, Finset.powersetCard_zero,
      Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one,
      one_mul, Finset.union_empty]
  | succ n ih =>
    intro A
    have step1 : nestSumFrom g C₀ (n + 1) A
        = ∑ P ∈ A, nestSumFrom g (insert P C₀) n (A.erase P) :=
      rfl
    rw [step1, Finset.sum_congr rfl
      (fun P _ => ih (insert P C₀) (A.erase P))]
    rw [← Finset.mul_sum]
    have hset : ∀ (P : LayerColumn N)
        (C : Finset (LayerColumn N)),
        insert P C₀ ∪ C = C₀ ∪ insert P C := by
      intro P C
      ext y
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [Finset.sum_congr rfl (fun P _ =>
      Finset.sum_congr rfl (fun C _ => by rw [hset P C]))]
    rw [ordered_tuple_count (fun D => g (C₀ ∪ D)) A n,
      Nat.factorial_succ]
    push_cast
    ring

/-- The bridge at length four, from the empty
accumulator: the ordered distinct-quadruple sum is
`24` times the sum over the `4`-subsets. -/
theorem nested_quadruple_sum_eq (g : Finset (LayerColumn N) → ℝ)
    (A : Finset (LayerColumn N)) :
    (∑ P ∈ A, ∑ Q ∈ A.erase P, ∑ R ∈ (A.erase P).erase Q,
      ∑ S ∈ ((A.erase P).erase Q).erase R, g {P, Q, R, S})
      = 24 * ∑ C ∈ A.powersetCard 4, g C := by
  classical
  have h := nestSumFrom_eq g ∅ 4 A
  have hunfold : nestSumFrom g ∅ 4 A
      = ∑ P ∈ A, ∑ Q ∈ A.erase P, ∑ R ∈ (A.erase P).erase Q,
        ∑ S ∈ ((A.erase P).erase Q).erase R,
        g (insert S (insert R (insert Q {P}))) := rfl
  have hset : ∀ P Q R S : LayerColumn N,
      insert S (insert R (insert Q {P}))
        = ({P, Q, R, S} : Finset (LayerColumn N)) := by
    intro P Q R S
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hunfold] at h
  rw [Finset.sum_congr rfl (fun P _ =>
    Finset.sum_congr rfl (fun Q _ =>
    Finset.sum_congr rfl (fun R _ =>
    Finset.sum_congr rfl (fun S _ => by rw [hset P Q R S]))))] at h
  rw [h]
  norm_num [Nat.factorial, Finset.empty_union]

end CountingBridge

section Assembly4

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant]

/-- Column densities are bounded by `2`. -/
theorem abs_colDensC_le
    (u u' : LayerLink N → G) (X : LayerColumn N)
    (α : LayerSite N → G) :
    |colDensC ρ u u' X α| ≤ 2 := by
  rw [colDensC_eq]
  have h1 : |colRe ρ u u' X α| ≤ (d : ℝ) :=
    abs_re_charFn_le ρ _
  have h2 : |colRe ρ u u' X α / (d : ℝ)| ≤ 1 := by
    rcases eq_or_ne d 0 with hd | hd
    · have hd0 : (d : ℝ) = 0 := by
        rw [hd]
        exact Nat.cast_zero
      have h0 : colRe ρ u u' X α = 0 := by
        have hle : |colRe ρ u u' X α| ≤ 0 := hd0 ▸ h1
        exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
      rw [h0, zero_div, abs_zero]
      exact zero_le_one
    · have hdabs : |(d : ℝ)| = (d : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg d)
      rw [abs_div, hdabs]
      exact div_le_one_of_le₀ h1 (Nat.cast_nonneg d)
  calc |1 - colRe ρ u u' X α / (d : ℝ)|
      ≤ |1| + |colRe ρ u u' X α / (d : ℝ)| := abs_sub _ _
    _ ≤ 2 := by rw [abs_one]; linarith

/-- Quadruple products of column densities are
integrable (bounded by `2⁴`). -/
theorem integrable_colDensC_prod4
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (A B C X : LayerColumn N) :
    Integrable (fun α => colDensC ρ u u' A α
        * colDensC ρ u u' B α * colDensC ρ u u' C α
        * colDensC ρ u u' X α)
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine Integrable.of_bound ?_ (16 : ℝ)
    (Filter.Eventually.of_forall fun α => ?_)
  · exact (((measurable_colDens ρ hρcont u u' A.1 A.2.1 A.2.2
      ).mul (measurable_colDens ρ hρcont u u' B.1 B.2.1 B.2.2)
      ).mul (measurable_colDens ρ hρcont u u' C.1 C.2.1 C.2.2)
      ).mul (measurable_colDens ρ hρcont u u' X.1 X.2.1 X.2.2)
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have hA := abs_colDensC_le ρ u u' A α
    have hB := abs_colDensC_le ρ u u' B α
    have hC := abs_colDensC_le ρ u u' C α
    have hX := abs_colDensC_le ρ u u' X α
    calc |colDensC ρ u u' A α| * |colDensC ρ u u' B α|
          * |colDensC ρ u u' C α| * |colDensC ρ u u' X α|
        ≤ 2 * 2 * 2 * 2 :=
          mul_le_mul (mul_le_mul (mul_le_mul hA hB
            (abs_nonneg _) (by norm_num)) hC (abs_nonneg _)
            (by norm_num)) hX (abs_nonneg _) (by norm_num)
      _ = 16 := by norm_num

/-- The two-column density pattern at arbitrary
degrees, in the assembly's value vocabulary:
`∫ dens_A^j · dens_B^k = A_j · A_k`. -/
theorem integral_colDens_pow_mul_value (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {A B : LayerColumn N}
    (hAB : A ≠ B) (j k : ℕ) :
    ∫ α : LayerSite N → G, (colDensC ρ u u' A α) ^ j
          * (colDensC ρ u u' B α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG j * densMomentValue ρ μG k := by
  rw [integral_colDens_pow_mul ρ μG hN hN3 hρcont u u' hAB j k,
    densMomentValue_eq ρ μG hN hρcont u u' A j,
    densMomentValue_eq ρ μG hN hρcont u u' B k]

/-- Rearrangement of a four-density integrand: the
integral depends only on the multiset of columns. -/
theorem integral_colDens_four_congr
    (u u' : LayerLink N → G) (A B C X : LayerColumn N)
    (A' B' C' X' : LayerColumn N)
    (h : ∀ α : LayerSite N → G,
      colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' C α * colDensC ρ u u' X α
        = colDensC ρ u u' A' α * colDensC ρ u u' B' α
          * colDensC ρ u u' C' α * colDensC ρ u u' X' α) :
    ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' C α
          * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, colDensC ρ u u' A' α
          * colDensC ρ u u' B' α * colDensC ρ u u' C' α
          * colDensC ρ u u' X' α
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
  integral_congr_ae (Filter.Eventually.of_forall h)

/-- The tuple product over four distinct columns is
the finset product over their set. -/
theorem integral_colDens_tuple_eq_finset
    (u u' : LayerLink N → G) {A B C X : LayerColumn N}
    (hAB : A ≠ B) (hAC : A ≠ C) (hAX : A ≠ X) (hBC : B ≠ C)
    (hBX : B ≠ X) (hCX : C ≠ X) :
    ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' C α
          * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          ∏ P ∈ ({A, B, C, X} : Finset (LayerColumn N)),
            colDensC ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  show colDensC ρ u u' A α * colDensC ρ u u' B α
      * colDensC ρ u u' C α * colDensC ρ u u' X α
    = ∏ P ∈ ({A, B, C, X} : Finset (LayerColumn N)),
      colDensC ρ u u' P α
  rw [Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hAB, hAC, hAX⟩),
    Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hBC, hBX⟩),
    Finset.prod_insert (by
      simp only [Finset.mem_singleton]
      exact hCX), Finset.prod_singleton]
  ring

/-- There are at least three columns. -/
theorem three_le_card_columns :
    3 ≤ Fintype.card (LayerColumn N) := by
  classical
  have hne : ∀ {ν μ : Fin 4} (hν : ν ≠ 0) (hμ : μ ≠ 0),
      ν ≠ μ →
      (⟨⟨fun _ => 0, by simp⟩, ⟨ν, hν⟩⟩ : LayerColumn N)
        ≠ ⟨⟨fun _ => 0, by simp⟩, ⟨μ, hμ⟩⟩ := by
    intro ν μ hν hμ hνμ h
    have h2 := congrArg (fun P : LayerColumn N => (P.2 : Fin 4)) h
    simp only [] at h2
    exact hνμ h2
  have h3 : ({(⟨⟨fun _ => 0, by simp⟩, ⟨1, by decide⟩⟩ :
        LayerColumn N),
      ⟨⟨fun _ => 0, by simp⟩, ⟨2, by decide⟩⟩,
      ⟨⟨fun _ => 0, by simp⟩, ⟨3, by decide⟩⟩} :
      Finset (LayerColumn N)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hne (by decide) (by decide) (by decide),
        hne (by decide) (by decide) (by decide)⟩),
      Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact hne (by decide) (by decide) (by decide)),
      Finset.card_singleton]
  have hle : ({(⟨⟨fun _ => 0, by simp⟩, ⟨1, by decide⟩⟩ :
        LayerColumn N),
      ⟨⟨fun _ => 0, by simp⟩, ⟨2, by decide⟩⟩,
      ⟨⟨fun _ => 0, by simp⟩, ⟨3, by decide⟩⟩} :
      Finset (LayerColumn N)).card ≤ Finset.univ.card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_univ, h3] at hle
  exact hle

/-- Real casts of erased column counts. -/
theorem cast_card_erase (A : LayerColumn N) :
    ((Finset.univ.erase A).card : ℝ) = colCount N - 1 := by
  have h1 : 1 ≤ Fintype.card (LayerColumn N) := by
    have h3 : 3 ≤ Fintype.card (LayerColumn N) :=
      three_le_card_columns
    omega
  rw [Finset.card_erase_of_mem (Finset.mem_univ A),
    Finset.card_univ, Nat.cast_sub h1, Nat.cast_one]
  rfl

theorem cast_card_erase_two {A B : LayerColumn N}
    (hAB : B ∈ Finset.univ.erase A) :
    (((Finset.univ.erase A).erase B).card : ℝ)
      = colCount N - 2 := by
  have h3 : 3 ≤ Fintype.card (LayerColumn N) :=
    three_le_card_columns
  have heq : Fintype.card (LayerColumn N) - 1 - 1
      = Fintype.card (LayerColumn N) - 2 := by omega
  rw [Finset.card_erase_of_mem hAB,
    Finset.card_erase_of_mem (Finset.mem_univ A),
    Finset.card_univ, heq,
    Nat.cast_sub (by omega : 2 ≤ Fintype.card (LayerColumn N)),
    Nat.cast_ofNat]
  rfl

theorem cast_card_erase_three {A B C : LayerColumn N}
    (hAB : B ∈ Finset.univ.erase A)
    (hABC : C ∈ (Finset.univ.erase A).erase B) :
    (((Finset.univ.erase A).erase B).erase C).card
      = ((colCount N - 3 : ℝ)) := by
  have h3 : 3 ≤ Fintype.card (LayerColumn N) :=
    three_le_card_columns
  have heq : Fintype.card (LayerColumn N) - 1 - 1 - 1
      = Fintype.card (LayerColumn N) - 3 := by omega
  have hcard : (((Finset.univ.erase A).erase B).erase C).card
      = Fintype.card (LayerColumn N) - 3 := by
    rw [Finset.card_erase_of_mem hABC,
      Finset.card_erase_of_mem hAB,
      Finset.card_erase_of_mem (Finset.mem_univ A),
      Finset.card_univ, heq]
  rw [hcard, Nat.cast_sub (by omega :
    3 ≤ Fintype.card (LayerColumn N)), Nat.cast_ofNat]
  rfl

/-- The first density moment is the factorized
value `B = 1 − e₁/d`. -/
theorem densMomentValue_one :
    densMomentValue ρ μG 1 = 1 - e1 ρ μG / (d : ℝ) := by
  unfold densMomentValue
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_self, Nat.choose_one_right, Nat.choose_zero_right,
    realMoment_zero, realMoment_one, pow_zero, pow_one,
    Nat.cast_ofNat, Nat.cast_one]
  rw [div_eq_inv_mul]
  ring

/-- **Inner sum, pattern (3,·):** summing the fourth
integral index over a tripled column. -/
theorem inner_sum_self (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (A : LayerColumn N) :
    ∑ X : LayerColumn N, ∫ α : LayerSite N → G,
          colDensC ρ u u' A α * colDensC ρ u u' A α
          * colDensC ρ u u' A α * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 4
        + (colCount N - 1) * (densMomentValue ρ μG 3
          * (1 - e1 ρ μG / (d : ℝ))) := by
  classical
  rw [← Finset.add_sum_erase Finset.univ
    (fun X => ∫ α : LayerSite N → G, colDensC ρ u u' A α
      * colDensC ρ u u' A α * colDensC ρ u u' A α
      * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG))
    (Finset.mem_univ A)]
  congr 1
  · have h1 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' A α * colDensC ρ u u' A α
          * colDensC ρ u u' A α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = colDensMoment ρ μG u u' A 4 :=
      integral_congr_ae (Filter.Eventually.of_forall fun α => by
        show colDensC ρ u u' A α * colDensC ρ u u' A α
            * colDensC ρ u u' A α * colDensC ρ u u' A α
          = (colDensC ρ u u' A α) ^ 4
        ring)
    rw [h1, densMomentValue_eq ρ μG hN hρcont u u' A 4]
  · rw [Finset.sum_congr rfl (g := fun _ : LayerColumn N =>
        densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)))
      (fun X hX => by
        have hXA : X ≠ A := Finset.ne_of_mem_erase hX
        have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
              * colDensC ρ u u' A α * colDensC ρ u u' A α
              * colDensC ρ u u' X α
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = ∫ α : LayerSite N → G, (colDensC ρ u u' A α) ^ 3
              * (colDensC ρ u u' X α) ^ 1
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_congr_ae (Filter.Eventually.of_forall
            fun α => by ring)
        rw [h2, integral_colDens_pow_mul_value ρ μG hN hN3
          hρcont u u' (fun h => hXA h.symm) 3 1,
          densMomentValue_one ρ μG]),
      Finset.sum_const, nsmul_eq_mul, cast_card_erase A]

/-- **Inner sum, pattern (2,1,·):** summing the fourth
index over a doubled and a single column. -/
theorem inner_sum_two_one (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {A B : LayerColumn N}
    (hAB : A ≠ B) :
    ∑ X : LayerColumn N, ∫ α : LayerSite N → G,
          colDensC ρ u u' A α * colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ))
        + ((densMomentValue ρ μG 2) ^ 2
          + (colCount N - 2) * (densMomentValue ρ μG 2
            * (1 - e1 ρ μG / (d : ℝ)) ^ 2)) := by
  classical
  have hBmem : B ∈ Finset.univ.erase A :=
    Finset.mem_erase.mpr ⟨fun h => hAB h.symm,
      Finset.mem_univ B⟩
  rw [← Finset.add_sum_erase Finset.univ
    (fun X => ∫ α : LayerSite N → G, colDensC ρ u u' A α
      * colDensC ρ u u' A α * colDensC ρ u u' B α
      * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG))
    (Finset.mem_univ A),
    ← Finset.add_sum_erase (Finset.univ.erase A)
    (fun X => ∫ α : LayerSite N → G, colDensC ρ u u' A α
      * colDensC ρ u u' A α * colDensC ρ u u' B α
      * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG)) hBmem]
  congr 1
  · -- X = A: pattern (3,1)
    have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' A α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, (colDensC ρ u u' A α) ^ 3
          * (colDensC ρ u u' B α) ^ 1
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall
        fun α => by ring)
    rw [h2, integral_colDens_pow_mul_value ρ μG hN hN3 hρcont
      u u' hAB 3 1, densMomentValue_one ρ μG]
  congr 1
  · -- X = B: pattern (2,2)
    have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' B α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, (colDensC ρ u u' A α) ^ 2
          * (colDensC ρ u u' B α) ^ 2
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall
        fun α => by ring)
    rw [h2, integral_colDens_pow_mul_value ρ μG hN hN3 hρcont
      u u' hAB 2 2]
    ring
  · -- X distinct: pattern (2,1,1)
    rw [Finset.sum_congr rfl (g := fun _ : LayerColumn N =>
        densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2)
      (fun X hX => by
        have hXB : X ≠ B := Finset.ne_of_mem_erase hX
        have hXA : X ≠ A :=
          Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hX)
        have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
              * colDensC ρ u u' A α * colDensC ρ u u' B α
              * colDensC ρ u u' X α
            ∂(Measure.pi fun _ : LayerSite N => μG)
          = ∫ α : LayerSite N → G, (colDensC ρ u u' A α) ^ 2
              * colDensC ρ u u' B α * colDensC ρ u u' X α
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
          integral_congr_ae (Filter.Eventually.of_forall
            fun α => by ring)
        rw [h2]
        exact integral_colDens_sq_mul_mul ρ μG hN hN3 hρcont
          u u' hAB (fun h => hXA h.symm) (fun h => hXB h.symm)),
      Finset.sum_const, nsmul_eq_mul,
      cast_card_erase_two hBmem]

/-- **Inner sum, pattern (1,1,1,·):** summing the
fourth index over three distinct columns. The three
diagonal hits are the (2,1,1) value; the distinct
hits are the finset quadruple value of the earlier
section, whose excess over `B⁴` is the dependent
remainder. -/
theorem inner_sum_distinct (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {A B C : LayerColumn N}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∑ X : LayerColumn N, ∫ α : LayerSite N → G,
          colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' C α * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
        + (densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
          + (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + ((colCount N - 3) * (1 - e1 ρ μG / (d : ℝ)) ^ 4
              + ((d : ℝ)⁻¹) ^ 4
                * ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
                  (quadReMoment ρ μG {A, B, C, X} u u'
                    - (e1 ρ μG) ^ 4)))) := by
  classical
  have hBmem : B ∈ Finset.univ.erase A :=
    Finset.mem_erase.mpr ⟨fun h => hAB h.symm,
      Finset.mem_univ B⟩
  have hCmem : C ∈ (Finset.univ.erase A).erase B :=
    Finset.mem_erase.mpr ⟨fun h => hBC h.symm,
      Finset.mem_erase.mpr ⟨fun h => hAC h.symm,
        Finset.mem_univ C⟩⟩
  rw [← Finset.add_sum_erase Finset.univ
    (fun X => ∫ α : LayerSite N → G, colDensC ρ u u' A α
      * colDensC ρ u u' B α * colDensC ρ u u' C α
      * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG))
    (Finset.mem_univ A),
    ← Finset.add_sum_erase (Finset.univ.erase A)
    (fun X => ∫ α : LayerSite N → G, colDensC ρ u u' A α
      * colDensC ρ u u' B α * colDensC ρ u u' C α
      * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG)) hBmem,
    ← Finset.add_sum_erase ((Finset.univ.erase A).erase B)
    (fun X => ∫ α : LayerSite N → G, colDensC ρ u u' A α
      * colDensC ρ u u' B α * colDensC ρ u u' C α
      * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG)) hCmem]
  congr 1
  · -- X = A: pattern (2,1,1) at (A, B, C)
    have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' C α
          * colDensC ρ u u' A α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, (colDensC ρ u u' A α) ^ 2
          * colDensC ρ u u' B α * colDensC ρ u u' C α
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall
        fun α => by ring)
    rw [h2]
    exact integral_colDens_sq_mul_mul ρ μG hN hN3 hρcont
      u u' hAB hAC hBC
  congr 1
  · -- X = B: pattern (2,1,1) at (B, A, C)
    have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' C α
          * colDensC ρ u u' B α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, (colDensC ρ u u' B α) ^ 2
          * colDensC ρ u u' A α * colDensC ρ u u' C α
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall
        fun α => by ring)
    rw [h2]
    exact integral_colDens_sq_mul_mul ρ μG hN hN3 hρcont
      u u' (fun h => hAB h.symm) hBC hAC
  congr 1
  · -- X = C: pattern (2,1,1) at (C, A, B)
    have h2 : ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' C α
          * colDensC ρ u u' C α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, (colDensC ρ u u' C α) ^ 2
          * colDensC ρ u u' A α * colDensC ρ u u' B α
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall
        fun α => by ring)
    rw [h2]
    exact integral_colDens_sq_mul_mul ρ μG hN hN3 hρcont
      u u' (fun h => hAC h.symm) (fun h => hBC h.symm) hAB
  · -- X distinct: the finset quadruple value
    rw [Finset.sum_congr rfl (g := fun X : LayerColumn N =>
        (1 - e1 ρ μG / (d : ℝ)) ^ 4 + ((d : ℝ)⁻¹) ^ 4
          * (quadReMoment ρ μG {A, B, C, X} u u'
            - (e1 ρ μG) ^ 4))
      (fun X hX => by
        have hXC : X ≠ C := Finset.ne_of_mem_erase hX
        have hXB : X ≠ B :=
          Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hX)
        have hXA : X ≠ A :=
          Finset.ne_of_mem_erase
            (Finset.mem_of_mem_erase
              (Finset.mem_of_mem_erase hX))
        have hcard : ({A, B, C, X} : Finset (LayerColumn N)
            ).card = 4 :=
          Finset.card_eq_four.mpr ⟨A, B, C, X, hAB, hAC,
            fun h => hXA h.symm, hBC, fun h => hXB h.symm,
            fun h => hXC h.symm, rfl⟩
        rw [integral_colDens_tuple_eq_finset ρ μG u u' hAB
          hAC (fun h => hXA h.symm) hBC (fun h => hXB h.symm)
          (fun h => hXC h.symm)]
        exact integral_colDens_prod_quadruple ρ μG hN hN3
          hρcont u u' {A, B, C, X} hcard),
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      cast_card_erase_three hBmem hCmem, ← Finset.mul_sum]

/-- **The excess vanishes off the primitive
quadruples:** at a non-primitive 4-set some column
has a private site within the set, the character
moment factors (`integral_colRe_quadruple_factor`),
and `quadReMoment C = e₁⁴`. -/
theorem excess_eq_zero_of_not_primitive (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 4) (hCnp : ¬ IsPrimitiveQuad C) :
    quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4 = 0 := by
  classical
  have hex : ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
    by_contra hcon
    apply hCnp
    refine ⟨hC, ?_⟩
    intro P hPC s hsP
    by_contra hnone
    exact hcon ⟨P, hPC, s, hsP, fun Y hYC hYX hsY =>
      hnone ⟨Y, hYC, hYX, hsY⟩⟩
  obtain ⟨X, hXC, s, hsX, hpriv⟩ := hex
  obtain ⟨P, Q, R, S, hPQ, hPR, hPS, hQR, hQS, hRS, hCeq⟩ :=
    Finset.card_eq_four.mp hC
  have hprod : quadReMoment ρ μG C u u'
      = ∫ α : LayerSite N → G, colRe ρ u u' P α
          * colRe ρ u u' Q α * colRe ρ u u' R α
          * colRe ρ u u' S α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
    rw [hCeq]
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun α => ?_)
    show (∏ Z ∈ ({P, Q, R, S} : Finset (LayerColumn N)),
        colRe ρ u u' Z α)
      = colRe ρ u u' P α * colRe ρ u u' Q α
        * colRe ρ u u' R α * colRe ρ u u' S α
    rw [Finset.prod_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton,
          not_or]
        exact ⟨hPQ, hPR, hPS⟩),
      Finset.prod_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton,
          not_or]
        exact ⟨hQR, hQS⟩),
      Finset.prod_insert (by
        simp only [Finset.mem_singleton]
        exact hRS), Finset.prod_singleton]
    ring
  have hXC' : X = P ∨ X = Q ∨ X = R ∨ X = S := by
    rw [hCeq] at hXC
    simpa only [Finset.mem_insert, Finset.mem_singleton]
      using hXC
  have hmem : ∀ Y : LayerColumn N, Y = P ∨ Y = Q ∨ Y = R
      ∨ Y = S → Y ∈ C := by
    intro Y hY
    rw [hCeq]
    rcases hY with rfl | rfl | rfl | rfl <;> simp
  have hval : quadReMoment ρ μG C u u' = (e1 ρ μG) ^ 4 := by
    rw [hprod]
    rcases hXC' with (h | h | h | h) <;> subst X
    · exact integral_colRe_quadruple_factor ρ μG hN hN3
        hρcont u u' hPQ hPR hPS hQR hQS hRS
        (Or.inl ⟨s, hsX, hpriv Q (hmem Q (Or.inr (Or.inl
          rfl))) (fun hh => hPQ hh.symm), hpriv R (hmem R
          (Or.inr (Or.inr (Or.inl rfl)))) (fun hh => hPR
          hh.symm), hpriv S (hmem S (Or.inr (Or.inr
          (Or.inr rfl)))) (fun hh => hPS hh.symm)⟩)
    · exact integral_colRe_quadruple_factor ρ μG hN hN3
        hρcont u u' hPQ hPR hPS hQR hQS hRS
        (Or.inr (Or.inl ⟨s, hsX, hpriv P (hmem P (Or.inl
          rfl)) hPQ, hpriv R (hmem R (Or.inr (Or.inr
          (Or.inl rfl)))) (fun hh => hQR hh.symm), hpriv S
          (hmem S (Or.inr (Or.inr (Or.inr rfl))))
          (fun hh => hQS hh.symm)⟩))
    · exact integral_colRe_quadruple_factor ρ μG hN hN3
        hρcont u u' hPQ hPR hPS hQR hQS hRS
        (Or.inr (Or.inr (Or.inl ⟨s, hsX, hpriv P (hmem P
          (Or.inl rfl)) hPR, hpriv Q (hmem Q (Or.inr
          (Or.inl rfl))) hQR, hpriv S (hmem S (Or.inr
          (Or.inr (Or.inr rfl)))) (fun hh => hRS
          hh.symm)⟩)))
    · exact integral_colRe_quadruple_factor ρ μG hN hN3
        hρcont u u' hPQ hPR hPS hQR hQS hRS
        (Or.inr (Or.inr (Or.inr ⟨s, hsX, hpriv P (hmem P
          (Or.inl rfl)) hPS, hpriv Q (hmem Q (Or.inr
          (Or.inl rfl))) hQS, hpriv R (hmem R (Or.inr
          (Or.inr (Or.inl rfl)))) hRS⟩)))
  rw [hval, sub_self]

/-- The excess sum over all 4-subsets is the excess
sum over the primitive quadruples. -/
theorem sum_powersetCard_four_eq_primitive (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∑ C ∈ Finset.univ.powersetCard 4,
        (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
      = ∑ C ∈ primitiveQuads,
        (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro C hC
    rw [primitiveQuads, Finset.mem_filter] at hC
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ C, hC.2.1⟩
  · intro C hC hCnot
    rw [Finset.mem_powersetCard] at hC
    have hnp : ¬ IsPrimitiveQuad C := by
      intro hprim
      apply hCnot
      rw [primitiveQuads, Finset.mem_filter]
      exact ⟨Finset.mem_univ C, hprim.1, hprim.2⟩
    exact excess_eq_zero_of_not_primitive ρ μG hN hN3
      hρcont u u' hC.2 hnp

/-- **Outer split over the third index,** for two
distinct fixed columns: the `C = A` and `C = B` hits
are the (2,1,·) inner sum; the rest is the
(1,1,1,·) inner sum. -/
theorem sum_over_C_two_one (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {A B : LayerColumn N}
    (hAB : A ≠ B) :
    ∑ C : LayerColumn N, ∑ X : LayerColumn N,
        ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' B α * colDensC ρ u u' C α
          * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ))
          + ((densMomentValue ρ μG 2) ^ 2
            + (colCount N - 2) * (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2))
        + ((densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ))
          + ((densMomentValue ρ μG 2) ^ 2
            + (colCount N - 2) * (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2)))
          + ∑ C ∈ (Finset.univ.erase A).erase B,
            (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + ((colCount N - 3) * (1 - e1 ρ μG / (d : ℝ)) ^ 4
              + ((d : ℝ)⁻¹) ^ 4
                * ∑ X ∈ ((Finset.univ.erase A).erase B
                    ).erase C,
                  (quadReMoment ρ μG {A, B, C, X} u u'
                    - (e1 ρ μG) ^ 4))))) ) := by
  classical
  have hBmem : B ∈ Finset.univ.erase A :=
    Finset.mem_erase.mpr ⟨fun h => hAB h.symm,
      Finset.mem_univ B⟩
  rw [← Finset.add_sum_erase Finset.univ
    (fun C => ∑ X : LayerColumn N,
      ∫ α : LayerSite N → G, colDensC ρ u u' A α
        * colDensC ρ u u' B α * colDensC ρ u u' C α
        * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG))
    (Finset.mem_univ A),
    ← Finset.add_sum_erase (Finset.univ.erase A)
    (fun C => ∑ X : LayerColumn N,
      ∫ α : LayerSite N → G, colDensC ρ u u' A α
        * colDensC ρ u u' B α * colDensC ρ u u' C α
        * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG)) hBmem]
  congr 1
  · -- C = A: rearrange to the (2,1,·) inner sum at (A, B)
    rw [Finset.sum_congr rfl (fun X _ =>
      integral_colDens_four_congr ρ μG u u' A B A X A A B X
        (fun α => by ring))]
    exact inner_sum_two_one ρ μG hN hN3 hρcont u u' hAB
  congr 1
  · -- C = B: rearrange to the (2,1,·) inner sum at (B, A)
    rw [Finset.sum_congr rfl (fun X _ =>
      integral_colDens_four_congr ρ μG u u' A B B X B B A X
        (fun α => by ring))]
    exact inner_sum_two_one ρ μG hN hN3 hρcont u u'
      (fun h => hAB h.symm)
  · -- C distinct: the (1,1,1,·) inner sum
    refine Finset.sum_congr rfl fun C hC => ?_
    have hCB : C ≠ B := Finset.ne_of_mem_erase hC
    have hCA : C ≠ A :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hC)
    exact inner_sum_distinct ρ μG hN hN3 hρcont u u' hAB
      (fun h => hCA h.symm) (fun h => hCB h.symm)

/-- **Outer split over the second index:** the
`B = A` hit is the (3,·) inner sum plus `(M − 1)`
copies of the (2,1,·) value; the rest is the
third-index split. -/
theorem sum_over_BC (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (A : LayerColumn N) :
    ∑ B : LayerColumn N, ∑ C : LayerColumn N,
        ∑ X : LayerColumn N, ∫ α : LayerSite N → G,
          colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' C α * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (densMomentValue ρ μG 4
          + (colCount N - 1) * (densMomentValue ρ μG 3
            * (1 - e1 ρ μG / (d : ℝ)))
        + (colCount N - 1) * (densMomentValue ρ μG 3
            * (1 - e1 ρ μG / (d : ℝ))
          + ((densMomentValue ρ μG 2) ^ 2
            + (colCount N - 2) * (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2))))
        + ∑ B ∈ Finset.univ.erase A,
          (densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ))
            + ((densMomentValue ρ μG 2) ^ 2
              + (colCount N - 2) * (densMomentValue ρ μG 2
                * (1 - e1 ρ μG / (d : ℝ)) ^ 2))
          + (densMomentValue ρ μG 3
              * (1 - e1 ρ μG / (d : ℝ))
            + ((densMomentValue ρ μG 2) ^ 2
              + (colCount N - 2) * (densMomentValue ρ μG 2
                * (1 - e1 ρ μG / (d : ℝ)) ^ 2))
          + ∑ C ∈ (Finset.univ.erase A).erase B,
            (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + (densMomentValue ρ μG 2
              * (1 - e1 ρ μG / (d : ℝ)) ^ 2
            + ((colCount N - 3) * (1 - e1 ρ μG / (d : ℝ)) ^ 4
              + ((d : ℝ)⁻¹) ^ 4
                * ∑ X ∈ ((Finset.univ.erase A).erase B
                    ).erase C,
                  (quadReMoment ρ μG {A, B, C, X} u u'
                    - (e1 ρ μG) ^ 4))))) )) := by
  classical
  rw [← Finset.add_sum_erase Finset.univ
    (fun B => ∑ C : LayerColumn N, ∑ X : LayerColumn N,
      ∫ α : LayerSite N → G, colDensC ρ u u' A α
        * colDensC ρ u u' B α * colDensC ρ u u' C α
        * colDensC ρ u u' X α
      ∂(Measure.pi fun _ : LayerSite N => μG))
    (Finset.mem_univ A)]
  congr 1
  · -- B = A: split C at A
    rw [← Finset.add_sum_erase Finset.univ
      (fun C => ∑ X : LayerColumn N,
        ∫ α : LayerSite N → G, colDensC ρ u u' A α
          * colDensC ρ u u' A α * colDensC ρ u u' C α
          * colDensC ρ u u' X α
        ∂(Measure.pi fun _ : LayerSite N => μG))
      (Finset.mem_univ A)]
    congr 1
    · exact inner_sum_self ρ μG hN hN3 hρcont u u' A
    · rw [Finset.sum_congr rfl (fun C hC =>
        inner_sum_two_one ρ μG hN hN3 hρcont u u'
          (fun h => (Finset.ne_of_mem_erase hC) h.symm)),
        Finset.sum_const, nsmul_eq_mul, cast_card_erase A]
  · refine Finset.sum_congr rfl fun B hB => ?_
    exact sum_over_C_two_one ρ μG hN hN3 hρcont u u'
      (fun h => (Finset.ne_of_mem_erase hB) h.symm)

/-- **The β⁴ coefficient in closed form plus its
dependent part.** The ordered-tuple expansion of
`(Σ_P dens_P)⁴` evaluates every pattern by the
inner sums; the only non-factorized contribution is
the excess of the primitive quadruples, counted by
the bridge (`24` orderings per 4-set). FENCE: this
is an identity for the finite-volume coefficient,
with `(u, u')`-independence as a corollary of the
pattern values; it asserts no sign. -/
theorem betaCoeff4_total (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    ∫ α : LayerSite N → G, (layerDensSum ρ α u u') ^ 4
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = kappa4Const (N := N) ρ μG
        + 24 * ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ primitiveQuads,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
  classical
  -- value atoms, abstracted for the counting algebra
  set bfac : ℝ := (1 - e1 ρ μG / (d : ℝ)) with hbfac
  set v2 : ℝ := densMomentValue ρ μG 2 * bfac ^ 2 with hv2
  set v31 : ℝ := densMomentValue ρ μG 3 * bfac with hv31
  set v21 : ℝ := v31 + ((densMomentValue ρ μG 2) ^ 2
    + (colCount N - 2) * v2) with hv21
  set cp : ℝ := v2 + (v2 + (v2
    + (colCount N - 3) * bfac ^ 4)) with hcp
  set s0 : ℝ := (densMomentValue ρ μG 4
      + (colCount N - 1) * v31)
    + (colCount N - 1) * v21 with hs0
  -- the pointwise ordered-tuple expansion
  have hpt : ∀ α : LayerSite N → G,
      (layerDensSum ρ α u u') ^ 4
        = ∑ A : LayerColumn N, ∑ B : LayerColumn N,
          ∑ C : LayerColumn N, ∑ X : LayerColumn N,
          colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' C α * colDensC ρ u u' X α := by
    intro α
    rw [layerDensSum_eq_sum_columns ρ hN α u u']
    have e2 : (∑ P : LayerColumn N, colDensC ρ u u' P α) ^ 2
        = ∑ A : LayerColumn N, ∑ B : LayerColumn N,
          colDensC ρ u u' A α * colDensC ρ u u' B α :=
      (pow_two _).trans (Finset.sum_mul_sum _ _ _ _)
    have e4 : (∑ P : LayerColumn N, colDensC ρ u u' P α) ^ 4
        = ∑ A : LayerColumn N, ∑ B : LayerColumn N,
          ∑ C : LayerColumn N, ∑ X : LayerColumn N,
          colDensC ρ u u' A α * colDensC ρ u u' B α
          * colDensC ρ u u' C α * colDensC ρ u u' X α := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, e2,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun A _ =>
        Finset.sum_congr rfl fun C _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun X _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun B _ => ?_
      ring
    exact e4
  -- the (1,1,1,·) values summed over the third index
  have hI111sum : ∀ {A B : LayerColumn N},
      B ∈ Finset.univ.erase A →
      ∑ C ∈ (Finset.univ.erase A).erase B,
        (v2 + (v2 + (v2 + ((colCount N - 3) * bfac ^ 4
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
              (quadReMoment ρ μG {A, B, C, X} u u'
                - (e1 ρ μG) ^ 4)))))
      = (colCount N - 2) * cp
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ (Finset.univ.erase A).erase B,
            ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
              (quadReMoment ρ μG {A, B, C, X} u u'
                - (e1 ρ μG) ^ 4) := by
    intro A B hBmem
    rw [Finset.sum_congr rfl
      (g := fun C : LayerColumn N => cp
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
            (quadReMoment ρ μG {A, B, C, X} u u'
              - (e1 ρ μG) ^ 4))
      (fun C _ => by rw [hcp]; ring),
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      cast_card_erase_two hBmem, ← Finset.mul_sum]
  -- interchange, then the outer splits
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum Finset.univ (fun A _ =>
      integrable_finsetSum Finset.univ (fun B _ =>
      integrable_finsetSum Finset.univ (fun C _ =>
      integrable_finsetSum Finset.univ (fun X _ =>
        integrable_colDensC_prod4 ρ μG hρcont u u' A B C X)))),
    Finset.sum_congr rfl (fun A _ =>
      integral_finsetSum Finset.univ (fun B _ =>
      integrable_finsetSum Finset.univ (fun C _ =>
      integrable_finsetSum Finset.univ (fun X _ =>
        integrable_colDensC_prod4 ρ μG hρcont u u' A B C X)))),
    Finset.sum_congr rfl (fun A _ =>
      Finset.sum_congr rfl (fun B _ =>
      integral_finsetSum Finset.univ (fun C _ =>
      integrable_finsetSum Finset.univ (fun X _ =>
        integrable_colDensC_prod4 ρ μG hρcont u u' A B C X)))),
    Finset.sum_congr rfl (fun A _ =>
      Finset.sum_congr rfl (fun B _ =>
      Finset.sum_congr rfl (fun C _ =>
      integral_finsetSum Finset.univ (fun X _ =>
        integrable_colDensC_prod4 ρ μG hρcont u u' A B C X)))),
    Finset.sum_congr rfl (fun A _ =>
      sum_over_BC ρ μG hN hN3 hρcont u u' A)]
  -- re-abstract the freshly rewritten terms into the value atoms
  rw [← hbfac, ← hv2, ← hv31, ← hv21, ← hs0]
  -- split each B-sum by the (1,1,1,·) evaluation
  have hBig : ∀ {A B : LayerColumn N},
      B ∈ Finset.univ.erase A →
      (v21 + (v21 + ∑ C ∈ (Finset.univ.erase A).erase B,
          (v2 + (v2 + (v2 + ((colCount N - 3) * bfac ^ 4
            + ((d : ℝ)⁻¹) ^ 4
              * ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
                (quadReMoment ρ μG {A, B, C, X} u u'
                  - (e1 ρ μG) ^ 4)))))))
      = (v21 + (v21 + (colCount N - 2) * cp))
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ (Finset.univ.erase A).erase B,
            ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
              (quadReMoment ρ μG {A, B, C, X} u u'
                - (e1 ρ μG) ^ 4) := by
    intro A B hB
    rw [hI111sum hB]
    ring
  rw [Finset.sum_congr rfl
    (g := fun A : LayerColumn N =>
      s0 + ∑ B ∈ Finset.univ.erase A,
        ((v21 + (v21 + (colCount N - 2) * cp))
          + ((d : ℝ)⁻¹) ^ 4
            * ∑ C ∈ (Finset.univ.erase A).erase B,
              ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
                (quadReMoment ρ μG {A, B, C, X} u u'
                  - (e1 ρ μG) ^ 4)))
    (fun A _ => congrArg (fun z => s0 + z)
      (Finset.sum_congr rfl (fun B hB => hBig hB)))]
  -- split the B-sums into constant and excess parts
  have hBsum : ∀ (K : ℝ)
      (E : LayerColumn N → LayerColumn N → ℝ)
      (A : LayerColumn N),
      (∑ B ∈ Finset.univ.erase A,
        (K + ((d : ℝ)⁻¹) ^ 4 * E A B))
      = (colCount N - 1) * K + ((d : ℝ)⁻¹) ^ 4
        * ∑ B ∈ Finset.univ.erase A, E A B := by
    intro K E A
    rw [Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, cast_card_erase A, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun A _ => congrArg
    (fun z => s0 + z)
    (hBsum (v21 + (v21 + (colCount N - 2) * cp))
      (fun A B => ∑ C ∈ (Finset.univ.erase A).erase B,
        ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
          (quadReMoment ρ μG {A, B, C, X} u u'
            - (e1 ρ μG) ^ 4)) A)),
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum]
  -- the excess is the nested quadruple sum: apply the bridge
  have hdep : ∑ A : LayerColumn N, ∑ B ∈ Finset.univ.erase A,
        ∑ C ∈ (Finset.univ.erase A).erase B,
        ∑ X ∈ ((Finset.univ.erase A).erase B).erase C,
          (quadReMoment ρ μG {A, B, C, X} u u'
            - (e1 ρ μG) ^ 4)
      = 24 * ∑ C ∈ primitiveQuads,
          (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
    rw [nested_quadruple_sum_eq
      (fun C => quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
      Finset.univ,
      sum_powersetCard_four_eq_primitive ρ μG hN hN3 hρcont
        u u']
  rw [hdep]
  show (↑(Finset.univ.card) : ℝ)
        * (densMomentValue ρ μG 4 + (colCount N - 1) * v31)
      + (↑(Finset.univ.card) : ℝ) * ((colCount N - 1) * v21)
      + ((↑(Finset.univ.card) : ℝ) * ((colCount N - 1)
          * (v21 + (v21 + (colCount N - 2) * cp)))
        + ((d : ℝ)⁻¹) ^ 4 * (24
          * ∑ C ∈ primitiveQuads,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)))
    = kappa4Const (N := N) ρ μG + 24 * ((d : ℝ)⁻¹) ^ 4
      * ∑ C ∈ primitiveQuads,
        (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4)
  rw [Finset.card_univ, hv21, hv31, hv2, hcp, hbfac]
  unfold kappa4Const colCount
  ring

/-- **The closed form of `κ₄^dep` (the headline):**
`betaCoeff4 = kappa4Const / 24 + d⁻⁴ · Σ_{C ∈
primitiveQuads} (quadReMoment C − e₁⁴)`; equivalently
`kappa4dep` is exactly the displayed sum. The sum
runs over the primitive (private-site-free)
4-subsets of columns. At `5 ≤ N` the next section
identifies those with the plaquette supports. -/
theorem betaCoeff4_closed_plus_dep (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    betaCoeff4 ρ μG u u'
      = kappa4Const (N := N) ρ μG / 24
        + ((d : ℝ)⁻¹) ^ 4
          * ∑ C ∈ primitiveQuads,
            (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
  classical
  unfold betaCoeff4
  rw [integral_congr_ae
    ((Filter.Eventually.of_forall
      (fun α : LayerSite N → G => by ring)) :
      (fun α : LayerSite N → G =>
        (layerDensSum ρ α u u') ^ 4 / 24)
        =ᵐ[Measure.pi fun _ : LayerSite N => μG]
      fun α => (24 : ℝ)⁻¹ * (layerDensSum ρ α u u') ^ 4),
    integral_const_mul,
    betaCoeff4_total ρ μG hN hN3 hρcont u u']
  ring

/-- `κ₄^dep` itself, in closed form. -/
theorem kappa4dep_eq (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    kappa4dep ρ μG u u'
      = ((d : ℝ)⁻¹) ^ 4
        * ∑ C ∈ primitiveQuads,
          (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) := by
  unfold kappa4dep
  rw [betaCoeff4_closed_plus_dep ρ μG hN hN3 hρcont u u']
  ring

/-! ## §11. The sign of `κ₄^dep`: what is proved, and the exact open
    component

**What is proved in this module.**

* The dependent coefficient is exactly the primitive-quad sum
  (`kappa4dep_eq`): every non-primitive 4-column contribution vanishes
  identically at general `(G, ρ)` (`excess_eq_zero_of_not_primitive`),
  because a column with a private site integrates out against the
  single-site mean `e₁`. This is the general form of the probe's
  dep-set criterion.
* At both probed seats — `(C₃, faithful)` and `(S₃, std)`, `N = 2` —
  the probe (module `PlaneCrossingKappa4Probe`, seat computations)
  found the dependent form positive semidefinite on its named
  observable space with margin **exactly zero** on the constant
  direction: face blocks `(3/16)I − (1/16)J` (spectrum
  `{0, 3/16, 3/16}`) and `w wᵀ` respectively, pair blocks positive on
  both nontrivial character directions.

**The exact open component (the sign is NOT decided in general).**
The sign of `κ₄^dep` at general `(G, ρ)` is the sign of the single sum

    `Φ(u, u') := ∑ C ∈ primitiveQuads, (quadReMoment C u u' − e₁⁴)`,

i.e. of the summed plaquette-loop functional over primitive quads.
The scoping's plaquette-telescoping prediction — each primitive quad's
contribution is a sum of squares of plaquette-loop functionals — would
force `Φ ≥ 0` (on the diagonal `u = u'`), and both probe seats conform
with zero margin. But the telescoping evaluation of `quadReMoment C`
at a primitive quad passes through a `ρ ⊗ ρ` projector integral
(Peter–Weyl orthogonality of matrix coefficients of `repMatrix`),
which does **not** exist in the tree; the two seat computations used
seat-specific character tables instead. The sign question for `κ₄^dep`
is therefore reduced, exactly, to the sign of `Φ` above: this brick
lands **PARTIAL** on the sign, with the closed form **FULL**. No
observable space has been widened: every statement here lives on the
probe's named observable space (the layer kernel's own `(u, u')`
arguments), per kill condition K-K4G-2. -/

/-- **Sign reduction (the PARTIAL headline):** the sign of `κ₄^dep` at
general `(G, ρ)` is exactly the sign of the summed primitive-quad loop
functional `Φ` displayed in the section text above — the closed form
`kappa4dep_eq` restated as the sign question's final address. The
component `Φ` is named, not evaluated: its sign is the open component
of this brick. -/
theorem kappa4dep_sign_reduction (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    kappa4dep ρ μG u u'
      = ((d : ℝ)⁻¹) ^ 4
        * ∑ C ∈ primitiveQuads,
          (quadReMoment ρ μG C u u' - (e1 ρ μG) ^ 4) :=
  kappa4dep_eq ρ μG hN hN3 hρcont u u'

end Assembly4

end ThetLogos
