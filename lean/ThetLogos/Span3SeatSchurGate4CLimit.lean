/-
# F2-GATE-4C limit engine

F2-GATE-4C limit engine: the seat pairing is continuous
in its second kernel factor along L²-approximations of
`pullBotKernel`. Analysis infrastructure at the concrete
seat; proves no positivity and no part of
`SeatSchurTarget`. NO CLAIM; dials 0/4.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGate4C

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGate4CLimit

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **GATE-4C limit engine.** The seat pairing against
`pullTopKernel * K₂ n` tends to the seat pairing against
the crossing marginal `planeCrossingMarginal` as `K₂ n`
approximates `pullBotKernel` in `L²` on the product
probability space, for bounded observables `k₁`, `k₂`,
given the target and per-stage pairing integrands
integrable. Difference-of-integrals plus an `L¹`
estimate: the difference integrand is bounded pointwise
by `(C₁ * exp (|β| * layerBoundConst N) * C₂) * ‖D n‖`,
and `∫ ‖D n‖ ≤ (eLpNorm (D n) 2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal`. -/
theorem seatPairing_pullTop_tendsto_of_kernel_approx
    (hN : Even N) (β : ℝ)
    (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ)
    (C₁ C₂ : ℝ)
    (hk₁ : ∀ z, ‖k₁ z‖ ≤ C₁) (hk₂ : ∀ z, ‖k₂ z‖ ≤ C₂)
    (K₂ : ℕ → (↥(posLinks (N := N)) → G) →
      (↥(posLinks (N := N)) → G) → ℂ)
    (hMem : ∀ n, MemLp
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2)
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hTend : Filter.Tendsto
      (fun n => (eLpNorm
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2)
        2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal)
      Filter.atTop (nhds 0))
    (hIntT : Integrable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
          * (starRingEnd ℂ) (k₂ r.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
    (hIntS : ∀ n, Integrable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * K₂ n r.1 r.2 * (starRingEnd ℂ) (k₂ r.2)))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) :
    Filter.Tendsto
      (fun n => seatPairing μG
        (fun z z' => pullTopKernel μG ρ hN β z z' * K₂ n z z')
        k₁ k₂)
      Filter.atTop
      (nhds (seatPairing μG (planeCrossingMarginal μG ρ hN β)
        k₁ k₂)) := by
  -- Nonnegativity of the three constant factors.
  have hC₁ : 0 ≤ C₁ := le_trans (norm_nonneg _) (hk₁ fun _ => 1)
  have hC₂ : 0 ≤ C₂ := le_trans (norm_nonneg _) (hk₂ fun _ => 1)
  have hBnn : 0 ≤ Real.exp (|β| * layerBoundConst N) :=
    (Real.exp_pos _).le
  -- The difference kernel is integrable (MemLp 2 → MemLp 1).
  have hDint : ∀ n, Integrable
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2) ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
    fun n => MemLp.integrable (le_refl (1 : ℝ≥0∞))
      ((hMem n).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  -- Pointwise: the difference integrand `J n` is the target
  -- integrand minus the stage integrand.
  have hJeq : ∀ (n : ℕ)
      (r : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G)),
      k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2))
        = k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) (k₂ r.2))
          - k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * K₂ n r.1 r.2 * (starRingEnd ℂ) (k₂ r.2)) := by
    intro n r
    rw [planeCrossingMarginal_eq_pull_mul]
    ring
  have hJfun : ∀ n,
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2)))
      = (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) (k₂ r.2))
          - k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * K₂ n r.1 r.2 * (starRingEnd ℂ) (k₂ r.2))) :=
    fun n => funext fun r => hJeq n r
  have hJint : ∀ n, Integrable
      (fun r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2))) ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    intro n
    rw [hJfun n]
    exact hIntT.sub (hIntS n)
  -- `∫ J n` is the target pairing minus the stage pairing.
  have hIntJ : ∀ n,
      (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = seatPairing μG (planeCrossingMarginal μG ρ hN β) k₁ k₂
        - seatPairing μG
          (fun z z' => pullTopKernel μG ρ hN β z z' * K₂ n z z')
          k₁ k₂ := by
    intro n
    have h1 : (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      - (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * K₂ n r.1 r.2 * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) := by
      rw [hJfun n, integral_sub hIntT (hIntS n)]
    have h2 : (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = seatPairing μG (planeCrossingMarginal μG ρ hN β)
        k₁ k₂ := rfl
    have h3 : (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * K₂ n r.1 r.2 * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = seatPairing μG
          (fun z z' => pullTopKernel μG ρ hN β z z' * K₂ n z z')
          k₁ k₂ := rfl
    rw [h1, h2, h3]
  -- Pointwise bound `‖J n r‖ ≤ (C₁ * B * C₂) * ‖D n r‖`.
  have hJbound : ∀ (n : ℕ)
      (r : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G)),
      ‖k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2))‖
        ≤ (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
          * ‖pullBotKernel μG ρ hN β r.1 r.2
            - K₂ n r.1 r.2‖ := by
    intro n r
    have hstar : ‖(starRingEnd ℂ) (k₂ r.2)‖ = ‖k₂ r.2‖ := by
      simp
    have htop : ‖pullTopKernel μG ρ hN β r.1 r.2‖
        ≤ Real.exp (|β| * layerBoundConst N) :=
      layerKernel_norm_le μG ρ β (tauTop hN r.1) (tauTop hN r.2)
    calc ‖k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
            * (starRingEnd ℂ) (k₂ r.2))‖
        = ‖k₁ r.1‖ * ((‖pullTopKernel μG ρ hN β r.1 r.2‖
            * ‖pullBotKernel μG ρ hN β r.1 r.2
              - K₂ n r.1 r.2‖) * ‖k₂ r.2‖) := by
          simp only [norm_mul, hstar]
      _ ≤ C₁ * ((Real.exp (|β| * layerBoundConst N)
            * ‖pullBotKernel μG ρ hN β r.1 r.2
              - K₂ n r.1 r.2‖) * C₂) := by
          apply mul_le_mul (hk₁ r.1) _ _ hC₁
          · exact mul_le_mul
              (mul_le_mul_of_nonneg_right htop (norm_nonneg _))
              (hk₂ r.2) (norm_nonneg _)
              (mul_nonneg hBnn (norm_nonneg _))
          · positivity
      _ = (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
            * ‖pullBotKernel μG ρ hN β r.1 r.2
              - K₂ n r.1 r.2‖ := by ring
  -- `∫ ‖D n‖ ≤ (eLpNorm (D n) 2 μprod).toReal`.
  have hL1 : ∀ n,
      (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        ‖pullBotKernel μG ρ hN β r.1 r.2
          - K₂ n r.1 r.2‖ ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      ≤ (eLpNorm
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2)
        2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal := by
    intro n
    have hsm : AEStronglyMeasurable
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2) ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
      (hMem n).aestronglyMeasurable
    have h1 : (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        ‖pullBotKernel μG ρ hN β r.1 r.2
          - K₂ n r.1 r.2‖ ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      = (eLpNorm
        (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2)
        1 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal := by
      rw [integral_norm_eq_lintegral_enorm hsm,
        ← eLpNorm_one_eq_lintegral_enorm hsm]
    rw [h1]
    exact ENNReal.toReal_mono (hMem n).eLpNorm_lt_top.ne
      (eLpNorm_le_eLpNorm_of_exponent_le
        (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  -- The master bound on `‖∫ J n‖`.
  have hNormInt : ∀ n,
      ‖∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))‖
      ≤ (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
        * (eLpNorm
          (fun p : (↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G) =>
            pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2)
          2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal := by
    intro n
    calc ‖∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
            * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))‖
        ≤ ∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          ‖k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
            * (starRingEnd ℂ) (k₂ r.2))‖ ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
            * ‖pullBotKernel μG ρ hN β r.1 r.2
              - K₂ n r.1 r.2‖ ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
          integral_mono_ae (hJint n).norm
            ((hDint n).norm.const_mul _)
            (ae_of_all _ fun r => hJbound n r)
      _ = (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
            * ∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          ‖pullBotKernel μG ρ hN β r.1 r.2
            - K₂ n r.1 r.2‖ ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
          integral_const_mul _ _
      _ ≤ (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
            * (eLpNorm
              (fun p : (↥(posLinks (N := N)) → G)
                  × (↥(posLinks (N := N)) → G) =>
                pullBotKernel μG ρ hN β p.1 p.2 - K₂ n p.1 p.2)
              2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal :=
          mul_le_mul_of_nonneg_left (hL1 n)
            (mul_nonneg (mul_nonneg hC₁ hBnn) hC₂)
  -- Squeeze: `∫ J n → 0`.
  have hTend0 : Filter.Tendsto
      (fun n => ∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hNormInt ?_
    simpa using hTend.const_mul
      (C₁ * Real.exp (|β| * layerBoundConst N) * C₂)
  -- Stage pairings are the target pairing minus `∫ J n`.
  have hEq : ∀ n, seatPairing μG
        (fun z z' => pullTopKernel μG ρ hN β z z' * K₂ n z z')
        k₁ k₂
      = seatPairing μG (planeCrossingMarginal μG ρ hN β) k₁ k₂
        - ∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
          * (pullBotKernel μG ρ hN β r.1 r.2 - K₂ n r.1 r.2)
          * (starRingEnd ℂ) (k₂ r.2)) ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
    intro n
    rw [hIntJ n]
    abel
  refine Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun n => (hEq n).symm) ?_
  simpa using tendsto_const_nhds.sub hTend0

end Span3SeatSchurGate4CLimit

end ThetLogos
