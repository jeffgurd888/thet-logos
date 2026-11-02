/-
# F2-GATE-4C discharge: the conditional limit passage, proved

F2-GATE-4C discharge: the conditional limit passage, proved. This
proves the GATE-4C conditional ONLY — GATE-0's item 6 stands
unproved as frozen (K-GATE-4C-2); `seatSchurProductStepOpen`,
GATE-3/item 5, and the pairings' discharge remain open.
NO CLAIM; dials 0/4.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGate4CLimit
import ThetLogos.LatticeGramAssembly

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGate4CProof

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

theorem seatSchurTarget_of_approxProductStep_gate4c_proved :
    seatSchurTarget_of_approxProductStep_gate4c (N := N) μG ρ := by
  intro hN hN4 β hd ι hfin c φ hc hMem hTend hIntStage hIntLim hPair
  letI : ∀ n, Fintype (ι n) := hfin
  intro _hβ _hLKP f hf hfbdd
  obtain ⟨C, hC⟩ := hfbdd
  -- The pair lemma: one limit passage per observable pair.
  have hpair : ∀ (k₁ k₂ : (↥(posLinks (N := N)) → G) → ℂ) (C₁ C₂ : ℝ),
      (∀ z, ‖k₁ z‖ ≤ C₁) → (∀ z, ‖k₂ z‖ ≤ C₂) →
      (∀ n i, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (k₁ r.1 * (φ n i) (tauBot hN r.1))
            * (pullTopKernel μG ρ hN β r.1 r.2
              * (starRingEnd ℂ) (k₂ r.2 * (φ n i) (tauBot hN r.2))))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))) →
      (∀ n i, 0 ≤ (seatPairing μG (pullTopKernel μG ρ hN β)
          (fun z => k₁ z * (φ n i) (tauBot hN z))
          (fun z => k₂ z * (φ n i) (tauBot hN z))).re) →
      Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          k₁ r.1 * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) (k₂ r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) →
      0 ≤ (seatPairing μG (planeCrossingMarginal μG ρ hN β) k₁ k₂).re := by
    intro k₁ k₂ C₁ C₂ hk₁ hk₂ hI hT hIT
    -- (a) Stage nonnegativity, via the finite-rank core.
    have hStage : ∀ n, 0 ≤ (seatPairing μG
        (fun z z' => pullTopKernel μG ρ hN β z z'
          * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN z)
              * (starRingEnd ℂ) ((φ n i) (tauBot hN z')))))
        k₁ k₂).re := by
      intro n
      exact seatPairing_mul_nonneg_of_finiteRank μG
        (pullTopKernel μG ρ hN β)
        (fun z z' => ∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN z)
          * (starRingEnd ℂ) ((φ n i) (tauBot hN z'))))
        k₁ k₂ (c n) (hc n)
        (fun i z => (φ n i) (tauBot hN z))
        (fun i z => (φ n i) (tauBot hN z))
        (fun z z' => rfl) (hI n) (hT n)
    -- (b) Stage integrability, via the pointwise sum identity.
    have hStageInt : ∀ n, Integrable
        (fun r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
            * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN r.1)
                * (starRingEnd ℂ) ((φ n i) (tauBot hN r.2))))
            * (starRingEnd ℂ) (k₂ r.2)))
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
      intro n
      have hpt : ∀ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
              * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN r.1)
                  * (starRingEnd ℂ) ((φ n i) (tauBot hN r.2))))
              * (starRingEnd ℂ) (k₂ r.2))
            = ∑ i, (c n i : ℂ) * ((k₁ r.1 * (φ n i) (tauBot hN r.1))
                * (pullTopKernel μG ρ hN β r.1 r.2
                  * (starRingEnd ℂ) (k₂ r.2
                    * (φ n i) (tauBot hN r.2)))) := by
        intro r
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      rw [show (fun r : (↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G) =>
            k₁ r.1 * (pullTopKernel μG ρ hN β r.1 r.2
              * (∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN r.1)
                  * (starRingEnd ℂ) ((φ n i) (tauBot hN r.2))))
              * (starRingEnd ℂ) (k₂ r.2)))
          = (fun r : (↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G) =>
            ∑ i, (c n i : ℂ) * ((k₁ r.1 * (φ n i) (tauBot hN r.1))
                * (pullTopKernel μG ρ hN β r.1 r.2
                  * (starRingEnd ℂ) (k₂ r.2
                    * (φ n i) (tauBot hN r.2))))) from funext hpt]
      exact integrable_finsetSum Finset.univ
        (fun i _ => (hI n i).const_mul _)
    -- (c) The limit passage, then closedness of `Ici 0`.
    have hLim := seatPairing_pullTop_tendsto_of_kernel_approx μG ρ hN β
      k₁ k₂ C₁ C₂ hk₁ hk₂
      (fun n z z' => ∑ i, (c n i : ℂ) * ((φ n i) (tauBot hN z)
        * (starRingEnd ℂ) ((φ n i) (tauBot hN z'))))
      hMem hTend hIT hStageInt
    have hLimRe := (Complex.continuous_re.tendsto _).comp hLim
    exact isClosed_Ici.mem_of_tendsto hLimRe
      (Filter.Eventually.of_forall hStage)
  -- The half-action weight bound, for the folded pair.
  have hW : ∀ z : ↥(posLinks (N := N)) → G,
      ‖((Real.exp (-(halfActionP ρ β z)) : ℂ))‖
        ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr
      ((neg_le_abs _).trans (GramAssemblyWord.abs_halfActionP_le ρ hd β z))
  -- Pair (marginal): the target's second conjunct.
  have hmarg := hpair (posGaugeAvg μG f) (mirrorGaugeAvg μG f) C C
    (fun z => norm_posGaugeAvg_le μG C f hC z)
    (fun z => norm_mirrorGaugeAvg_le μG C f hC z)
    (fun n i => (hIntStage f hf ⟨C, hC⟩ n i).1)
    (fun n i => (hPair f (φ n i) hf ⟨C, hC⟩).1)
    (hIntLim f hf ⟨C, hC⟩).1
  -- Pair (folded): the target's first conjunct, through the fold.
  have hfold := hpair
    (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
      * (posGaugeAvg μG f) z)
    (fun z => (Real.exp (-(halfActionP ρ β z)) : ℂ)
      * (mirrorGaugeAvg μG f) z)
    (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) * C)
    (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) * C)
    (fun z => (norm_mul_le _ _).trans (mul_le_mul (hW z)
      (norm_posGaugeAvg_le μG C f hC z) (norm_nonneg _)
      (Real.exp_pos _).le))
    (fun z => (norm_mul_le _ _).trans (mul_le_mul (hW z)
      (norm_mirrorGaugeAvg_le μG C f hC z) (norm_nonneg _)
      (Real.exp_pos _).le))
    (fun n i => (hIntStage f hf ⟨C, hC⟩ n i).2)
    (fun n i => (hPair f (φ n i) hf ⟨C, hC⟩).2)
    (hIntLim f hf ⟨C, hC⟩).2
  constructor
  · rw [planeAvgPairing_eq_seatPairing_marginal_fold μG ρ hN β
      (posGaugeAvg μG f) (mirrorGaugeAvg μG f)]
    exact hfold
  · exact hmarg

end Span3SeatSchurGate4CProof

end ThetLogos
