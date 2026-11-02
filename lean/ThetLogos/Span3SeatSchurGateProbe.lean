/-
# F2-GATE-3 FALSITY PROBE — the β = 0 fence (weld line)

Brick: the in-tree fence of the GATE-3 falsity probe
(Jeff's decision, 2026-11-02 00:49 EST: fire the falsity
probe on GATE-3). Companion: probe dossier
`whitepaper/gate3-probe-landing-2026-11-02.md` and the
finite-seat probe BR1-031 (script
`routeb-general-scratch/f2gate3-probe.py`).

**Target (pinned verbatim, GATE-0 item 5, in
`Span3SeatSchurGatePost`):**
`pullBotKernel_seatFactorApproxExpansion` — at every
`Even N`, every `β ≥ 0`, under `LayerKernelPos`, the
bottom pullback kernel admits the approximating Gram
expansion `SeatFactorApproxExpansion` of item 1.

**What this module proves — and all it proves:** the
expansion EXISTS unconditionally at `β = 0`, at every
seat `(G, μG, ρ, N)`: at `β = 0` the layer action
vanishes identically, so `layerKernel = 1` and
`pullBotKernel = 1`, and the constant Gram family
(`ι = PUnit`, `c = 1`, `φ = 1`) is an exact expansion
(difference kernel identically zero). Consequence for
the probe, on the face: **K-GATE-3 cannot fire at
`β = 0`, and no counterexample seat for item 5 lives at
`β = 0`** — the hypothesis `LayerKernelPos` is not even
needed there. The probe's search space is `β > 0`; this
module asserts NOTHING about any `β > 0`, nothing about
`LayerKernelPos`, nothing about `𝒜 ⪰ 0`.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4. Even a
completed gate + W3 would prove neither FACT nor
clause (a); this fence proves strictly less: one
degenerate seat of one gate item is expansion-positive.
-/

import ThetLogos.Span3SeatSchurGatePost

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateProbe

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The layer kernel at `β = 0` is the constant `1`:**
the one-layer action carries the prefactor `β`, so at
`β = 0` every Boltzmann factor is `exp 0 = 1` and the
stratum average of `1` over a probability measure is
`1`. -/
theorem layerKernel_zero (u u' : LayerLink N → G) :
    layerKernel μG ρ 0 u u' = 1 := by
  unfold layerKernel layerAction
  simp

/-- **The bottom pullback kernel at `β = 0` is the
constant `1`** (its slots are two evaluations of the
layer kernel). -/
theorem pullBotKernel_zero (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    pullBotKernel μG ρ hN 0 z z' = 1 :=
  layerKernel_zero μG ρ _ _

/-- **The β = 0 fence:** the approximating expansion of
GATE-0 item 1 EXISTS at `β = 0`, unconditionally — the
constant Gram family (`ι n = PUnit`, `c = 1`, `φ = 1`)
reproduces `pullBotKernel = 1` exactly, so the
difference kernel is identically zero, its `MemLp 2`
condition is trivial, and its HS norm is the constant
sequence `0`. Hence GATE-0 item 5
(`pullBotKernel_seatFactorApproxExpansion`) holds at
`β = 0` at every seat with NO `LayerKernelPos`
hypothesis, and the falsity probe for K-GATE-3 has no
counterexample seat at `β = 0`. -/
theorem seatFactorApproxExpansion_zero (hN : Even N) :
    SeatFactorApproxExpansion μG ρ hN 0 := by
  have hdiff : ∀ (n : ℕ)
      (p : (↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G)),
      pullBotKernel μG ρ hN 0 p.1 p.2
        - ∑ _i : PUnit, (1 : ℂ)
            * ((1 : (LayerLink N → G) → ℂ) (tauBot hN p.1)
              * (starRingEnd ℂ)
                ((1 : (LayerLink N → G) → ℂ) (tauBot hN p.2)))
        = 0 := by
    intro n p
    simp [pullBotKernel_zero μG ρ hN]
  refine ⟨fun _ => PUnit, fun _ => inferInstance, fun _ _ => 1,
    fun _ _ => 1, fun _ _ => zero_le_one, ?_, ?_⟩
  · intro n
    have hfun : (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN 0 p.1 p.2
          - ∑ i : PUnit, ((fun _ _ => (1 : ℝ)) n i : ℂ)
              * (((fun _ _ => (1 : (LayerLink N → G) → ℂ)) n i)
                  (tauBot hN p.1)
                * (starRingEnd ℂ)
                  (((fun _ _ => (1 : (LayerLink N → G) → ℂ)) n i)
                    (tauBot hN p.2))))
        = fun _ => 0 := by
      funext p
      exact hdiff n p
    rw [hfun]
    exact memLp_const 0
  · refine Filter.Tendsto.congr (fun n => ?_) tendsto_const_nhds
    show (0 : ℝ) = (eLpNorm
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN 0 p.1 p.2
          - ∑ _i : PUnit, (1 : ℂ)
              * ((1 : (LayerLink N → G) → ℂ) (tauBot hN p.1)
                * (starRingEnd ℂ)
                  ((1 : (LayerLink N → G) → ℂ) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal
    rw [eLpNorm_congr_ae
      (Filter.Eventually.of_forall (fun p => hdiff n p))]
    simp

end Span3SeatSchurGateProbe

end ThetLogos
