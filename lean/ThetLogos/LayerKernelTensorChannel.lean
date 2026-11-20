/-
# WP2 character route, Module A, brick A2b — the site average
is the averaging operator; the channel decomposition

A1's site average `tensorAvg` (the counting-measure average of
a tensor entry over the finite group) is identified with T2's
averaging operator (`AveragingProjection.averagingOperator`)
at the normalized Haar probability measure `haarProb G`,
applied to A2a's tensor representation.  The bridge is the
finite-group identity `∫ g, f g ∂(haarProb G) = (card G)⁻¹ •
∑ g, f g`, proved from `integral_fintype` and the equality of
all `haarProb` singletons.  Transporting
`AveragingProjection.averagingOperator_gram` through the
identification gives the **channel decomposition** of the
average: `tensorAvg σ A B = ∑ i, star (f i A) * f i B` over
finitely many channels `f i` — the separated-squares (Gram)
form the assembly (B2) consumes.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of this
line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelTensorAverage

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal InnerProductSpace

namespace ThetLogos

section TensorChannel

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [TopologicalSpace G] [DiscreteTopology G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
variable [CompactSpace G] [LocallyCompactSpace G]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {n : κ → ℕ}
  (σ : ∀ j, G →* ↥(Matrix.unitaryGroup (Fin (n j)) ℂ))

/-- All `haarProb` singletons of a finite group have the same
mass `(card G)⁻¹` (as a real number): left invariance makes
them all equal, and they sum to `1`. -/
theorem haarProb_real_singleton (g : G) :
    (haarProb G).real {g} = (Fintype.card G : ℝ)⁻¹ := by
  have hEq : ∀ x : G, haarProb G {x} = haarProb G {1} := by
    intro x
    have hmap := Measure.IsMulLeftInvariant.map_mul_left_eq_self
      (μ := haarProb G) x
    have h2 : (Measure.map (fun y => x * y) (haarProb G)) {x}
        = haarProb G {1} := by
      rw [Measure.map_apply (measurable_const_mul x)
        (measurableSet_singleton x)]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        exact mul_left_cancel (a := x) (by rw [h, mul_one])
      · intro h
        rw [h, mul_one]
    rw [hmap] at h2
    exact h2
  have hsum : ∑ x : G, haarProb G {x} = 1 := by
    have h3 : (Set.univ : Set G) = ⋃ x ∈ (Finset.univ : Finset G), {x} := by
      ext y
      simp
    rw [← measure_univ (μ := haarProb G), h3,
      measure_biUnion_finset (fun x _ y _ hxy =>
        Set.disjoint_singleton.mpr hxy)
        (fun x _ => measurableSet_singleton x)]
  have hcard : (Fintype.card G : ℝ≥0∞) * haarProb G {1} = 1 := by
    have h4 : ∑ x : G, haarProb G {x}
        = (Fintype.card G : ℝ≥0∞) * haarProb G {1} := by
      calc ∑ x : G, haarProb G {x} = ∑ _x : G, haarProb G {1} :=
            Finset.sum_congr rfl fun x _ => hEq x
        _ = (Fintype.card G : ℝ≥0∞) * haarProb G {1} := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [hsum] at h4
    exact h4.symm
  have h1 : haarProb G {1} = (Fintype.card G : ℝ≥0∞)⁻¹ := by
    have hne : (Fintype.card G : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have htop : (Fintype.card G : ℝ≥0∞) ≠ ∞ :=
      ENNReal.natCast_ne_top _
    calc haarProb G {1}
        = (Fintype.card G : ℝ≥0∞)⁻¹
            * ((Fintype.card G : ℝ≥0∞) * haarProb G {1}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]
      _ = (Fintype.card G : ℝ≥0∞)⁻¹ * 1 := by rw [hcard]
      _ = (Fintype.card G : ℝ≥0∞)⁻¹ := mul_one _
  rw [measureReal_def, hEq g, h1, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **The finite bridge.** The Haar integral of a tensor
entry over the finite group is A1's counting-measure site
average. -/
theorem integral_tensorEntry_haarProb (A B : ∀ j, Fin (n j)) :
    ∫ g, tensorEntry σ g A B ∂(haarProb G) = tensorAvg σ A B := by
  rw [integral_fintype Integrable.of_finite, tensorAvg]
  calc ∑ g, (haarProb G).real {g} • tensorEntry σ g A B
      = ∑ _g : G, ((Fintype.card G : ℝ)⁻¹) • tensorEntry σ _g A B :=
        Finset.sum_congr rfl fun g _ => by rw [haarProb_real_singleton]
    _ = ((Fintype.card G : ℝ)⁻¹) • ∑ g, tensorEntry σ g A B :=
        (Finset.smul_sum).symm
    _ = ((Fintype.card G : ℂ))⁻¹ * ∑ g, tensorEntry σ g A B := by
        rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- **The identification.** A1's site average is the
`(A, B)` matrix coefficient of T2's averaging operator for
the tensor representation, at `haarProb G`. -/
theorem tensorAvg_eq_averagingOperator (A B : ∀ j, Fin (n j)) :
    tensorAvg σ A B
      = ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A,
          AveragingProjection.averagingOperator (haarProb G) (tensorRepCLM σ)
            (tensorRepCLM_continuous σ) (tensorRepCLM_unitary σ)
            ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B)⟫_ℂ := by
  haveI : CompleteSpace (EuclideanSpace ℂ (∀ j, Fin (n j))) :=
    FiniteDimensional.complete ℂ _
  rw [← integral_tensorEntry_haarProb σ A B,
    AveragingProjection.averagingOperator_apply]
  show (∫ g, tensorEntry σ g A B ∂(haarProb G))
      = (innerSL ℂ ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A))
          (∫ g, tensorRepCLM σ g
            ((EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) B) ∂(haarProb G))
  rw [← ContinuousLinearMap.integral_comp_comm _
    (AveragingProjection.integrable_apply _ _
      (tensorRepCLM_continuous σ) _)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
    (tensorRepCLM_inner_basis σ g A B).symm)

/-- **The channel decomposition of the site average.**
There are finitely many channels `f i` (the coefficients of
an orthonormal basis of the invariant subspace, transported
through the identification) with
`tensorAvg σ A B = ∑ i, star (f i A) * f i B` — the
separated-squares form of the average. -/
theorem tensorAvg_channel_form :
    ∃ (m : ℕ) (f : Fin m → (∀ j, Fin (n j)) → ℂ),
      ∀ A B, tensorAvg σ A B = ∑ i, star (f i A) * f i B := by
  have hmul : ∀ g h (v : EuclideanSpace ℂ (∀ j, Fin (n j))),
      tensorRepCLM σ (g * h) v = tensorRepCLM σ g (tensorRepCLM σ h v) := by
    intro g h v
    rw [tensorRepCLM_mul]
    exact ContinuousLinearMap.mul_apply _ _ _
  have hone : ∀ v : EuclideanSpace ℂ (∀ j, Fin (n j)),
      tensorRepCLM σ 1 v = v := by
    intro v
    rw [tensorRepCLM_one]
    exact ContinuousLinearMap.one_apply v
  obtain ⟨m, e, he⟩ := AveragingProjection.averagingOperator_gram
    (haarProb G) (tensorRepCLM σ) (tensorRepCLM_continuous σ)
    hmul hone (tensorRepCLM_unitary σ)
  refine ⟨m, fun i X => ⟪(e i : EuclideanSpace ℂ (∀ j, Fin (n j))),
    (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) X⟫_ℂ, fun A B => ?_⟩
  rw [tensorAvg_eq_averagingOperator, he, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsymm : ⟪(EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A,
        (e i : EuclideanSpace ℂ (∀ j, Fin (n j)))⟫_ℂ
      = star ⟪(e i : EuclideanSpace ℂ (∀ j, Fin (n j))),
          (EuclideanSpace.basisFun (∀ j, Fin (n j)) ℂ) A⟫_ℂ := by
    rw [← inner_conj_symm, starRingEnd_apply]
  rw [inner_smul_right, hsymm, mul_comm]

/-- The site average is conjugate-symmetric in its two
indices — read off the channel decomposition. -/
theorem tensorAvg_conj_symm (A B : ∀ j, Fin (n j)) :
    star (tensorAvg σ A B) = tensorAvg σ B A := by
  obtain ⟨m, f, hf⟩ := tensorAvg_channel_form σ
  rw [hf A B, hf B A, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul, star_star]

end TensorChannel

end ThetLogos
