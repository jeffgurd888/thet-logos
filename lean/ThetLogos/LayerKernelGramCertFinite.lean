/-
# Brick (ii), Module 2 — the d ≥ 2 assembly at finite (G, ρ):
# finite-sum form, contracted form, and the named gap

Brick (ii) of the Q3 closable set (item 6;
`q3-closable-scope-2026-11-08.md` §2).  Target: (PIN-F) at
every finite `(G, ρ)`, even `N`, all `β ≥ 0`, hence
`LayerKernelPos` at every finite seat via the G-0 discharge
(`LayerKernelSOSCert.layerKernelPos`, cited, not reproved).

**State of this module: PARTIAL, at full rank.**  What is
proved here, unconditionally and at full generality:

* the finite-sum form of the layer kernel (the Haar integral
  over the stratum is the uniform finite average);
* the contracted form: the kernel is the counting factor
  times the sum over stratum configurations `α` and column
  types `t` of the assembled δ-coefficient weight times the
  product of column δ-coefficients of the column words
  (Module 1's coefficient system);
* the conditional discharge: IF the contracted sum admits
  the Gram factorization of `DeltaGramGap` below, THEN the
  G-0 certificate with the δ-data exists and
  `LayerKernelPos` follows at every finite seat, even `N`,
  all `β ≥ 0`.

What is NOT proved: `DeltaGramGap` itself.  The lane's
obstruction analysis (STATUS.md, full rank): the δ-basis
separation fails patternwise — for fixed `(α, t)` the
contracted kernel `C(u) • δ(u', W(u))` of Module 1's word
contraction is not Hermitian, so no feature family at that
pattern Gram-factorizes it; the character route needs
(1) `exp (-β • gramDens)` as a finite nonnegative combination
of characters of finite-dimensional unitary representations
(tensor-power series + irreducible decomposition — the
pinned Mathlib's character theory stops at orthogonality)
and (2) the cyclic tensor-network contraction splitting at
the `averageMap` site projections.  Those two steps are the
priced L core of the brick.  **K-GRAM-SECTOR and
K-GRAM-DEGEN do not fire**: no negative coefficient and no
certificate-breaking degeneracy was found at any finite
`(G, ρ)`; the gap is a proof gap, not a counterexample.
Fences kept: even `N` only; no FACT-shaped routing anywhere
(no field or proof mentions `StratumColumnFactorization`,
`zPolymer`, or `LayerKernelPos` as an input).

NO CLAIM; dials 0/4.  Rung R1 stays OPEN at `d ≥ 2`.
-/

import ThetLogos.LayerKernelContractionAPI
import ThetLogos.LayerKernelGramCertOneDim

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

section FiniteAssembly

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- The δ-basis column coefficient: the one-column Boltzmann
factor itself, `exp (-β • dens_ρ t) > 0` for every `β`. -/
noncomputable def deltaCoeff (β : ℝ) (t : G) : ℝ :=
  Real.exp (-β * gramDens ρ t)

theorem deltaCoeff_pos (β : ℝ) (t : G) : 0 < deltaCoeff ρ β t :=
  Real.exp_pos _

theorem deltaCoeff_nonneg (β : ℝ) (t : G) : 0 ≤ deltaCoeff ρ β t :=
  (deltaCoeff_pos ρ β t).le

/-- The one-column δ-expansion: the Boltzmann factor is the
sum of its values against the δ-basis (Module 1, 1a). -/
theorem delta_expansion (β : ℝ) (g : G) :
    ((Real.exp (-β * gramDens ρ g) : ℝ) : ℂ)
      = ∑ t, ((deltaCoeff ρ β t : ℝ) : ℂ) * deltaFn t g :=
  (sum_deltaFn_mul (fun t => ((deltaCoeff ρ β t : ℝ) : ℂ)) g).symm

/-- **Finite-sum form of the layer kernel** (even `N`): the
Haar integral over the stratum is the uniform average over
finitely many stratum configurations, of the product over
columns of the one-column Boltzmann factors. -/
theorem layerKernel_eq_card_inv_sum (hN : Even N) (β : ℝ)
    (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G, ∏ P : LayerColumn N,
          ((Real.exp (-β * gramDens ρ (colWordOf u u' P α)) : ℝ) : ℂ) := by
  classical
  have hreal : ∀ α : LayerSite N → G, -(layerAction ρ β α u u')
      = ∑ P : LayerColumn N, (-β * gramDens ρ
          (colWordOf u u' P α)) := by
    intro α
    rw [layerAction_eq, layerDensSum_eq_sum_columns ρ hN,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hcd : colDensC ρ u u' P α
        = gramDens ρ (colWordOf u u' P α) := rfl
    rw [hcd, neg_mul]
  have hcol : ∀ α : LayerSite N → G,
      ((Real.exp (-(layerAction ρ β α u u')) : ℝ) : ℂ)
        = ∏ P : LayerColumn N, ((Real.exp (-β * gramDens ρ
            (colWordOf u u' P α)) : ℝ) : ℂ) := by
    intro α
    rw [hreal α, Real.exp_sum, Complex.ofReal_prod]
  have step1 : layerKernel μG ρ β u u'
      = ∫ α : LayerSite N → G, ∏ P : LayerColumn N,
          ((Real.exp (-β * gramDens ρ (colWordOf u u' P α)) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
    unfold layerKernel
    exact integral_congr_ae (Filter.Eventually.of_forall hcol)
  rw [step1, integral_pi_eq_card_inv_sum μG]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- **Contracted form of the layer kernel** (even `N`): the
counting factor times the sum over stratum configurations
and column types of the assembled coefficient weight times
the product of the column δ-coefficients — Module 1's
coefficient system, assembled. -/
theorem layerKernel_eq_contracted (hN : Even N) (β : ℝ)
    (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G, ∑ t : LayerColumn N → G,
          (∏ P : LayerColumn N, ((deltaCoeff ρ β (t P) : ℝ) : ℂ))
            * ∏ P : LayerColumn N,
              deltaFn (t P) (colWordOf u u' P α) := by
  rw [layerKernel_eq_card_inv_sum μG ρ hN β u u']
  refine congrArg _ (Finset.sum_congr rfl fun α _ => ?_)
  have hcol : ∀ P : LayerColumn N,
      ((Real.exp (-β * gramDens ρ (colWordOf u u' P α)) : ℝ) : ℂ)
        = ∑ s : G, ((deltaCoeff ρ β s : ℝ) : ℂ)
            * deltaFn s (colWordOf u u' P α) :=
    fun P => delta_expansion ρ β _
  rw [Finset.prod_congr rfl (fun P _ => hcol P)]
  rw [Fintype.prod_sum (fun (P : LayerColumn N) (s : G) =>
    ((deltaCoeff ρ β s : ℝ) : ℂ) * deltaFn s (colWordOf u u' P α))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.prod_mul_distrib]

/-- **The named gap.**  The Gram factorization of the
contracted sum, over the joint index `j = (α, t)`, with the
assembled weights `gramColWeight` of the δ-coefficients.
This is exactly the `kernel_eq` field of the δ-certificate;
everything else in the certificate is proved in this
module. -/
def DeltaGramGap (β : ℝ) : Prop :=
  ∃ feat : ((LayerSite N → G) × (LayerColumn N → G))
      → (LayerLink N → G) → ℂ,
    ∀ u u' : LayerLink N → G,
      ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
          * ∑ α : LayerSite N → G, ∑ t : LayerColumn N → G,
            (∏ P : LayerColumn N, ((deltaCoeff ρ β (t P) : ℝ) : ℂ))
              * ∏ P : LayerColumn N,
                deltaFn (t P) (colWordOf u u' P α)
        = ∑ j, ((gramColWeight (deltaCoeff ρ β)
              (fun j : (LayerSite N → G) × (LayerColumn N → G) =>
                j.2) j : ℝ) : ℂ)
            * feat j u * star (feat j u')

/-- **The δ-certificate, conditional on the gap.**  All
fields are the δ-data of Module 1; `kernel_eq` is the
contracted form closed by the gap. -/
noncomputable def gramDeltaCert (hN : Even N) (β : ℝ)
    (hgap : DeltaGramGap (ρ := ρ) (N := N) β) :
    LayerKernelSOSCert (N := N) (τ := G)
      (ι := (LayerSite N → G) × (LayerColumn N → G)) μG ρ β where
  coeff := deltaCoeff ρ β
  coeff_nonneg := fun t => deltaCoeff_nonneg ρ β t
  char := fun t g => deltaFn t g
  expansion := fun g => delta_expansion ρ β g
  τof := fun j P => j.2 P
  feat := Classical.choose hgap
  pairScale := ((Fintype.card (LayerLink N → G) : ℝ)⁻¹)
    * ((Fintype.card (LayerLink N → G) : ℝ)⁻¹)
  pairScale_nonneg := mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  pairing_eq := by
    intro F
    have step1 : ∀ u : LayerLink N → G,
        ∫ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
            ∂(Measure.pi fun _ : LayerLink N => μG)
          = ((Fintype.card (LayerLink N → G) : ℝ)⁻¹)
            • ∑ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u'
              * F u' :=
      fun u => integral_pi_eq_card_inv_sum μG _
    rw [integral_congr_ae (Filter.Eventually.of_forall step1),
      integral_pi_eq_card_inv_sum μG, ← Finset.smul_sum, smul_smul,
      Complex.real_smul]
  kernel_eq := by
    intro u u'
    rw [layerKernel_eq_contracted μG ρ hN β u u']
    exact Classical.choose_spec hgap u u'

/-- **Conditional headline.**  If the gap closes, then
`LayerKernelPos` holds at every finite `(G, ρ)`, every even
`N`, and every `β ≥ 0` — by the δ-certificate above,
discharged once by the G-0 theorem
(`LayerKernelSOSCert.layerKernelPos`, cited, not reproved).
The hypothesis `DeltaGramGap` is the brick's remaining
priced core; it is NOT proved in this module. -/
theorem layerKernelPos_of_deltaGramGap (hN : Even N) {β : ℝ}
    (hβ : 0 ≤ β) (hgap : DeltaGramGap (ρ := ρ) (N := N) β) :
    LayerKernelPos (N := N) μG ρ β :=
  (gramDeltaCert μG ρ hN β hgap).layerKernelPos

end FiniteAssembly

end ThetLogos
