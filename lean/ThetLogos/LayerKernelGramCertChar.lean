/-
# WP2 character route, Module B, brick B3 — the character
# Gram certificate and `LayerKernelPos` at finite `(G, ρ)`

The assembly of B1 and B2 into a `LayerKernelSOSCert`:
the column family is the finite irreducible family
`τ = charFamily G` (B2a1), the column coefficients are
B1d's `colCoeff`s (nonnegative for `β ≥ 0`), the column
expansion is B1d's `column_expansion` reindexed over the
subtype, and the kernel identity assembles
`layerKernel_eq_card_inv_sum` (the Finite module's
counting form) column by column: the expansion turns each
column's Boltzmann factor into a character sum, the
product over columns becomes a sum over column-type
assignments `t`, and B2a2's `char_separation` splits each
`t`-summand over channel tuples into separated features
`charSepFeat`.  The joint index is therefore
`j = (t, c) : Σ t, ∀ s, Fin (siteChanCount t s)`, with
assembled weight `gramColWeight coeff τof j = ∏_P colCoeff
(τof j P) ≥ 0`.  The pairing evaluation is the Finite
regime's, copied from the δ-certificate (it is
data-independent).  The G-0 discharge
(`LayerKernelSOSCert.layerKernelPos`, proved once in the
certificate module) then gives `LayerKernelPos` at every
finite `(G, ρ)`, every even `N`, every `β ≥ 0`.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This closes
the character route to `LayerKernelPos` at finite
`(G, ρ)` only: `DeltaGramGap` itself is NOT proved here
(it is the δ-route's named gap, a different statement);
no continuum limit is claimed; Dial 3 = 0.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity
object.
-/

import ThetLogos.LayerKernelCharSeparation
import ThetLogos.LayerKernelGramCertFinite

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

section CharAssembly

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- **The character Gram certificate.**  The
`LayerKernelSOSCert` of the character route at even `N`
and `β ≥ 0`: B1d's coefficients and expansion over the
finite irreducible family, B2a2's separated features over
the joint index of column-type assignments and channel
tuples. -/
noncomputable def gramCharCert (hN : Even N) (β : ℝ)
    (hβ : 0 ≤ β) :
    LayerKernelSOSCert (N := N) (τ := charFamily G)
      (ι := Σ t : LayerColumn N → charFamily G,
        ∀ s : LayerSite N, Fin (siteChanCount t s)) μG ρ β where
  coeff := fun χ => colCoeff ρ β χ.1
  coeff_nonneg := fun χ => colCoeff_nonneg ρ hβ χ.1
  char := fun χ g => χ.1 g
  expansion := fun g =>
    (column_expansion ρ hβ g).trans
      (Finset.sum_coe_sort _ _).symm
  τof := fun j P => j.1 P
  feat := fun j => charSepFeat j.1 j.2
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
    have hexp : ∀ (α : LayerSite N → G) (P : LayerColumn N),
        ((Real.exp (-β * gramDens ρ (colWordOf u u' P α)) : ℝ) : ℂ)
          = ∑ χ : charFamily G, ((colCoeff ρ β χ.1 : ℝ) : ℂ)
              * χ.1 (colWordOf u u' P α) :=
      fun α P =>
        (column_expansion ρ hβ _).trans (Finset.sum_coe_sort _ _).symm
    calc layerKernel μG ρ β u u'
        = ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
            * ∑ α : LayerSite N → G, ∏ P : LayerColumn N,
              ∑ χ : charFamily G, ((colCoeff ρ β χ.1 : ℝ) : ℂ)
                * χ.1 (colWordOf u u' P α) := by
          rw [layerKernel_eq_card_inv_sum μG ρ hN β u u']
          refine congrArg _ (Finset.sum_congr rfl fun α _ => ?_)
          exact Finset.prod_congr rfl fun P _ => hexp α P
      _ = ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
            * ∑ α : LayerSite N → G,
              ∑ t : LayerColumn N → charFamily G,
                ∏ P : LayerColumn N, ((colCoeff ρ β (t P).1 : ℝ) : ℂ)
                  * (t P).1 (colWordOf u u' P α) := by
          refine congrArg _ (Finset.sum_congr rfl fun α _ => ?_)
          exact Fintype.prod_sum _
      _ = ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
            * ∑ t : LayerColumn N → charFamily G,
              ∑ α : LayerSite N → G,
                ∏ P : LayerColumn N, ((colCoeff ρ β (t P).1 : ℝ) : ℂ)
                  * (t P).1 (colWordOf u u' P α) := by
          exact congrArg _ Finset.sum_comm
      _ = ∑ t : LayerColumn N → charFamily G,
            ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
            * ∑ α : LayerSite N → G,
              ∏ P : LayerColumn N, ((colCoeff ρ β (t P).1 : ℝ) : ℂ)
                * (t P).1 (colWordOf u u' P α) := by
          rw [Finset.mul_sum]
      _ = ∑ t : LayerColumn N → charFamily G,
            (∏ P : LayerColumn N, ((colCoeff ρ β (t P).1 : ℝ) : ℂ))
            * (((Fintype.card (LayerSite N → G) : ℂ))⁻¹
              * ∑ α : LayerSite N → G,
                ∏ P : LayerColumn N, (t P).1 (colWordOf u u' P α)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          have hα : ∀ α : LayerSite N → G,
              ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
                  * ∏ P : LayerColumn N,
                    ((colCoeff ρ β (t P).1 : ℝ) : ℂ)
                      * (t P).1 (colWordOf u u' P α)
                = (∏ P : LayerColumn N,
                    ((colCoeff ρ β (t P).1 : ℝ) : ℂ))
                  * (((Fintype.card (LayerSite N → G) : ℂ))⁻¹
                    * ∏ P : LayerColumn N,
                      (t P).1 (colWordOf u u' P α)) := by
            intro α
            rw [Finset.prod_mul_distrib]
            ring
          rw [Finset.mul_sum,
            Finset.sum_congr rfl (fun α _ => hα α),
            ← Finset.mul_sum, ← Finset.mul_sum]
      _ = ∑ t : LayerColumn N → charFamily G,
            (∏ P : LayerColumn N, ((colCoeff ρ β (t P).1 : ℝ) : ℂ))
            * ∑ c : ∀ s : LayerSite N, Fin (siteChanCount t s),
              charSepFeat t c u * star (charSepFeat t c u') := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact congrArg _ (char_separation t u u')
      _ = ∑ t : LayerColumn N → charFamily G,
            ∑ c : ∀ s : LayerSite N, Fin (siteChanCount t s),
              (∏ P : LayerColumn N, ((colCoeff ρ β (t P).1 : ℝ) : ℂ))
              * (charSepFeat t c u * star (charSepFeat t c u')) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j : (Σ t : LayerColumn N → charFamily G,
              ∀ s : LayerSite N, Fin (siteChanCount t s)),
            ((gramColWeight (fun χ => colCoeff ρ β χ.1)
              (fun j P => j.1 P) j : ℝ) : ℂ)
              * charSepFeat j.1 j.2 u
              * star (charSepFeat j.1 j.2 u') := by
          refine (Finset.sum_congr rfl fun t _ =>
            Finset.sum_congr rfl fun c _ => ?_).trans
            (Fintype.sum_sigma _).symm
          simp only [gramColWeight, Complex.ofReal_prod]
          ring

/-- **Character-route headline.**  `LayerKernelPos` at
every finite `(G, ρ)`, every even `N`, every `β ≥ 0` — by
the character Gram certificate, discharged once by the
G-0 theorem (`LayerKernelSOSCert.layerKernelPos`, cited,
not reproved). -/
theorem layerKernelPos_char (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelPos (N := N) μG ρ β :=
  (gramCharCert μG ρ hN β hβ).layerKernelPos

end CharAssembly

end ThetLogos
