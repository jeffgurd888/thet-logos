/-
# G-0b — Retrofit: the landed SOS supports as G-0 certificates

Menu item **G-0b** of the Gram/SOS scoping
(`~/workspace/your_files/gram-sos-lkp-scoping-2026-11-05.md`, §4):
register the landed sum-of-squares supports of `LayerKernelPos`
as instances of the G-0 structure `LayerKernelSOSCert`
(`LayerKernelGramCert.lean`), so the certificate vocabulary
covers all three landed supports uniformly:

* the binary seat (N = 2, ZMod 2, sign representation) —
  `seatSOSCert`, from `layerKernel_seat` + `seatIntegralPi`;
* the abelian seat family (every N ≥ 2, same seat data) —
  `famSOSCert`, from `layerKernel_abelian` + `seatIntegralPi`;
* the ternary seat (N = 2, ZMod 3, cube-root character) —
  `ternarySOSCert`, from `layerKernel_ternary_closed` +
  `seatIntegralPi₃`.

**The F2 litmus (§2.2 of the scoping), discharged here.**  The
binary seat registered below is a seat at which
`StratumColumnFactorization` (FACT) is FALSE for every β > 0
(K-FACT-SEAT, `seat_not_stratumColumnFactorization`).  The
certificate construction therefore provably does not route
through FACT: it specializes to a valid certificate exactly
where FACT fails.

**The F3 check at the binary seat.**  `seatSOSCert`'s features
are not constant: `seatSOSCert_features_not_constant` exhibits
the reverse pair `{seatCol0, seatCol0'}` whose configuration
character takes both values `1` and `-1`.  By G-0's
`layerKernel_const_of_features_constant`, a constant-feature
certificate would force a constant kernel; this one does not
have constant features, so the F3 degeneracy shape is absent
(**K-GRAM-DEGEN does not fire on the retrofit**).

**What is NOT registered, and why.**  The family's N = 1 case
(`layerKernelPos_one`) is not a certificate instance: at N = 1
the kernel is the constant `1`, so its only Gram presentation
in this vocabulary has constant features — the F3-degenerate
shape.  It stands in the corpus as a direct proof, outside the
certificate vocabulary, by design.  No landed seat brick is
re-pointed by this module (per the commission: re-pointing is
Jeff's call); the instances are new registrations over the
landed closed forms, and the landed proofs are untouched.

NO CLAIM; dials 0/4.  `LayerKernelPos` in general at β > 0
remains OPEN.
-/

import ThetLogos.LayerKernelGramCert
import ThetLogos.LayerKernelPosSeatProbe
import ThetLogos.LayerKernelPosAbelianFamily
import ThetLogos.LayerKernelPosTernaryGram

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

/-! ## Shared binary-seat column data (seat and family) -/

/-- The binary seat's column coefficients, as a family over the
two types of `ZMod 2`: the trivial type carries
`a(β) = (1 + e^{−2β})/2`, the sign type carries
`b(β) = (1 − e^{−2β})/2` — the split of `exp_colDensC`. -/
noncomputable def gramSeatCoeff (β : ℝ) (t : ZMod 2) : ℝ :=
  if t = 0 then (1 + Real.exp (-2 * β)) / 2
  else (1 - Real.exp (-2 * β)) / 2

/-- The binary seat's column characters: the trivial character
and the seat sign. -/
noncomputable def gramSeatChar (t : ZMod 2)
    (g : Multiplicative (ZMod 2)) : ℂ :=
  if t = 0 then 1 else (seatSign g : ℂ)

/-- Both binary column coefficients are nonnegative for
`β ≥ 0` (this is where the sign of β is spent). -/
theorem gramSeatCoeff_nonneg {β : ℝ} (hβ : 0 ≤ β) :
    ∀ t, 0 ≤ gramSeatCoeff β t := by
  intro t
  unfold gramSeatCoeff
  split_ifs
  · have h := Real.exp_pos (-2 * β)
    linarith
  · have h : Real.exp (-2 * β) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    linarith

/-- Sums over the two types of `ZMod 2`, unfolded. -/
theorem gram_sum_univ_two (f : ZMod 2 → ℂ) :
    ∑ t, f t = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]

/-- **The binary column expansion** (the scoping's §2 column
expansion at the binary seat): the one-element Boltzmann
factor is `a(β) + b(β)·χ` as a character sum over the two
types.  Shared by the seat and family registrations (same
seat representation). -/
theorem gramSeat_expansion (β : ℝ) (g : Multiplicative (ZMod 2)) :
    ((Real.exp (-β * gramDens seatρ g) : ℝ) : ℂ)
      = ∑ t, ((gramSeatCoeff β t : ℝ) : ℂ) * gramSeatChar t g := by
  have hdens : gramDens seatρ g = 1 - seatSign g := by
    unfold gramDens
    rw [charFn_seat]
    simp
  rw [hdens, gram_sum_univ_two]
  have hf0 : ((gramSeatCoeff β 0 : ℝ) : ℂ) * gramSeatChar 0 g
      = (((1 + Real.exp (-2 * β)) / 2 : ℝ) : ℂ) := by
    simp [gramSeatCoeff, gramSeatChar]
  have hf1 : ((gramSeatCoeff β 1 : ℝ) : ℂ) * gramSeatChar 1 g
      = (((1 - Real.exp (-2 * β)) / 2 : ℝ) : ℂ) * (seatSign g : ℂ) := by
    simp [gramSeatCoeff, gramSeatChar]
  rw [hf0, hf1]
  rcases seatSign_eq g with h | h
  · rw [h]
    have e1 : -β * (1 - (1 : ℝ)) = 0 := by ring
    rw [e1, Real.exp_zero, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      show (1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * 1 = (1 : ℝ) by ring]
  · rw [h]
    have e1 : -β * (1 - (-1 : ℝ)) = -2 * β := by ring
    rw [e1, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      show (1 + Real.exp (-2 * β)) / 2
          + (1 - Real.exp (-2 * β)) / 2 * (-1) = Real.exp (-2 * β) by ring]

/-- The assembled weight of a column family under the binary
coefficients: `a^(#columns − |S|) · b^|S|`, in card form (the
family's closed-form exponent shape; the seat's literal `24`
is `card (LayerColumn 2)`). -/
theorem gramWeight_ite {N : ℕ} [NeZero N] (β : ℝ)
    (S : Finset (LayerColumn N)) :
    ∏ P : LayerColumn N, gramSeatCoeff β (if P ∈ S then (1 : ZMod 2) else 0)
      = ((1 + Real.exp (-2 * β)) / 2)
          ^ (Fintype.card (LayerColumn N) - S.card)
        * ((1 - Real.exp (-2 * β)) / 2) ^ S.card := by
  have hterm : ∀ P : LayerColumn N,
      gramSeatCoeff β (if P ∈ S then (1 : ZMod 2) else 0)
        = if P ∈ S then (1 - Real.exp (-2 * β)) / 2
          else (1 + Real.exp (-2 * β)) / 2 := by
    intro P
    by_cases h : P ∈ S
    · have h1 : gramSeatCoeff β (if P ∈ S then (1 : ZMod 2) else 0)
          = (1 - Real.exp (-2 * β)) / 2 := by
        rw [if_pos h]
        unfold gramSeatCoeff
        rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]
      rw [h1, if_pos h]
    · have h1 : gramSeatCoeff β (if P ∈ S then (1 : ZMod 2) else 0)
          = (1 + Real.exp (-2 * β)) / 2 := by
        rw [if_neg h]
        unfold gramSeatCoeff
        rw [if_pos rfl]
      rw [h1, if_neg h]
  rw [Finset.prod_congr rfl (fun P _ => hterm P)]
  calc (∏ P : LayerColumn N,
        if P ∈ S then (1 - Real.exp (-2 * β)) / 2
        else (1 + Real.exp (-2 * β)) / 2)
      = (∏ P ∈ Finset.univ \ S,
          if P ∈ S then (1 - Real.exp (-2 * β)) / 2
          else (1 + Real.exp (-2 * β)) / 2)
        * (∏ P ∈ S,
          if P ∈ S then (1 - Real.exp (-2 * β)) / 2
          else (1 + Real.exp (-2 * β)) / 2) :=
        (Finset.prod_sdiff (Finset.subset_univ S)).symm
    _ = (∏ P ∈ Finset.univ \ S, (1 + Real.exp (-2 * β)) / 2)
        * (∏ P ∈ S, (1 - Real.exp (-2 * β)) / 2) := by
        congr 1
        · exact Finset.prod_congr rfl fun P hP =>
            if_neg (Finset.mem_sdiff.mp hP).2
        · exact Finset.prod_congr rfl fun P hP => if_pos hP
    _ = ((1 + Real.exp (-2 * β)) / 2)
          ^ (Fintype.card (LayerColumn N) - S.card)
        * ((1 - Real.exp (-2 * β)) / 2) ^ S.card := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff,
          Finset.inter_univ, Finset.card_univ]

/-! ## The binary seat instance -/

/-- **G-0b, instance 1 — the binary seat as a G-0
certificate.**  Joint index: column families
`S : Finset (LayerColumn 2)`; the feature is the family's
configuration character on even families, `0` off them (the
stratum filter, as a feature); the type readout is the
family's indicator.  Discharging it through G-0 reproduces
`layerKernelPos_seat` — the registration, not a re-proof. -/
noncomputable def seatSOSCert {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelSOSCert (N := 2) (τ := ZMod 2)
      (ι := Finset (LayerColumn 2)) seatμ seatρ β where
  coeff := gramSeatCoeff β
  coeff_nonneg := gramSeatCoeff_nonneg hβ
  char := gramSeatChar
  expansion := gramSeat_expansion β
  τof := fun S P => if P ∈ S then 1 else 0
  feat := fun S u => if seatEven S then ((configProd S u : ℝ) : ℂ) else 0
  pairScale := ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2))
      : ℝ)⁻¹)
    * ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 2)) : ℝ)⁻¹)
  pairScale_nonneg :=
    mul_nonneg (inv_nonneg.mpr (by positivity))
      (inv_nonneg.mpr (by positivity))
  pairing_eq := by
    intro F
    set c : ℝ := ((Fintype.card (LayerLink 2
      → Multiplicative (ZMod 2)) : ℝ)⁻¹) with hc
    have hP1 : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * layerKernel seatμ seatρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink 2 => seatμ)
          ∂(Measure.pi fun _ : LayerLink 2 => seatμ))
        = c • ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u') := by
      rw [seatIntegralPi]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      exact seatIntegralPi _
    rw [hP1]
    have hsmul : ∀ (r : ℝ) (x : ℂ), r • x = ((r : ℝ) : ℂ) * x := by
      intro r x
      rw [Complex.real_smul]
    calc c • ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u')
        = ((c : ℂ)) * ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u') :=
        hsmul _ _
      _ = ((c : ℂ)) * ∑ u, ((c : ℂ)) * ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u' := by
        congr 1
      _ = ((c : ℂ)) * (((c : ℂ)) * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u') := by
        congr 1
        rw [← Finset.mul_sum]
      _ = ((c * c : ℝ) : ℂ) * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u' := by
        rw [← mul_assoc, ← Complex.ofReal_mul]
  kernel_eq := by
    intro u u'
    have hw : ∀ S : Finset (LayerColumn 2),
        gramColWeight (gramSeatCoeff β)
            (fun S P => if P ∈ S then (1 : ZMod 2) else 0) S
          = ((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card := by
      intro S
      show ∏ P : LayerColumn 2,
          gramSeatCoeff β (if P ∈ S then (1 : ZMod 2) else 0) = _
      rw [gramWeight_ite, layerColumn_card]
    have hstar : ∀ r : ℝ, star ((r : ℂ)) = (r : ℂ) := by
      intro r
      simp
    rw [layerKernel_seat, Complex.ofReal_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : seatEven S
    · rw [if_pos hS]
      show ((((1 + Real.exp (-2 * β)) / 2) ^ (24 - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
            * configProd S u * configProd S u' : ℝ) : ℂ)
        = ((gramColWeight (gramSeatCoeff β)
              (fun S P => if P ∈ S then (1 : ZMod 2) else 0) S : ℝ) : ℂ)
          * (if seatEven S then ((configProd S u : ℝ) : ℂ) else 0)
          * star (if seatEven S then ((configProd S u' : ℝ) : ℂ) else 0)
      rw [if_pos hS, if_pos hS, hw S, hstar]
      push_cast
      ring
    · rw [if_neg hS]
      show (0 : ℂ)
        = ((gramColWeight (gramSeatCoeff β)
              (fun S P => if P ∈ S then (1 : ZMod 2) else 0) S : ℝ) : ℂ)
          * (if seatEven S then ((configProd S u : ℝ) : ℂ) else 0)
          * star (if seatEven S then ((configProd S u' : ℝ) : ℂ) else 0)
      rw [if_neg hS, if_neg hS]
      simp

/-- **The F3 check at the binary seat**: the seat
certificate's features are not constant in the configuration —
the reverse pair's character takes the values `1` (at the
identity configuration) and `-1` (at a one-link deviation). -/
theorem seatSOSCert_features_not_constant {β : ℝ} (hβ : 0 ≤ β) :
    ¬ gramFeaturesConstant (seatSOSCert hβ).feat := by
  have hne : seatCol0 ≠ seatCol0' := fun h => seatCol0_ne h.symm
  have hlink : layerLinkOf seatCol0'.1 seatCol0'.2.1 seatCol0'.2.2
      ≠ layerLinkOf seatCol0.1 seatCol0.2.1 seatCol0.2.2 := by
    intro h
    have hval := congrArg Subtype.val h
    have hsite : seatCol0'.1 = seatCol0.1 :=
      Subtype.ext (congrArg Prod.fst hval)
    exact layerShift_ne seatDir1.1 seatDir1.2 seatSite0 hsite
  set u0 : LayerLink 2 → Multiplicative (ZMod 2) :=
    fun ℓ => if ℓ = layerLinkOf seatCol0.1 seatCol0.2.1 seatCol0.2.2
      then Multiplicative.ofAdd 1 else 1 with hu0
  have h10 : u0 (layerLinkOf seatCol0.1 seatCol0.2.1 seatCol0.2.2)
      = Multiplicative.ofAdd 1 := if_pos rfl
  have h11 : u0 (layerLinkOf seatCol0'.1 seatCol0'.2.1 seatCol0'.2.2)
      = 1 := if_neg hlink
  have hprod : configProd {seatCol0, seatCol0'} u0 = -1 := by
    rw [configProd, Finset.prod_pair hne]
    have hs0 : configSign seatCol0 u0 = -1 := by
      unfold configSign seatSign
      rw [h10]
      simp
    have hs1 : configSign seatCol0' u0 = 1 := by
      unfold configSign seatSign
      rw [h11]
      simp
    rw [hs0, hs1, mul_one]
  have hf1 : (seatSOSCert hβ).feat {seatCol0, seatCol0'} 1 = 1 := by
    show (if seatEven {seatCol0, seatCol0'}
        then ((configProd {seatCol0, seatCol0'} 1 : ℝ) : ℂ)
        else 0) = 1
    rw [if_pos seatEven_pair, configProd_one]
    simp
  have hf2 : (seatSOSCert hβ).feat {seatCol0, seatCol0'} u0 = -1 := by
    show (if seatEven {seatCol0, seatCol0'}
        then ((configProd {seatCol0, seatCol0'} u0 : ℝ) : ℂ)
        else 0) = -1
    rw [if_pos seatEven_pair, hprod]
    simp
  intro hcon
  have hcc := hcon {seatCol0, seatCol0'} 1 u0
  rw [hf1, hf2] at hcc
  norm_num at hcc

/-! ## The abelian family instance -/

/-- **G-0b, instance 2 — the abelian seat family as a G-0
certificate**, at every `N ≥ 2` (the column form's regime).
Same column data as the seat; the joint index is
`Finset (LayerColumn N)` with the family's evenness filter.
The `DecidableEq (LayerLink N)` instance argument is the
family's own standing side condition (the family module's
proofs take it from `Classical`); it is explicit here so the
registration's type is honest about it.  Discharging through
G-0 reproduces `layerKernelPos_abelian_ge` on `2 ≤ N`. -/
noncomputable def famSOSCert {N : ℕ} [NeZero N]
    [DecidableEq (LayerLink N)] (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelSOSCert (N := N) (τ := ZMod 2)
      (ι := Finset (LayerColumn N)) seatμ seatρ β where
  coeff := gramSeatCoeff β
  coeff_nonneg := gramSeatCoeff_nonneg hβ
  char := gramSeatChar
  expansion := gramSeat_expansion β
  τof := fun S P => if P ∈ S then 1 else 0
  feat := fun S u => if famEven S then ((famConfigProd S u : ℝ) : ℂ) else 0
  pairScale := ((Fintype.card (LayerLink N → Multiplicative (ZMod 2))
      : ℝ)⁻¹)
    * ((Fintype.card (LayerLink N → Multiplicative (ZMod 2)) : ℝ)⁻¹)
  pairScale_nonneg :=
    mul_nonneg (inv_nonneg.mpr (by positivity))
      (inv_nonneg.mpr (by positivity))
  pairing_eq := by
    intro F
    set c : ℝ := ((Fintype.card (LayerLink N
      → Multiplicative (ZMod 2)) : ℝ)⁻¹) with hc
    have hP1 : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * layerKernel seatμ seatρ β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink N => seatμ)
          ∂(Measure.pi fun _ : LayerLink N => seatμ))
        = c • ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u') := by
      rw [seatIntegralPi]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      exact seatIntegralPi _
    rw [hP1]
    have hsmul : ∀ (r : ℝ) (x : ℂ), r • x = ((r : ℝ) : ℂ) * x := by
      intro r x
      rw [Complex.real_smul]
    calc c • ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u')
        = ((c : ℂ)) * ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u') :=
        hsmul _ _
      _ = ((c : ℂ)) * ∑ u, ((c : ℂ)) * ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u' := by
        congr 1
      _ = ((c : ℂ)) * (((c : ℂ)) * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u') := by
        congr 1
        rw [← Finset.mul_sum]
      _ = ((c * c : ℝ) : ℂ) * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ seatρ β u u' * F u' := by
        rw [← mul_assoc, ← Complex.ofReal_mul]
  kernel_eq := by
    intro u u'
    have hw : ∀ S : Finset (LayerColumn N),
        gramColWeight (gramSeatCoeff β)
            (fun S P => if P ∈ S then (1 : ZMod 2) else 0) S
          = ((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card := by
      intro S
      show ∏ P : LayerColumn N,
          gramSeatCoeff β (if P ∈ S then (1 : ZMod 2) else 0) = _
      exact gramWeight_ite β S
    have hstar : ∀ r : ℝ, star ((r : ℂ)) = (r : ℂ) := by
      intro r
      simp
    rw [layerKernel_abelian hN, Complex.ofReal_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : famEven S
    · rw [if_pos hS]
      show ((((1 + Real.exp (-2 * β)) / 2)
              ^ (Fintype.card (LayerColumn N) - S.card)
            * ((1 - Real.exp (-2 * β)) / 2) ^ S.card
            * famConfigProd S u * famConfigProd S u' : ℝ) : ℂ)
        = ((gramColWeight (gramSeatCoeff β)
              (fun S P => if P ∈ S then (1 : ZMod 2) else 0) S : ℝ) : ℂ)
          * (if famEven S then ((famConfigProd S u : ℝ) : ℂ) else 0)
          * star (if famEven S then ((famConfigProd S u' : ℝ) : ℂ)
              else 0)
      rw [if_pos hS, if_pos hS, hw S, hstar]
      push_cast
      ring
    · rw [if_neg hS]
      show (0 : ℂ)
        = ((gramColWeight (gramSeatCoeff β)
              (fun S P => if P ∈ S then (1 : ZMod 2) else 0) S : ℝ) : ℂ)
          * (if famEven S then ((famConfigProd S u : ℝ) : ℂ) else 0)
          * star (if famEven S then ((famConfigProd S u' : ℝ) : ℂ)
              else 0)
      rw [if_neg hS, if_neg hS]
      simp

/-! ## The ternary seat instance -/

/-- The ternary seat's column coefficients over the three
types of `ZMod 3`: the trivial type carries `a₃(β)`, both
nontrivial types carry `b₃(β)` — the split of
`exp_colDensC₃` (the density sees only `Re χ`, so `χ` and `χ̄`
share a coefficient). -/
noncomputable def gramTernaryCoeff (β : ℝ) (t : ZMod 3) : ℝ :=
  if t = 0 then seatA₃ β else seatB₃ β

/-- The ternary seat's column characters: the powers of the
cube-root character (`χ⁰ = 1`, `χ¹ = χ`, `χ² = χ̄`). -/
noncomputable def gramTernaryChar (t : ZMod 3)
    (g : Multiplicative (ZMod 3)) : ℂ :=
  seatChar₃ g ^ t.val

/-- Both ternary column coefficients are nonnegative for
`β ≥ 0` (`seatA₃` at every β, `seatB₃` iff `β ≥ 0`). -/
theorem gramTernaryCoeff_nonneg {β : ℝ} (hβ : 0 ≤ β) :
    ∀ t, 0 ≤ gramTernaryCoeff β t := by
  intro t
  unfold gramTernaryCoeff
  split_ifs
  · exact seatA₃_nonneg β
  · exact seatB₃_nonneg hβ

/-- Sums over the three types of `ZMod 3`, unfolded. -/
theorem gram_sum_univ_three (f : ZMod 3 → ℂ) :
    ∑ t, f t = f 0 + f 1 + f 2 := by
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv, Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
    Finset.sum_pair (by decide : (1 : ZMod 3) ≠ 2), add_assoc]

/-- **The ternary column expansion**: the one-element
Boltzmann factor is `a₃(β) + b₃(β)·χ + b₃(β)·χ²` as a
character sum over the three types. -/
theorem gramTernary_expansion (β : ℝ)
    (g : Multiplicative (ZMod 3)) :
    ((Real.exp (-β * gramDens seatρ₃ g) : ℝ) : ℂ)
      = ∑ t, ((gramTernaryCoeff β t : ℝ) : ℂ) * gramTernaryChar t g := by
  have hdens : gramDens seatρ₃ g = 1 - (seatChar₃ g).re := by
    unfold gramDens
    rw [charFn_seat₃]
    simp
  rw [hdens, gram_sum_univ_three]
  have hf0 : ((gramTernaryCoeff β 0 : ℝ) : ℂ) * gramTernaryChar 0 g
      = ((seatA₃ β : ℝ) : ℂ) := by
    simp [gramTernaryCoeff, gramTernaryChar]
  have hf1 : ((gramTernaryCoeff β 1 : ℝ) : ℂ) * gramTernaryChar 1 g
      = ((seatB₃ β : ℝ) : ℂ) * seatChar₃ g := by
    show (((if (1 : ZMod 3) = 0 then seatA₃ β else seatB₃ β : ℝ)) : ℂ)
        * (seatChar₃ g ^ (1 : ZMod 3).val) = _
    rw [if_neg (by decide : (1 : ZMod 3) ≠ 0),
      show (1 : ZMod 3).val = 1 from rfl, pow_one]
  have hf2 : ((gramTernaryCoeff β 2 : ℝ) : ℂ) * gramTernaryChar 2 g
      = ((seatB₃ β : ℝ) : ℂ) * (seatChar₃ g) ^ 2 := by
    show (((if (2 : ZMod 3) = 0 then seatA₃ β else seatB₃ β : ℝ)) : ℂ)
        * (seatChar₃ g ^ (2 : ZMod 3).val) = _
    rw [if_neg (by decide : (2 : ZMod 3) ≠ 0),
      show (2 : ZMod 3).val = 2 from rfl]
  rw [hf0, hf1, hf2]
  by_cases h : Multiplicative.toAdd g = 0
  · have hre : (seatChar₃ g).re = 1 := by rw [seatChar₃_re, if_pos h]
    have hχ : seatChar₃ g = 1 := by simp [seatChar₃, h, chiC3_zero]
    have e1 : -β * (1 - (1 : ℝ)) = 0 := by ring
    rw [hre, hχ, e1, Real.exp_zero, one_pow, mul_one,
      ← Complex.ofReal_add, ← Complex.ofReal_add,
      show seatA₃ β + seatB₃ β + seatB₃ β = (1 : ℝ) by
        have h2 := seatA₃_add_two_mul_seatB₃ β
        linarith]
  · have hre : (seatChar₃ g).re = -1 / 2 := by rw [seatChar₃_re, if_neg h]
    have hsum : seatChar₃ g + (seatChar₃ g) ^ 2 = -1 := by
      rcases seatChar₃_cases g with h1 | h1 | h1
      · rw [h1] at hre
        norm_num at hre
      · rw [h1]
        linear_combination zetaC3_sq_add
      · have h4 : (zetaC3 ^ 2) ^ 2 = zetaC3 := by
          rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add,
            zetaC3_cube, one_mul, pow_one]
        rw [h1, h4]
        linear_combination zetaC3_sq_add
    have e1 : -β * (1 - (-1 / 2 : ℝ)) = -(3 / 2) * β := by ring
    rw [hre, e1,
      show ((seatA₃ β : ℝ) : ℂ) + ((seatB₃ β : ℝ) : ℂ) * seatChar₃ g
          + ((seatB₃ β : ℝ) : ℂ) * (seatChar₃ g) ^ 2
        = ((seatA₃ β - seatB₃ β : ℝ) : ℂ) by
        rw [Complex.ofReal_sub, add_assoc, ← mul_add, hsum]
        push_cast
        ring,
      seatA₃_sub_seatB₃]

/-- The assembled weight of a ternary pattern is the landed
pattern weight: `a₃^(24−|supp ε|) · b₃^|supp ε|`. -/
theorem gramWeight_pattern (β : ℝ) (ε : LayerColumn 2 → ZMod 3) :
    ∏ P : LayerColumn 2, gramTernaryCoeff β (ε P)
      = patternWeight₃ ε β := by
  have hterm : ∀ P : LayerColumn 2, gramTernaryCoeff β (ε P)
      = if ε P ≠ 0 then seatB₃ β else seatA₃ β := by
    intro P
    unfold gramTernaryCoeff
    by_cases h : ε P = 0
    · rw [if_pos h, if_neg (fun hh => hh h)]
    · rw [if_neg h, if_pos h]
  have hsupp : patternSupp₃ ε
      = Finset.univ.filter (fun P => ε P ≠ 0) := rfl
  unfold patternWeight₃
  rw [hsupp, Finset.prod_congr rfl (fun P _ => hterm P)]
  calc (∏ P : LayerColumn 2, if ε P ≠ 0 then seatB₃ β else seatA₃ β)
      = (∏ P ∈ Finset.univ \ (Finset.univ.filter (fun P => ε P ≠ 0)),
          if ε P ≠ 0 then seatB₃ β else seatA₃ β)
        * (∏ P ∈ Finset.univ.filter (fun P => ε P ≠ 0),
          if ε P ≠ 0 then seatB₃ β else seatA₃ β) :=
        (Finset.prod_sdiff (Finset.subset_univ _)).symm
    _ = (∏ P ∈ Finset.univ \ (Finset.univ.filter (fun P => ε P ≠ 0)),
          seatA₃ β)
        * (∏ P ∈ Finset.univ.filter (fun P => ε P ≠ 0), seatB₃ β) := by
        congr 1
        · exact Finset.prod_congr rfl fun P hP =>
            if_neg (fun hh => (Finset.mem_sdiff.mp hP).2
              (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hh⟩))
        · exact Finset.prod_congr rfl fun P hP =>
            if_pos (Finset.mem_filter.mp hP).2
    _ = (seatA₃ β) ^ (24
          - (Finset.univ.filter (fun P => ε P ≠ 0)).card)
        * (seatB₃ β) ^ (Finset.univ.filter (fun P => ε P ≠ 0)).card := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff,
          Finset.inter_univ, Finset.card_univ, layerColumn_card]

/-- **G-0b, instance 3 — the ternary seat as a G-0
certificate.**  Joint index: patterns
`ε : LayerColumn 2 → ZMod 3` (the type readout is the pattern
itself); the feature is the conjugated configuration
character `star (A_ε(u))` on surviving patterns, `0` off them
(the conjugation places TM-2's closed form
`A_ε(u') · star (A_ε(u))` in the pin's orientation
`Φ(u) · star (Φ(u'))`).  Discharging through G-0 reproduces
`layerKernelPos_ternary_seat`. -/
noncomputable def ternarySOSCert {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelSOSCert (N := 2) (τ := ZMod 3)
      (ι := LayerColumn 2 → ZMod 3) seatμ₃ seatρ₃ β where
  coeff := gramTernaryCoeff β
  coeff_nonneg := gramTernaryCoeff_nonneg hβ
  char := gramTernaryChar
  expansion := gramTernary_expansion β
  τof := fun ε P => ε P
  feat := fun ε u => if patternSurvives₃ ε
    then star (patternConfig₃ ε u) else 0
  pairScale := ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3))
      : ℝ)⁻¹)
    * ((Fintype.card (LayerLink 2 → Multiplicative (ZMod 3)) : ℝ)⁻¹)
  pairScale_nonneg :=
    mul_nonneg (inv_nonneg.mpr (by positivity))
      (inv_nonneg.mpr (by positivity))
  pairing_eq := by
    intro F
    rw [ternary_pairing_sum]
    set c : ℝ := ((Fintype.card (LayerLink 2
      → Multiplicative (ZMod 3)) : ℝ)⁻¹) with hc
    have hsmul : ∀ (r : ℝ) (x : ℂ), r • x = ((r : ℝ) : ℂ) * x := by
      intro r x
      rw [Complex.real_smul]
    calc c • ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ₃ seatρ₃ β u u' * F u')
        = ((c : ℂ)) * ∑ u, (c • ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ₃ seatρ₃ β u u' * F u') :=
        hsmul _ _
      _ = ((c : ℂ)) * ∑ u, ((c : ℂ)) * ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ₃ seatρ₃ β u u' * F u' := by
        congr 1
      _ = ((c : ℂ)) * (((c : ℂ)) * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ₃ seatρ₃ β u u' * F u') := by
        congr 1
        rw [← Finset.mul_sum]
      _ = ((c * c : ℝ) : ℂ) * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
            * layerKernel seatμ₃ seatρ₃ β u u' * F u' := by
        rw [← mul_assoc, ← Complex.ofReal_mul]
  kernel_eq := by
    intro u u'
    have hw : ∀ ε : LayerColumn 2 → ZMod 3,
        gramColWeight (gramTernaryCoeff β) (fun ε P => ε P) ε
          = patternWeight₃ ε β := by
      intro ε
      show ∏ P : LayerColumn 2, gramTernaryCoeff β (ε P) = _
      exact gramWeight_pattern β ε
    rw [layerKernel_ternary_closed]
    unfold layerKernel_ternary
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ε _ => ?_
    by_cases hε : patternSurvives₃ ε
    · rw [if_pos hε]
      show ((patternWeight₃ ε β : ℂ))
          * (patternConfig₃ ε u' * star (patternConfig₃ ε u))
        = ((gramColWeight (gramTernaryCoeff β) (fun ε P => ε P) ε
            : ℝ) : ℂ)
          * (if patternSurvives₃ ε then star (patternConfig₃ ε u)
              else 0)
          * star (if patternSurvives₃ ε
              then star (patternConfig₃ ε u') else 0)
      rw [if_pos hε, if_pos hε, hw ε, star_star]
      ring
    · rw [if_neg hε]
      show (0 : ℂ)
        = ((gramColWeight (gramTernaryCoeff β) (fun ε P => ε P) ε
            : ℝ) : ℂ)
          * (if patternSurvives₃ ε then star (patternConfig₃ ε u)
              else 0)
          * star (if patternSurvives₃ ε
              then star (patternConfig₃ ε u') else 0)
      rw [if_neg hε, if_neg hε]
      simp

end ThetLogos
